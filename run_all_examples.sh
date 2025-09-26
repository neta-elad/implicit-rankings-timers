#!/bin/bash

# Script to run make check and all examples, capturing output to a text file
# Usage: ./run_all_examples.sh [output_file]

# Set output file (default: run_all_examples_output.txt)
OUTPUT_FILE=${1:-run_all_examples_output.txt}

# Get the directory where this script is located
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

# Arrays to track results
declare -a EXAMPLE_NAMES
declare -a EXAMPLE_RESULTS

# Create temporary file for detailed output
TEMP_FILE=$(mktemp)

# Run make check
echo "Starting run_all_examples.sh at $(date)" > "$TEMP_FILE"
echo "Output will be saved to: $OUTPUT_FILE" >> "$TEMP_FILE"
echo "===========================================" >> "$TEMP_FILE"
echo "" >> "$TEMP_FILE"
echo "Running: make check" >> "$TEMP_FILE"
echo "-------------------------------------------" >> "$TEMP_FILE"

MAKE_CHECK_RESULT="PASS"
if make check 2>&1 | tee -a "$TEMP_FILE"; then
    echo "make check completed successfully" >> "$TEMP_FILE"
else
    echo "make check failed with exit code $?" >> "$TEMP_FILE"
    MAKE_CHECK_RESULT="FAIL"
fi

# Get all Python files in examples directory
EXAMPLES_DIR="examples"
if [ ! -d "$EXAMPLES_DIR" ]; then
    echo "Error: $EXAMPLES_DIR directory not found" >> "$TEMP_FILE"
    exit 1
fi

# Find all .py files in examples directory (excluding __pycache__)
PYTHON_FILES=$(find "$EXAMPLES_DIR" -name "*.py" -not -path "*/__pycache__/*" | sort)

if [ -z "$PYTHON_FILES" ]; then
    echo "No Python files found in $EXAMPLES_DIR" >> "$TEMP_FILE"
    exit 1
fi

echo "" >> "$TEMP_FILE"
echo "Found Python files to run:" >> "$TEMP_FILE"
echo "$PYTHON_FILES" >> "$TEMP_FILE"
echo "===========================================" >> "$TEMP_FILE"

# Run each example
for python_file in $PYTHON_FILES; do
    echo "" >> "$TEMP_FILE"
    echo "Running: make $python_file" >> "$TEMP_FILE"
    echo "-------------------------------------------" >> "$TEMP_FILE"
    
    # Extract just the filename without path for summary
    example_name=$(basename "$python_file")
    EXAMPLE_NAMES+=("$example_name")
    
    # Capture output to analyze verification results
    example_output=$(make "$python_file" 2>&1)
    echo "$example_output" >> "$TEMP_FILE"
    
    # Analyze the output to determine if verification passed or failed
    if echo "$example_output" | grep -q "All passed!"; then
        EXAMPLE_RESULTS+=("PASS")
    elif echo "$example_output" | grep -q "fail:"; then
        # Extract the failure reason
        fail_reason=$(echo "$example_output" | grep "fail:" | tail -1 | sed 's/.*fail: //')
        EXAMPLE_RESULTS+=("FAIL: $fail_reason")
    elif echo "$example_output" | grep -q "Traceback\|Error\|Exception"; then
        EXAMPLE_RESULTS+=("ERROR")
    else
        # If make succeeded but no clear pass/fail indication, check exit code
        if [ $? -eq 0 ]; then
            EXAMPLE_RESULTS+=("PASS")
        else
            EXAMPLE_RESULTS+=("FAIL")
        fi
    fi
done

# Create summary at the top
{
    echo "==========================================="
    echo "SUMMARY"
    echo "==========================================="
    echo "make check: $MAKE_CHECK_RESULT"
    echo ""
    
    # Count passes and fails
    pass_count=0
    fail_count=0
    
    for i in "${!EXAMPLE_NAMES[@]}"; do
        example_name="${EXAMPLE_NAMES[$i]}"
        result="${EXAMPLE_RESULTS[$i]}"
        echo "$example_name: $result"
        
        if [ "$result" = "PASS" ]; then
            ((pass_count++))
        else
            ((fail_count++))
        fi
    done
    
    echo ""
    echo "Total: $((pass_count + fail_count)) examples"
    echo "Passed: $pass_count"
    echo "Failed: $fail_count"
    echo ""
    echo "==========================================="
    echo "DETAILED OUTPUT"
    echo "==========================================="
    echo ""
    
    # Add the detailed output
    cat "$TEMP_FILE"
    
    echo ""
    echo "==========================================="
    echo "All examples completed at $(date)"
    echo "Output saved to: $OUTPUT_FILE"
} > "$OUTPUT_FILE"

# Clean up temporary file
rm "$TEMP_FILE"

echo "Script completed. Summary saved to: $OUTPUT_FILE"
