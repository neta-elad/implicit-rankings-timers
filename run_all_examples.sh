#!/bin/bash

# Script to run make check and all examples, capturing output to a text file
# Usage: ./run_all_examples.sh [output_file]

# Set output file (default: run_all_examples_output.txt)
OUTPUT_FILE=${1:-run_all_examples_output.txt}

# Get the directory where this script is located
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

echo "Starting run_all_examples.sh at $(date)" | tee "$OUTPUT_FILE"
echo "Output will be saved to: $OUTPUT_FILE" | tee -a "$OUTPUT_FILE"
echo "===========================================" | tee -a "$OUTPUT_FILE"

# Run make check
echo "" | tee -a "$OUTPUT_FILE"
echo "Running: make check" | tee -a "$OUTPUT_FILE"
echo "-------------------------------------------" | tee -a "$OUTPUT_FILE"
if make check 2>&1 | tee -a "$OUTPUT_FILE"; then
    echo "make check completed successfully" | tee -a "$OUTPUT_FILE"
else
    echo "make check failed with exit code $?" | tee -a "$OUTPUT_FILE"
fi

# Get all Python files in examples directory
EXAMPLES_DIR="examples"
if [ ! -d "$EXAMPLES_DIR" ]; then
    echo "Error: $EXAMPLES_DIR directory not found" | tee -a "$OUTPUT_FILE"
    exit 1
fi

# Find all .py files in examples directory (excluding __pycache__)
PYTHON_FILES=$(find "$EXAMPLES_DIR" -name "*.py" -not -path "*/__pycache__/*" | sort)

if [ -z "$PYTHON_FILES" ]; then
    echo "No Python files found in $EXAMPLES_DIR" | tee -a "$OUTPUT_FILE"
    exit 1
fi

echo "" | tee -a "$OUTPUT_FILE"
echo "Found Python files to run:" | tee -a "$OUTPUT_FILE"
echo "$PYTHON_FILES" | tee -a "$OUTPUT_FILE"
echo "===========================================" | tee -a "$OUTPUT_FILE"

# Run each example
for python_file in $PYTHON_FILES; do
    echo "" | tee -a "$OUTPUT_FILE"
    echo "Running: make $python_file" | tee -a "$OUTPUT_FILE"
    echo "-------------------------------------------" | tee -a "$OUTPUT_FILE"
    
    if make "$python_file" 2>&1 | tee -a "$OUTPUT_FILE"; then
        echo "make $python_file completed successfully" | tee -a "$OUTPUT_FILE"
    else
        echo "make $python_file failed with exit code $?" | tee -a "$OUTPUT_FILE"
    fi
done

echo "" | tee -a "$OUTPUT_FILE"
echo "===========================================" | tee -a "$OUTPUT_FILE"
echo "All examples completed at $(date)" | tee -a "$OUTPUT_FILE"
echo "Output saved to: $OUTPUT_FILE" | tee -a "$OUTPUT_FILE"
