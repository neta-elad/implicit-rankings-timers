import re
import sys
from os import getenv
from pathlib import Path


def line_size(line: str) -> int:
    regex = r"(<->|->|[a-zA-Z0-9_\$]+|~\=|(?<!~)\=|~(?=\=)|&|\|)"
    results = re.findall(regex, line.split("#")[0])
    return len(results)


def main(filename: Path) -> None:
    size = 0
    lines = filename.read_text().splitlines()

    i = 0
    while i < len(lines):
        line = lines[i].strip()

        # Check if this line starts an invariant or conjecture
        if line.startswith("invariant") or line.startswith("conjecture"):
            # Collect the complete invariant/conjecture (may span multiple lines)
            invariant_text = line

            # Look for continuation lines
            j = i + 1
            while j < len(lines):
                next_line = lines[j].strip()

                # Skip empty lines
                if not next_line:
                    j += 1
                    continue

                # Check if this looks like a continuation line
                # (starts with logical operators, parentheses, or contains logical symbols)
                # But NOT if it starts with 'invariant' or 'conjecture' (new invariant)
                if (
                    not next_line.startswith("invariant")
                    and not next_line.startswith("conjecture")
                    and (
                        next_line.startswith("(")
                        or next_line.startswith("&")
                        or next_line.startswith("|")
                        or next_line.startswith("->")
                        or next_line.startswith("<->")
                        or next_line.startswith("~")
                        or next_line.startswith(")")
                        or next_line.startswith("forall")
                        or next_line.startswith("exists")
                        or next_line.startswith("globally")
                        or next_line.startswith("eventually")
                        or "->" in next_line
                        or "<->" in next_line
                        or "&" in next_line
                        or "|" in next_line
                        or "~=" in next_line
                        or "=" in next_line
                    )
                ):
                    invariant_text += " " + next_line
                    j += 1
                else:
                    # This doesn't look like a continuation
                    break

            # Calculate size for the complete invariant
            size += line_size(invariant_text)
            i = j  # Skip to the line after the invariant
        else:
            i += 1

    print(f"[{filename}] Proof size: {size}")


if __name__ == "__main__":
    ivy_file = getenv("IVY_FILE")
    if ivy_file is None:
        print(f"Missing env var `IVY_FILE`")
        exit(-1)
    ivy_path = Path(ivy_file)
    if not ivy_path.exists() or not ivy_path.is_file():
        print(f"{ivy_file} is missing or not a file")
        exit(-1)
    main(ivy_path)
