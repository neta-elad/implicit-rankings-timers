import re
import sys
from os import getenv
from pathlib import Path

def line_size(line: str) -> int:
    regex = r"(<->|->|[a-zA-Z0-9_\$]+|~\=|(?<!~)\=|~(?=\=)|&|\|)"
    results = re.findall(regex, line.split("#")[0])
    return len(results)


def main(filename: Path) -> None:
    in_proof = False
    size = 0

    for raw_line in filename.read_text().splitlines():
        line = raw_line.strip()
        if not line:
            continue  # empty line
        if line.startswith("#"):
            continue  # comment
        if line.startswith("proof"):
            in_proof = True
            continue
        if not in_proof:
            continue
        size += line_size(line)

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