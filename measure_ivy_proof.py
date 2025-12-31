import re
from os import getenv
from pathlib import Path

counted_expr = re.compile(r"([a-zA-Z0-9_$]+|<->|->|~=|(?<!~)=|~(?==)|&|\|)")


def clean_line(line: str) -> tuple[str, bool]:
    parts = line.split("#")
    return parts[0].strip(), len(parts) > 1


def line_size(line: str) -> int:
    results = counted_expr.findall(line)
    return len(results)


def starts_inv(line: str) -> bool:
    return line.startswith("invariant") or line.startswith("conjecture")


def continuation(line: str) -> bool:
    return counted_expr.match(line) is not None


def measure_ivy_proof(filename: Path) -> int:
    size = 0
    in_invariant = False

    for raw_line in filename.read_text().splitlines():
        line, has_comment = clean_line(raw_line)
        if starts_inv(line):
            in_invariant = True
            size += line_size(line)
        elif in_invariant and (has_comment or continuation(line)):
            size += line_size(line)
        else:
            in_invariant = False

    return size


if __name__ == "__main__":
    ivy_file = getenv("IVY_FILE")
    if ivy_file is None:
        print(f"Missing env var `IVY_FILE`")
        exit(-1)
    ivy_path = Path(ivy_file)
    if not ivy_path.exists() or not ivy_path.is_file():
        print(f"{ivy_file} is missing or not a file")
        exit(-1)
    size = measure_ivy_proof(ivy_path)
    print(f"[{ivy_path}] Proof size: {size}")
