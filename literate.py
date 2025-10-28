import re
from os import getenv
from pathlib import Path

OUT_DIR = Path("docs")


def extract_literate_blocks(source_path: Path, target_path: Path) -> None:
    """Extract <> blocks from a Python file and write them as Markdown."""
    src = source_path.read_text(encoding="utf-8").splitlines()
    out_lines: list[str] = []

    in_block = False
    code_buffer: list[str] = []
    force_markdown = False

    def flush_code() -> None:
        """Write accumulated code as a fenced code block."""
        nonlocal code_buffer
        if code_buffer:
            out_lines.append("```python")
            out_lines.extend(code_buffer)
            out_lines.append("```")
            out_lines.append("")  # blank line
            code_buffer = []

    for line in src:
        if not in_block:
            if (match := re.match(r"^\s*#\s*<>(.*)$", line)) is not None:
                flush_code()
                line = match[1]
                in_block = True
                if line.startswith("!"):
                    line = line[1:]
                    force_markdown = True
                else:
                    force_markdown = False
                    continue
            else:
                continue  # skip outside blocks

        if (match := re.match(r"^(.*?)#\s*</>$", line)) is not None:
            line = match[1]
            in_block = False

        # Inside a block:
        stripped_line = line.lstrip()
        if force_markdown or stripped_line.startswith("# |"):
            # Markdown line: flush any code buffer first
            flush_code()
            if not force_markdown:
                stripped_line = stripped_line[3:].lstrip()  # remove "# |"
            out_lines.append(stripped_line)
        else:
            code_buffer.append(line)

    # If file ended inside a block
    flush_code()

    target_path.parent.mkdir(parents=True, exist_ok=True)
    target_path.write_text("\n".join(out_lines).rstrip() + "\n", encoding="utf-8")
    print(f"Wrote {target_path}")


if __name__ == "__main__":
    file = getenv("FILE")
    if file is None:
        print(f"Missing env var `FILE`")
        exit(-1)
    file_path = Path(file)
    if not file_path.exists() or not file_path.is_file():
        print(f"{file} is missing or not a file")
        exit(-1)
    extract_literate_blocks(file_path, OUT_DIR / file_path.with_suffix(".md"))
