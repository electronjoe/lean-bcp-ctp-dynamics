#!/usr/bin/env python3
"""
Generate `LLM.md` by concatenating selected project files in a markdown-friendly format.

Each file is wrapped in a fenced code block whose info string is the POSIX-style path.
The script targets the repository root (the directory containing this script).
"""

from __future__ import annotations

import argparse
from pathlib import Path
from typing import Iterable, List


def gather_files(root: Path) -> List[Path]:
    """Collect the repository files to include in the summary."""
    files: List[Path] = []

    # Files at the project root.
    root_files = [
        Path("README.md"),
        Path("LeanBcpDynamicVsCtp.lean"),
        Path("lakefile.toml"),
        Path("lake-manifest.json"),
        Path("lean-toolchain"),
        Path("REFS.md"),
        Path("STRATEGIES.md"),
        Path("DEBUGGING.md"),
        Path("build.log"),
    ]
    for path in root_files:
        candidate = root / path
        if candidate.is_file():
            files.append(candidate)

    # All files under LeanBcpDynamicVsCtp directory (recursively).
    project_dir = root / "LeanBcpDynamicVsCtp"
    if project_dir.is_dir():
        for file_path in sorted(project_dir.rglob("*")):
            if file_path.is_file():
                files.append(file_path)

    return files


def format_file(path: Path, root: Path) -> str:
    """Return the file contents wrapped in a markdown code fence."""
    rel_path = path.relative_to(root).as_posix()
    text = path.read_text(encoding="utf-8")
    if not text.endswith("\n"):
        text += "\n"
    return f"```{rel_path}\n{text}```\n"


def write_output(files: Iterable[Path], root: Path, output: Path) -> None:
    """Write all collected files to the output markdown file."""
    with output.open("w", encoding="utf-8") as f:
        for path in files:
            f.write(format_file(path, root))
            f.write("\n")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Collect repository files into LLM.md for external LLM consumption."
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("LLM.md"),
        help="Path of the markdown file to generate (default: LLM.md).",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    root = Path(__file__).resolve().parent
    files = gather_files(root)
    write_output(files, root, args.output.resolve())


if __name__ == "__main__":
    main()
