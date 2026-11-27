"""Move standalone comments into Markdown while preserving every line that contains Lean code."""
from pathlib import Path
import argparse
import hashlib
import shutil

from leanreducer.source import lexical_lines


def code_lines(text):
    return [code for code, _ in lexical_lines(text) if code.strip()]


def compact(source, output):
    if output.exists():
        raise ValueError("output directory already exists")
    shutil.copytree(source, output, ignore=shutil.ignore_patterns(".git", ".lake"))
    notes = ["# Notes from the conditional Lean source", "",
             "Sections give the original source locations. Executable lines and inline comments stay in the Lean files.", ""]
    for file in sorted((output / "src").rglob("*.lean")):
        path = file.relative_to(output).as_posix()
        if path == "src/Statements.lean":
            continue
        original = file.read_text()
        kept = ["-- Modified by LeanReducer. Module documentation is in SOURCE-NOTES.md."]
        notes += ["## " + path, ""]
        pending = []
        def flush():
            if pending:
                notes.extend([f"Original lines {pending[0][0]}–{pending[-1][0]}", "", "```lean",
                              *(v for _, v in pending), "```", ""])
                pending.clear()
        for i, (line, (code, _)) in enumerate(zip(original.splitlines(), lexical_lines(original)), 1):
            if code.strip():
                flush()
                if path == "src/SampledGRH.lean" and line.startswith(("namespace ", "def EstimateAt ", "theorem nonvanishing ", "theorem five_endpoints ")):
                    kept.append("")
                kept.append(line)
            elif line.strip():
                pending.append((i, line))
            else:
                flush()
        flush()
        result = "\n".join(kept) + "\n"
        if code_lines(original) != code_lines(result):
            raise ValueError(f"changing the documentation alters executable text in {path}")
        file.write_text(result)
    (output / "SOURCE-NOTES.md").write_text("\n".join(notes))
    (output / "SOURCE.sha256").write_text("".join(
        hashlib.sha256(p.read_bytes()).hexdigest() + "  " + str(p.relative_to(output)) + "\n"
        for p in sorted((output / "src").rglob("*.lean"))))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    compact(args.source, args.output)
