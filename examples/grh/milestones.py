"""Create a standalone, reproducible Lake project for four intermediate GRH results."""
import argparse
import hashlib
import io
from pathlib import Path
import subprocess
import sys
from urllib.request import urlopen
import zipfile

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from leanreducer.source import Corpus

COMMIT = "72fead102f663d5c7a407964a13dc0cf9d977207"
MIT = "https://math.mit.edu/~drew/shortgrh/"
RECORDS = {"source-files.sha256": "cd537287df9d0580afa93fcf7237370967520295f38075805964e4d4bbb9f1f8",
           "compact-replay-leanchecker.results.txt": "afda4b95fb0c64a06d3b4935398836470a7840009fc4a154f00db29ae78838c5"}
ROOTS = ["New.Data.DataExist", "New.Heights.OneDeterminant",
         "New.Filling.Moments", "New.Endgame.OneSidedCriterion"]


def sha(data):
    return hashlib.sha256(data).hexdigest()


def pack(checkout, output, evidence=None):
    rev = subprocess.check_output(["git", "-C", str(checkout), "rev-parse", "HEAD"], text=True).strip()
    if rev != COMMIT:
        raise ValueError("expected lsernau/grh-lean at " + COMMIT)
    records = {}
    for filename, digest in RECORDS.items():
        if evidence:
            data = (evidence / filename).read_bytes()
        else:
            with urlopen(MIT + filename, timeout=60) as response:
                data = response.read()
        if sha(data) != digest:
            raise ValueError("unexpected independent record: " + filename)
        records[filename] = data.decode()
    hashes = {p: h for h, p in (line.split(maxsplit=1) for line in records["source-files.sha256"].splitlines())}
    replay = {l.split()[0]: l for l in records["compact-replay-leanchecker.results.txt"].splitlines()
              if len(l.split()) == 3 and l.split()[1] == "ok"}
    base = checkout / "grh-compact"
    src = Corpus(base / "src", ["Mathlib"])
    keep = set().union(*(src.walk(root) for root in ROOTS))
    counts = src.size(keep)
    if (counts["modules"], counts["physical"], counts["code"]) != (347, 49230, 31714):
        raise ValueError("unexpected source counts")
    members = {}
    def verified(path):
        data = (base / path).read_bytes()
        if sha(data) != hashes["grh-compact/" + path]:
            raise ValueError("source hash mismatch: " + path)
        return data
    for m in sorted(keep):
        path = src.paths[m].relative_to(base).as_posix()
        members[path] = verified(path)
    for file in ("lean-toolchain", "lake-manifest.json", "LICENSE", "NOTICE", "ATTRIBUTION.md", "REFERENCES.md"):
        members[file] = verified(file)
    conf = verified("lakefile.toml").decode()
    members["lakefile.toml"] = conf.split('[[lean_lib]]\nname = "Main"')[0].replace(
        'defaultTargets = ["Lib", "New", "Main"]', 'defaultTargets = ["Lib", "New"]')
    members["KERNEL-REPLAY.txt"] = "\n".join(replay[m] for m in sorted(keep)) + "\n"
    members["SOURCE.sha256"] = "".join(sha(data) + "  " + path + "\n"
                                       for path, data in sorted(members.items()) if path.startswith("src/"))
    members["README.md"] = f"""# Four results inside the compact GRH proof

These 347 project modules prove the existence of the auxiliary data, a determinant height bound, the second-moment estimates for the filling argument, and the one-sided analytic criterion. The package covers 31,714 nonblank code lines and 49,230 physical Lean lines, plus the pinned Mathlib dependency. The complete RH and Dirichlet GRH proof also requires the remaining arithmetic and covolume arguments.

The four roots are {', '.join(ROOTS)}. The source is unchanged from lsernau/grh-lean at {COMMIT}. The Lake configuration selects the included libraries. Every included source file matched Andrew Sutherland's published SHA-256 record, and every module has a successful entry in his kernel replay of the original project. KERNEL-REPLAY.txt contains those entries. A fresh local source build is a separate check.

Run `sha256sum -c SOURCE.sha256`, `lake exe cache get`, then `lake build`. See LICENSE, NOTICE, ATTRIBUTION.md and REFERENCES.md for the upstream work.
"""
    stream = io.BytesIO()
    with zipfile.ZipFile(stream, "w", compression=zipfile.ZIP_DEFLATED) as archive:
        for path, contents in sorted(members.items()):
            info = zipfile.ZipInfo(path, (2026, 11, 25, 0, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o100644 << 16
            archive.writestr(info, contents)
    with output.open("xb") as file:
        file.write(stream.getvalue())
    return counts


if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("checkout", type=Path)
    p.add_argument("output", type=Path)
    p.add_argument("--evidence", type=Path)
    a = p.parse_args()
    print(pack(a.checkout, a.output, a.evidence))
