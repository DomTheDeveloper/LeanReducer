"""Package the pinned compact project with both source patches, retaining its build files."""
import argparse
import io
from pathlib import Path
import subprocess
import sys
import tempfile
import zipfile

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from leanreducer.source import Corpus

BASE = "a57c37471c835968b1932a0f8347978b89ba7ab6"
HERE = Path(__file__).resolve().parent


def package(checkout, output):
    with tempfile.TemporaryDirectory(prefix="grh-candidate-") as temp:
        tree = Path(temp) / "tree"
        subprocess.run(["git", "clone", "--quiet", "--shared", "--no-checkout", "--",
                        str(checkout.resolve()), str(tree)], check=True)
        subprocess.run(["git", "-C", str(tree), "checkout", "--quiet", "--detach", BASE], check=True)
        subprocess.run(["git", "-C", str(tree), "apply", str(HERE / "share-ext.patch")], check=True)
        subprocess.run([sys.executable, str(HERE / "check_ext.py"), str(tree)], check=True)
        subprocess.run(["git", "-C", str(tree), "apply", str(HERE / "public-endpoints.patch")], check=True)
        project = tree / "grh-compact"
        corpus = Corpus(project / "src", ["Mathlib"])
        counts = corpus.size(corpus.walk("Main"))
        if (counts["modules"], counts["physical"], counts["code"]) != (794, 112770, 76072):
            raise ValueError("candidate differs from the measured proof")
        names = sorted(p for p in project.rglob("*") if p.is_file())
        stream = io.BytesIO()
        with zipfile.ZipFile(stream, "w", zipfile.ZIP_DEFLATED) as archive:
            for path in names:
                label = path.relative_to(project).as_posix()
                info = zipfile.ZipInfo("GRH-76072/" + label, (2026, 11, 27, 0, 0, 0))
                info.compress_type = zipfile.ZIP_DEFLATED
                info.external_attr = 0o100644 << 16
                archive.writestr(info, path.read_bytes())
            info = zipfile.ZipInfo("GRH-76072/REDUCTION.md", (2026, 11, 27, 0, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o100644 << 16
            archive.writestr(info, """# LeanReducer compact candidate

The input is EllaZhangCA/grh-lean-astra at a57c37471c835968b1932a0f8347978b89ba7ab6.
LeanReducer applied share-ext.patch followed by public-endpoints.patch.
The official Statements.lean, Challenge.lean, comparator.json, toolchain and dependency pins are unchanged.
The 794 files under src contain 76,072 code lines and 112,770 physical lines.
The guide and README describe the upstream edition. The three results previously reached through New.grh, New.zeros_on_line and New.zeta_zeros_on_line are now defined under the public theorem names.
The proof, references, license and attributions are included. The 50,000-line target is open.

Run lake exe cache get, lake build, and lake env lean scripts/PrintAxioms.lean from this directory.
Run lake comparator --paranoid with the pinned Comparator installed for an independent challenge check.
Verification status and additional experiments are at https://github.com/DomTheDeveloper/LeanReducer/tree/main/examples/grh.
""")
        with output.open("xb") as dst:
            dst.write(stream.getvalue())
        return counts


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkout", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    print(package(args.checkout, args.output))
