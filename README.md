# LeanReducer

LeanReducer shortens Lean proofs while retaining the public theorem statements and their permitted axioms. This repository hosts the reducer and its RH and Dirichlet GRH case study.

The command-line tool counts the full local import closure, searches for shorter proof bodies, and outputs a Git patch and a verification record. Each accepted edit must reduce both code lines and non-whitespace code characters. The report gives physical lines, UTF-8 bytes and the complete source-tree count as well.

## Measure a project

From this repository, run Python 3.10 or later. The analyzer uses the standard library.

```sh
python3 -m leanreducer analyze /path/to/project/src --entry Main
python3 -m leanreducer analyze /path/to/grh-compact/src --entry Main --cut New.Endgame.LongForms
```

Add `--import-audit` to find direct imports available through another project dependency. Add `--repetitions` to find repeated `seal` or `unseal` commands and the nearest module their sites already share.

To search for a different mathematical argument, add `--plan-cut MODEL` to an analysis with one `--cut` and set `OPENAI_API_KEY`. The architecture agent receives the selected source, bounded excerpts from up to four callers, and the exact replacement budget. Its JSON proposal gives the statement to replace, outstanding proof obligations, dependencies to check, and a first Lean experiment. Implementations can be audited with `reduce --patch`. [Architecture prompt](agents/architect.md)

A cut means removing that module and following all remaining import paths from the entry. The output counts the modules used exclusively through the cut. Any new code needed to prove a substitute theorem must be added back. Project-owned modules are counted before pinned external packages. The initial external namespaces are Mathlib, Lean, Std and Init. Add a package with `--external` if it belongs outside your source budget. Supply every project-owned dependency under the source root for a complete count.

## Try a reduction

A case file pins the public module, the expected theorem types and allowed axioms. The GRH case additionally pins a Git revision, Lean version, source directory, and protected files. Run against a trusted Lean project. Only the Git revision at HEAD is used. Uncommitted changes stay in the original checkout.

```sh
git clone https://github.com/EllaZhangCA/grh-lean-astra.git proof
git -C proof checkout --detach a57c37471c835968b1932a0f8347978b89ba7ab6
python3 -m leanreducer reduce --repo proof --config examples/grh/case.json \
  --output result --cache --target 50000 --rounds 3 --trials 4
```

Add `--ai MODEL` and set `OPENAI_API_KEY` to use the OpenAI Responses API. The planner selects a declaration, the prover suggests tactic and lemma combinations, and the reviewer ranks them. Each round makes up to three requests. The model receives candidate statements and the selected proof excerpt. The prompts are in [agents](agents). Offline mode tries direct substitution of singly used local facts in simple proof chains and a bounded list of Lean tactics. Use `--module`, `--decl` and repeated `--tactic` options to narrow a run.

The checker builds a fresh checkout, verifies the endpoint types with Lean, reads each axiom report, and runs `leanchecker` on edited modules and the entry. It discards failing trials and publishes the patch only after checking the final state. A verified partial result records `target_met: false`. The optional `--paranoid` flag also runs the project’s installed Lake Comparator against its challenge. For broader, human-reviewed mathematical refactors, use `--patch PATH` with a unified Git diff. This mode can add lemmas and change several modules. The source boundary and protected paths still apply. Lean source and Lake builds execute code, so use trusted projects and review externally supplied patches before running them.

## GRH case study

The complete candidate has **76,072 code lines** across 794 modules (**112,770 physical lines**). The independently checked 347-module package contains four intermediate results in **49,230 physical lines**. The full proof still needs a reduction of 26,072 code lines to reach 50,000. [Browse the complete candidate](https://github.com/DomTheDeveloper/LeanReducer/tree/41bbac1c78e806eced8fd373f6cb55e77a045af5) · [Download the complete candidate](examples/grh/artifacts/GRH-76072.zip) · [Download the four intermediate results](examples/grh/artifacts/GRH-milestones.zip)

The study tracks the original 17.37 million lines, the compact rewrite, and the remaining arithmetic obstacle. It includes a Lean-checked theorem reducing the half-plane goal for all Dirichlet characters to one bound at each factorial modulus. [Latest reduction and verification](examples/grh/REDUCTION-STUDY.md) · [Earlier measurements and fourth-power sampling](examples/grh/RESULTS.md)

A standalone **998-code-line conditional proof** derives all five public conclusions from a specific arithmetic estimate on fourth powers at factorial levels. The complete checkout has 19 modules and 1,365 physical lines. Its Lean 4.35 build, axiom audit and kernel replays passed. [Source](https://github.com/DomTheDeveloper/LeanReducer/tree/e9e575e17cead892a1047ae30da86098ce967cc3) · [Verification](https://github.com/DomTheDeveloper/LeanReducer/actions/runs/45986092341)

## Tests

```sh
python3 -m unittest discover -s tests -v
python3 tests/integration.py
```

The integration test uses Lean 4.33.1, Lake, and leanchecker on PATH, or elan with that toolchain installed. It rejects an invalid tactic, accepts a shorter proof, applies the emitted patch to a clean checkout and checks the public theorem again. The GRH case uses Lean 4.35.0. The default limit is five hours per build or check. Supply `--timeout SECONDS` to override it.
