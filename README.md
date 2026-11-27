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

Repeat `--cut` to measure the chosen modules individually and together. The joint result shows which dependencies become unnecessary only when several arguments change together. Use `--pair-audit` to test every pair below the entry against the line target, and `--exclude-from-pairs MODULE` to preserve a particular module as a potential caller. The reported minimum counts the retained source before writing any replacement proofs. Use `--triple-audit` to examine every three-module combination and report the first ten meeting the target. Both audits accept `--exclude-from-audit MODULE`. The number of combinations grows cubically for triples.

To search for a different mathematical argument, set `OPENAI_API_KEY` and add `--plan-cut MODEL` to an analysis. Select modules with one or more `--cut` arguments, or let a pair or triple audit choose the group leaving the fewest lines. The architecture agent receives the selected source excerpts, the surviving callers, and one shared replacement budget. Its JSON proposal gives the statement to replace, outstanding proof obligations, dependencies to check, and a first Lean experiment. Implementations can be audited with `reduce --patch`. [Architecture prompt](agents/architect.md)

A cut means removing that module and following all remaining import paths from the entry. The output counts the modules used exclusively through the cut. Any new code needed to prove a substitute theorem must be added back. Project-owned modules are counted before pinned external packages. The initial external namespaces are Mathlib, Lean, Std and Init. Add a package with `--external` if it belongs outside your source budget. Supply every project-owned dependency under the source root for a complete count.

## Try a reduction

A case file pins the public module, the expected theorem types and allowed axioms. Its optional `open_scoped` list makes Lean notation and instances such as `Classical` available in the independent statement check. The GRH case additionally pins a Git revision, Lean version, source directory, and protected files. Run against a trusted Lean project. Only the Git revision at HEAD is used. Uncommitted changes stay in the original checkout.

```sh
git clone https://github.com/EllaZhangCA/grh-lean-astra.git proof
git -C proof checkout --detach a57c37471c835968b1932a0f8347978b89ba7ab6
python3 -m leanreducer reduce --repo proof --config examples/grh/case.json \
  --output result --cache --target 50000 --rounds 3 --trials 4
```

Add `--ai MODEL` and set `OPENAI_API_KEY` to use the OpenAI Responses API. The planner selects a declaration, the prover suggests tactic and lemma combinations, and the reviewer ranks them. Each round makes up to three requests. The model receives candidate statements and the selected proof excerpt. The prompts are in [agents](agents). Offline mode tries direct substitution of singly used local facts in simple proof chains and a bounded list of Lean tactics. Use `--module`, `--decl` and repeated `--tactic` options to narrow a run.

The checker builds a fresh checkout, verifies the endpoint types with Lean, reads each axiom report, and runs `leanchecker` on edited modules and the entry. It discards failing trials and publishes the patch only after checking the final state. A verified partial result records `target_met: false`. The optional `--paranoid` flag also runs the project’s installed Lake Comparator against its challenge. For broader, human-reviewed mathematical refactors, use `--patch PATH` with a unified Git diff. This mode can add lemmas and change several modules. The source boundary and protected paths still apply. Lean source and Lake builds execute code, so use trusted projects and review externally supplied patches before running them.

## GRH case study

| Download | Result | Project code lines | Project physical lines |
| --- | --- | ---: | ---: |
| [Complete source](examples/grh/artifacts/GRH-76072.zip) | Five unconditional RH and Dirichlet GRH statements | **76,072** | **112,770** |
| [Four intermediate results](examples/grh/artifacts/GRH-milestones.zip) | Auxiliary data, a determinant bound, filling moments and a one-sided analytic criterion | 31,714 | 49,230 |
| [Short conditional proof](https://github.com/DomTheDeveloper/LeanReducer/archive/440ee79d9a051dedbd983495a6557ef4bcca4c68.zip) | The five original statements given the sampled prime-error estimate | **920** | **944** |

Counts include every local import above the pinned Lean and Mathlib. In the short project, a separate 46-line test file brings all checked-in Lean source to **990 physical lines**. Lean 4.35 compiled and replayed the 17 project modules. LeanReducer also checked the expanded arithmetic hypothesis against the five conclusion types. [Short proof build](https://github.com/DomTheDeveloper/LeanReducer/actions/runs/45997603687) · [Independent reducer audit](https://github.com/DomTheDeveloper/LeanReducer/actions/runs/45997641927) · [Full source workflow](https://github.com/DomTheDeveloper/LeanReducer/actions/runs/45983909693)

The 50,000-code-line unconditional target requires another **26,072 lines** of reduction on the full source. The short proof gives a different route. At any positive conductor and requested accuracy, establish the fourth-power bound on a family of admissible auxiliary primes whose sum of log(p)/p diverges. The modulus may be any suitable multiple of the conductor. Keeping the short proof would leave **49,080 code lines** for this arithmetic argument at the 50,000-line target, or **80** at 1,000. [Exact mathematical statement](https://github.com/DomTheDeveloper/LeanReducer/blob/440ee79d9a051dedbd983495a6557ef4bcca4c68/src/SampledGRH.lean) · [Source counts, evidence and alternatives](examples/grh/REDUCTION-STUDY.md)

The original archive contained 15,531,759 code lines and 17,374,215 physical lines. All 175,187 project modules were reachable from its public entry. The study follows the readable and compact rewrites, the later source changes, the intermediate results under 50,000 physical lines, and the earlier conditional estimates. [Historical measurements](examples/grh/edition-measurements.json) · [Original reduction experiments](examples/grh/RESULTS.md) · [Bounded-height criterion](examples/grh/FactorialBoxes.lean)

To reproduce the short proof's audit from the LeanReducer root:

```sh
git clone --single-branch --branch auxiliary-multiples-grh https://github.com/DomTheDeveloper/LeanReducer.git multiples-proof
git -C multiples-proof checkout --detach 440ee79d9a051dedbd983495a6557ef4bcca4c68
python3 -m leanreducer reduce --repo multiples-proof --config examples/grh/multiples-case.json \
  --output multiples-audit --cache --target 1000
```

## Tests

```sh
python3 -m unittest discover -s tests -v
python3 tests/integration.py
```

The integration test uses Lean 4.33.1, Lake, and leanchecker on PATH, or elan with that toolchain installed. It rejects an invalid tactic, accepts a shorter proof, applies the emitted patch to a clean checkout and checks the public theorem again. The GRH case uses Lean 4.35.0. The default limit is five hours per build or check. Supply `--timeout SECONDS` to override it.
