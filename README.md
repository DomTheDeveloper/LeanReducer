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

Repeat `--cut` to measure the chosen modules individually and together. The joint result shows which dependencies become unnecessary only when several arguments change together. Use `--pair-audit` to test every pair below the entry against the line target, and `--exclude-from-pairs MODULE` to preserve a particular module as a potential caller. The reported minimum counts the retained source before writing any replacement proofs.

To search for a different mathematical argument, add `--plan-cut MODEL` to an analysis with one `--cut` and set `OPENAI_API_KEY`. The architecture agent receives the selected source, bounded excerpts from up to four callers, and the exact replacement budget. Its JSON proposal gives the statement to replace, outstanding proof obligations, dependencies to check, and a first Lean experiment. Implementations can be audited with `reduce --patch`. [Architecture prompt](agents/architect.md)

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

The complete candidate has **76,072 code lines** across 794 modules (**112,770 physical lines**). Four intermediate results and their dependencies occupy **49,230 physical lines**. All 347 modules match the independently checked upstream replay. The full proof still needs a reduction of 26,072 code lines to reach 50,000. [Browse the complete candidate](https://github.com/DomTheDeveloper/LeanReducer/tree/41bbac1c78e806eced8fd373f6cb55e77a045af5) · [Download the complete candidate](examples/grh/artifacts/GRH-76072.zip) · [Download the four intermediate results](examples/grh/artifacts/GRH-milestones.zip)

The study tracks the original 17.37 million lines, the compact rewrite, and the remaining arithmetic obstacle. It includes a Lean-checked theorem reducing the half-plane goal for all Dirichlet characters to one bound at each factorial modulus. [Latest reduction and verification](examples/grh/REDUCTION-STUDY.md) · [Earlier measurements and fourth-power sampling](examples/grh/RESULTS.md)

The every-level **conditional proof has 985 code lines**, 1,348 physical lines and 19 modules. One eventual weighted-prime estimate at a prescribed exponent for each factorial level implies all five public conclusions. The pinned Lean 4.35.0 build, axiom audit and all 19 module replays passed. [Complete project](https://github.com/DomTheDeveloper/LeanReducer/tree/680cdffe8dca5e2f3de405a615318d0989f0f055) · [Verification](https://github.com/DomTheDeveloper/LeanReducer/actions/runs/45988169144)

The **920-code-line conditional proof** uses 17 project modules and **944 physical lines**. All 18 checked-in Lean files, including three compatibility proofs, total **990 physical lines**. Each conductor and requested accuracy may use its own auxiliary modulus and divergent family of primes. Lean checked the five original conclusions under that arithmetic hypothesis, and a separate LeanReducer run audited its fully expanded statement. [Download the project](https://github.com/DomTheDeveloper/LeanReducer/archive/440ee79d9a051dedbd983495a6557ef4bcca4c68.zip) · [Native build and per-module replay](https://github.com/DomTheDeveloper/LeanReducer/actions/runs/45997603687) · [Independent reducer audit](https://github.com/DomTheDeveloper/LeanReducer/actions/runs/45997641927)

The 957-line factorial-level edition derives all five original conclusions from a sampled prime-error estimate on a family of primes with divergent sum of `log(p)/p`. All 18 source modules together contain **957 code lines and 982 physical lines**. The separate compatibility test brings every checked-in Lean file to **exactly 1,000 physical lines**. The arithmetic estimate remains the unconditional proof obligation. [Complete project ZIP](https://github.com/DomTheDeveloper/LeanReducer/archive/b95fc6679ddb55033c7d11a62bfbb832b7f1812b.zip) · [Build, axiom check and kernel replay](https://github.com/DomTheDeveloper/LeanReducer/actions/runs/45994424273) · [Reduction study](examples/grh/REDUCTION-STUDY.md)

The **976-code-line conditional proof** weakens the arithmetic assumption further. Only an unbounded set of good factorial levels is needed. The entire 19-module source has 1,338 physical lines. Lean checked the explicit implication to all five original conclusions and all 19 modules passed kernel replay. [976-line project ZIP](https://github.com/DomTheDeveloper/LeanReducer/archive/ae21d67f172b180b660d9bfa2183e3f806ab0ef2.zip) · [Build, axiom audit and kernel replay](https://github.com/DomTheDeveloper/LeanReducer/actions/runs/45989759982)

The sparse project has its own [reducer case](examples/grh/cofinal-case.json). Its contract spells out the prime inequality and every quantifier independently of `SampledGRH.Estimates`. The case fixes the original five statement definitions, the factorial modulus, and the four source modules defining the weighted prime error. Running the reducer against this contract reproduced the 976-line count and the three permitted axioms. [Completed audit and downloadable verification record](https://github.com/DomTheDeveloper/LeanReducer/actions/runs/45991669828)

```sh
git clone --single-branch --branch cofinal-sampled-grh https://github.com/DomTheDeveloper/LeanReducer.git cofinal-proof
git -C cofinal-proof checkout --detach ae21d67f172b180b660d9bfa2183e3f806ab0ef2
python3 -m leanreducer reduce --repo cofinal-proof --config examples/grh/cofinal-case.json \
  --output cofinal-audit --cache --target 1000
```

A separate two-module project proves an equivalent bounded-height test for nonvanishing. Its 93 code lines restrict the remaining zero search to one bounded region in the critical strip per factorial level. [Bounded-height criterion](examples/grh/FactorialBoxes.lean) · [Pinned build and kernel replay](https://github.com/DomTheDeveloper/LeanReducer/actions/runs/45988875281)

A further formulation counts only the primes contained in the chosen set when summing log(p)/p. This removes seven code lines. The annotated **950-code-line** project has 1,304 physical lines and passed a clean Lean 4.35 build and kernel replay of all 18 modules. The version with standalone comments in Markdown has **975 physical Lean lines**, counting the full local source tree. The surviving arithmetic obligation is the sampled bound on such a family for arbitrarily large factorial levels. [Annotated project and verification](https://github.com/DomTheDeveloper/LeanReducer/actions/runs/45994270811) · [975-physical-line project](https://github.com/DomTheDeveloper/LeanReducer/tree/39d23a7d38d6d53c3618646c8831cd91fd8295eb) · [Compact build and kernel replay](https://github.com/DomTheDeveloper/LeanReducer/actions/runs/45995433632) · [Independent audit and compatibility test](https://github.com/DomTheDeveloper/LeanReducer/actions/runs/45996229428) · [Exact reducer case](examples/grh/prime-weight-case.json)

## Tests

```sh
python3 -m unittest discover -s tests -v
python3 tests/integration.py
```

The integration test uses Lean 4.33.1, Lake, and leanchecker on PATH, or elan with that toolchain installed. It rejects an invalid tactic, accepts a shorter proof, applies the emitted patch to a clean checkout and checks the public theorem again. The GRH case uses Lean 4.35.0. The default limit is five hours per build or check. Supply `--timeout SECONDS` to override it.
