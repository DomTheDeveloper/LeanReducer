# How much of the RH and Dirichlet GRH proof is left?

This page records the shared-command experiment. The [combined reduction](REDUCTION-STUDY.md) also simplifies the public endpoints and gives the latest counts.

A shared four-line Lean command reduces the Astra source from **76,113 to 76,075 code lines**. The five public statements and the mathematical proofs remain byte-identical after expanding the command. The new source is **26,075 code lines above 50,000** and **75,075 above 1,000**. For physical lines those gaps are 62,775 and 111,775.

[Download the complete source at the measured revision](https://github.com/DomTheDeveloper/LeanReducer/archive/30ee9e9c89c9fd7539251d86c7881d480ae0e677.zip) · [Fresh Lean 4.35 build and kernel check](https://github.com/DomTheDeveloper/LeanReducer/actions/runs/45981813632)

## Comparison

| Edition | Project modules | Physical lines | Nonblank code lines |
| --- | ---: | ---: | ---: |
| Alpöge and Claude, original archive | 175,187 | 17,374,215 | — |
| Sernau and colleagues, readable | 803 | 477,124 | 299,902 |
| Sernau and colleagues, compact | 794 | 112,827 | 76,149 |
| EllaZhangCA Astra revision | 794 | 112,791 | 76,113 |
| LeanReducer shared Ext command | 794 | 112,775 | 76,075 |

The original physical count comes from the published archive inventory. The other rows were counted directly under each pinned edition’s `src`. Code lines include imports and declarations and exclude blank lines and comments. The physical figures include both. All counts exclude the pinned Lean toolchain and Mathlib. Every local compact module is reachable from `Main`. The compact graph contains 1,400 direct import edges. Across the local graph, none of those targets is already available through another direct import of the same module. Run the analyzer with `--import-audit` to repeat the check. The physical reduction from the original archive to the compact edition was about 154-fold. [Archive inventory](https://riemannhypothesissolved.com/proof-in-numbers/) · [Published compact source](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact)

Sutherland’s comparison of the two independent exports found 51,408 remaining declarations in the readable proof and 39,420 in the compact proof after setting aside 165,163 common library declarations. The full elaborated exports grew from 4.49 to 5.17 GB while the source shrank. [Export analysis](https://math.mit.edu/~drew/shortgrh/)

The rewrite retained the method and often used different intermediate arguments. Its readable and compact editions split library results missing from Mathlib into `Lib` and the proof-specific argument into `New`. The seven later Astra proof edits give concrete examples. One uses Mathlib’s integrality of finite-group character values in place of a cyclic-subgroup decomposition. Two use a bound on the number of prime ideals above a rational prime. In the main inequality, a shift of the row height lets one linear combination handle the missing rows. The released sources support these comparisons. They do not record every historical editing step. [Authors’ account](https://github.com/lsernau/grh-lean) · [Astra revision and verification](https://github.com/EllaZhangCA/grh-lean-astra/tree/a57c37471c835968b1932a0f8347978b89ba7ab6)

## The new patch

Twenty-one commands in twenty modules repeat the same six Ext identifiers. These commands control which definitions Lean unfolds during elaboration. The patch defines `sealAbelianExt` once in a shared dependency that every site already imports. It replaces the repeated three-line commands with calls, including the six uses restricted to the following command. Running `analyze --entry Main --repetitions` on the Astra source identifies the 21 sites and their nearest common local import, `Lib.General.Algebra.CechDescent`. This saves 42 invocation lines and adds four lines of shared code. Source bytes fall from 7,417,833 to 7,415,016. Per-file change notices are included in the physical count. [Native Lean patch](share-ext.patch)

We checked that expanding the abbreviation restores every byte of **all 794 Lean source files** at the pinned Astra revision. A native Lean scope test checked all six flags before, inside and after a scoped invocation and after a persistent invocation. The scope test uses stand-in declarations and Lean 4.33.1. The fork authors report a full build and axiom check of the 76,113-line base. Sutherland’s independent multikernel and Comparator checks cover Sernau’s 76,149-line compact edition. The 76,075-line revision subsequently passed a clean Lean 4.35.0 build and five axiom checks. The combined 76,072-line revision also passed its clean build, five frozen theorem-type and axiom checks, and native replay of all 23 changed modules. [Complete verification record](verification-results.json) [Expansion check](check_ext.py) · [Scope test](../../tests/SealScope.lean) · [Independent verification](https://math.mit.edu/~drew/shortgrh/) · [Full-build workflow runs](https://github.com/DomTheDeveloper/LeanReducer/actions/workflows/grh.yml)

```sh
git clone https://github.com/EllaZhangCA/grh-lean-astra.git proof
git -C proof checkout --detach a57c37471c835968b1932a0f8347978b89ba7ab6
git -C proof apply "$PWD/examples/grh/share-ext.patch"
python3 examples/grh/check_ext.py proof
python3 -m leanreducer analyze proof/grh-compact/src --entry Main
```

For the full upstream checks, run `lake exe cache get`, `lake build` and `lake env lean scripts/PrintAxioms.lean` from `proof/grh-compact`. A configured Comparator installation can additionally run `lake comparator --paranoid`. The five expected theorem types and permitted axioms are in [case.json](case.json).

## Where a 50,000-line proof could come from

On the 76,113-line base, the 573 `Lib` modules contribute 51,269 code lines. The 219 `New` modules contribute 24,825. The entry and statement modules contribute 19 together. Even eliminating the whole proof-specific part would leave the present library over the 50,000-line budget.

| Module on the Astra base | Code lines in its own import closure | Lines exclusive to paths through it from Main | Remaining if replaced for free |
| --- | ---: | ---: | ---: |
| `New.Endgame.LongForms` | 75,474 | 58,905 | 17,208 |
| `New.Endgame.ShortAndEnough` | 67,670 | 480 | 75,633 |
| `New.Data.DataExist` | 17,131 | 562 | 75,551 |
| `New.Endgame.OneSidedCriterion` | 1,251 | 477 | 75,636 |
| `New.Endgame.PrimeError` | 649 | 68 | 76,045 |

Each row is a separate counterfactual. Dependencies reached through a second path stay in the remaining total. The new edition has 58,867 lines exclusive to `LongForms` and the same 17,208 lines outside it. Cutting `LongForms` therefore leaves a **32,792-line budget** to prove a replacement and supply its interfaces on either revision. The corresponding mathematical problem is to derive the required weighted-prime inequality by a shorter argument. The present proof compares upper and lower bounds for one covolume. Short forms, enough forms and the lower bound on lengths all feed the comparison. Removing `DataExist` alone frees only 562 lines since other branches still use its inputs. [Reproducible graph and counts](baseline.json) · [Authors’ guide to the inequalities](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/GUIDE.md)

The tactic-body search recognized 1,408 multiline bodies on this base. Replacing every one with a single tactic would save at most 19,860 code lines under this particular recognizer. Even that ideal run would leave 56,253. Additional declaration shapes, reuse of existing Mathlib theorems or an argument spanning several modules must supply the balance. This is a ceiling for this pass, not a lower bound on Lean proof size.

A separate audit streamed the 5,172,274,528-byte compact kernel export. Its uncompressed SHA-256 matched the published digest, and the reader found 204,583 declaration records. A deliberately conservative screen found 59 top-level theorem or lemma spellings absent even as a component of an exported declaration name, spanning 72 code lines. Of those, 28 had only a single spelling occurrence in the source, spanning 34 lines. Common names cause false negatives. A simplifier or elaborator can depend on a source declaration even when its name drops out of the final term. These are candidates for build tests and have not been deleted. [Candidate rows](export-candidates.json) · [Published export](https://math.mit.edu/~drew/shortgrh/)

```sh
git clone https://github.com/lsernau/grh-lean.git original
git -C original checkout --detach 72fead102f663d5c7a407964a13dc0cf9d977207
curl -fsSL https://math.mit.edu/~drew/shortgrh/compact-solution.ndjson.zst |
  zstd -dc | PYTHONPATH=. python3 examples/grh/export_audit.py original/grh-compact/src
```

## What fourth powers buy

The previous sampling package checked the passage from squares to all real inputs under an increment bound. Here Lean also checks **fourth powers**, using a quadratic interpolation error. For a nonnegative finite weighted sum with the stated logarithmic normalization, `WeightedFourthPowers.bounds_iff` proves that eventual upper bounds with every exponent strictly between −½ and 0 on fourth powers are equivalent to those bounds on all sufficiently large real arguments.

For adjacent samples `u` and `v`, the interpolation loss at `x` is at most `(x−u)(v−x)/(φx²)`. For `u = n⁴` and `v = (n+1)⁴`, the gap is at most `15n³`. With `φ ≥ 1`, the resulting loss is at most `225/√x`. A small slack between the sample exponent and the requested exponent absorbs the constant. The three source files contain 176 code lines over Mathlib, with no GRH imports. We checked the final theorem on Lean 4.33.1. It uses `propext`, `Classical.choice` and `Quot.sound`. [Finite-sum interpolation](ReciprocalInterpolation.lean) · [Fourth-power mesh](FourthPowers.lean) · [Combined theorem](WeightedFourthPowers.lean)

The direct specialization `PrimeErrorFourthPowers.bounds_iff` uses the upstream `primeError_eq_sum` identity and nonnegativity of `lambdaClass`. Its entire project import closure is **849 code lines, 1,260 physical lines and 12 modules**. Those figures comprise 649 upstream code lines, 176 interpolation and sampling lines, and 24 lines applying them to the actual prime error. A clean Lean 4.35.0 build checked this specialization against the actual upstream declarations. Its axiom audit reported only the three standard axioms and the kernel replay passed. The statement transfers bounds between samples and all real arguments. Proving the sampled bounds requires additional arithmetic. [Prime-error theorem](PrimeErrorFourthPowers.lean) · [Self-contained 849-line project](https://github.com/DomTheDeveloper/LeanReducer/tree/e49cc72aac895a7d91ad59221dcb1cff8fa51a97) · [Completed build](https://github.com/DomTheDeveloper/LeanReducer/actions/runs/45984868143)

The quadratic loss has a matching local lower bound in the same finite-sum model. For every `0 < h < 1`, a single nonnegative weight gives zero at `1/(1+h)` and `1/(1−h)` and gives at least `h²/2` at `1`. This rules out a uniform error of smaller order in the reciprocal mesh width from these hypotheses alone. The example varies with the interval. The actual prime weights may satisfy stronger bounds. Lean checked this theorem with the three standard axioms. [Single-weight example](SharpInterpolation.lean)

The arithmetic residue condition is also checked for **every positive modulus parameter q**. If `d mod (18480q) = 9240q−1`, then `d mod 8 = 7` and `gcd(18480q,d) = 1`. Its Lean proof uses only `propext` and `Quot.sound`. The older fixed-level helper shrank from 16 to 13 code lines. [All levels](AuxiliaryResidue.lean) · [Level one](OrdinaryResidue.lean)

A 1,000-line unconditional proof still needs a proof of the arithmetic estimate at the sampled fourth powers for the actual prime error and all required characters, or another route to the same nonvanishing statement. In addition, the existing one-sided analytic criterion already imports 1,251 lines before any new arithmetic proof is added. A proof at this budget must shorten or replace that criterion as well if it follows this route. The sampling files prove a conditional equivalence; the arithmetic estimate that makes it yield GRH remains the central missing step.
