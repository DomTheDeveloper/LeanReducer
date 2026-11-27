# From 17.37 million lines to the next proof obligation

The combined RH and Dirichlet GRH candidate contains **76,072 code lines and 112,770 physical lines** in 794 project modules. Reaching 50,000 requires removing another **26,072 code lines** or **62,770 physical lines**, depending on which measure is intended. The 1,000-line goal is open. [Full candidate](artifacts/GRH-76072.zip) · [Machine-readable measurements](combined-metrics.json)

## Comparable counts

| Source edition | Project modules | Physical lines | Code lines |
| --- | ---: | ---: | ---: |
| Original archive | 175,187 | 17,374,215 | Unmeasured here |
| Sernau and colleagues, readable | 803 | 477,124 | 299,902 |
| Sernau and colleagues, compact | 794 | 112,827 | 76,149 |
| EllaZhangCA Astra revision | 794 | 112,791 | 76,113 |
| Shared Ext command | 794 | 112,775 | 76,075 |
| Shared Ext command and direct public theorems | 794 | **112,770** | **76,072** |

Physical lines include comments and blank lines. Code lines exclude both and count imports. The compact candidate has 7,414,871 source bytes. All 794 modules are reachable from `Main`. The table counts project sources above the pinned toolchain and Mathlib dependency. The original physical count is from the authors' archive. The later counts are from the versioned sources. [Original archive inventory](https://riemannhypothesissolved.com/proof-in-numbers/) · [Independent verification and source hashes](https://math.mit.edu/~drew/shortgrh/) · [Compact edition](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact)

## What produced the reduction

The decisive reduction was a mathematical rewrite. The readable edition already reduced the original to 477,124 physical lines. Its library isolates results absent from Mathlib, and its proof-specific part makes the comparison of upper and lower bounds on a covolume explicit. The readable and compact editions differ by a further 364,297 physical lines. The independent kernel exports went from 4,485,867,644 to 5,172,274,528 uncompressed bytes, an increase of 15.3% as the code-line count fell by 74.6%. The shorter source and the exported proof therefore give different answers to the size question. In later Astra changes, Mathlib's theorem on integrality of character values replaces an argument through cyclic subgroups, and a prime-ideal count serves two local bounds. The available revisions establish the counts and show these instances. They do not attribute each original line to one transformation. [Earlier study and reproductions](RESULTS.md) · [Independent export sizes](https://math.mit.edu/~drew/shortgrh/) · [Astra changes](https://github.com/EllaZhangCA/grh-lean-astra/tree/a57c37471c835968b1932a0f8347978b89ba7ab6)

The shared command saves 38 code lines across 21 uses, counting the new definition. Its native scope test passed on both Lean 4.33.1 and the project’s pinned Lean 4.35.0. The next patch defines three public results where their underlying arguments are proved and removes three wrapper hops. The public RH result uses the public zeta result directly. The five challenge names and statement types are preserved in the source. The intermediate names `New.grh`, `New.zeros_on_line`, and `New.zeta_zeros_on_line` are retired. Downstream code using those names or the more general conditional helpers needs to adapt. [Ext patch and inverse check](check_ext.py) · [Public theorem changes](public-endpoints.patch) · [Frozen challenge contract](case.json)

An audit of the original compact kernel export independently identified the exact-type alias between `New.grh` and `LFunction_ne_zero_of_half_lt_re`. The SHA-256 of the 5,172,274,528-byte uncompressed export matched the published digest. Of 165,589 theorem records, 28,075 occur in 5,623 groups sharing a type node and universe parameters. The export includes Mathlib and generated declarations. A group is a search lead, and by itself establishes no removable project lines. [Streaming analyzer](kernel_types.py) · [Independent proof export](https://math.mit.edu/~drew/shortgrh/)

## Four results that fit below 50,000 physical lines

The standalone package contains the union of all project imports of these four modules from upstream revision `72fead102f663d5c7a407964a13dc0cf9d977207`.

| Module | What it supplies |
| --- | --- |
| `New.Data.DataExist` | Existence of the auxiliary arithmetic data |
| `New.Heights.OneDeterminant` | A determinant height bound |
| `New.Filling.Moments` | Second-moment estimates in the filling argument |
| `New.Endgame.OneSidedCriterion` | Passage from a one-sided prime-sum estimate to a zero-free region |

The union has **347 modules, 31,714 code lines and 49,230 physical lines**. Each of the 347 source hashes matched Andrew Sutherland's published inventory, and each module had a successful entry in the upstream kernel replay. The archive includes those records, the source, the pinned Lake and Mathlib configuration, and attribution. Rebuilding the archive from the pinned inputs reproduced its SHA-256. These four results leave the covolume comparison and the unconditional prime estimate outstanding. [Four-result project](artifacts/GRH-milestones.zip) · [Reproduction script](milestones.py) · [Upstream checker records](https://math.mit.edu/~drew/shortgrh/)

The offline reducer was also checked on a Lean 4.35.0 proof of `Nat.succ` injectivity. It replaced three local proof steps with `exact Nat.succ.inj h`, taking the file from four code lines to two. Lean checked the public type, and the kernel replay passed with zero axioms. On the combined GRH candidate that same straight-line substitution rule matched zero of the 1,463 multiline theorem bodies recognized by the current reader. This measures why that rule alone cannot shorten this particular proof. The planner, prover and reviewer can also try Lean tactics through the Responses API. [Reduction implementation](../../leanreducer/inlining.py) · [Agent prompts](../../agents)

## What would reach 50,000

On the combined revision, removing the import path through `New.Endgame.LongForms` removes **58,867 code lines** used exclusively on that path and leaves **17,205**. A new proof and its additional local imports could use at most **32,795 code lines** to finish under the inclusive 50,000-line limit. Using physical lines leaves 28,261 and a replacement budget of 21,739. These are budgets for a replacement that still proves all five endpoints. The module itself uses the upper covolume bound, enough independent forms and the lower bound for integral forms. A shorter derivation of the weighted prime estimate could bypass that comparison. [Exact import cut](combined-metrics.json) · [Upstream proof guide](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/GUIDE.md)

## What would reach 1,000

Lean checks a smaller target for the analytic endgame. Write `M(k) = 18480 × (k+1)!`. Nonvanishing for every Dirichlet character of every positive modulus on Re(s) > 1/2, with the principal pole excepted, is equivalent to nonvanishing for every character of modulus `M(k)` only on Re(s) > 1/2 + 1/(k+1), for every natural k. Given q and a point strictly right of 1/2, one factorial multiple is divisible by q and has a small enough margin. The Euler factors in change of level then transfer nonvanishing to q. The file compiles over the proof's pinned Lean 4.35.0 and Mathlib revision with axioms `propext`, `Classical.choice` and `Quot.sound`. [Complete Lean proof](FactorialLevels.lean)

The original one-sided analytic criterion imports 1,251 code lines, and the fourth-power specialization for the actual prime error imports 849. These two sets of imports overlap. The standalone reductions below keep the required declarations and bring the full conditional implication below 1,000 code lines. A shorter arithmetic argument must still prove its sampled prime-error hypothesis. [Original analytic and arithmetic interfaces](RESULTS.md) · [Fourth-power specialization](PrimeErrorFourthPowers.lean)

## A checked 998-line route from sampled estimates to all five conclusions

The standalone project proves `SampledGRH.Estimates →` the conjunction of the five original RH and Dirichlet GRH statements. A clean build on the original Lean 4.35.0 and Mathlib pins passed. Lean checked the exact implication, reported only `propext`, `Classical.choice` and `Quot.sound`, and replayed every one of the 19 project modules. [Standalone source](https://github.com/DomTheDeveloper/LeanReducer/tree/e9e575e17cead892a1047ae30da86098ce967cc3) · [Download the 998-line project](https://github.com/DomTheDeveloper/LeanReducer/archive/e9e575e17cead892a1047ae30da86098ce967cc3.zip) · [Build, axiom audit and kernel replay](https://github.com/DomTheDeveloper/LeanReducer/actions/runs/45986092341)

Let `q = (k+1)!` and `M = 18480q`. For each auxiliary prime `d ≡ 9240q−1 (mod M)` and each real exponent `−½ < a < 0`, the hypothesis requires the actual upstream prime error to satisfy `primeError d M (n⁴) ≤ (n⁴)^a` for all sufficiently large natural `n`. The threshold may depend on the level, prime and exponent. The proof transfers the estimate to real arguments, applies the one-sided analytic criterion and descends from the factorial levels to every positive conductor. The functional equations then give all five original conclusions. [Lean statement and proof](SampledGRH.lean)

| Source used for this implication | Modules | Code lines | Physical lines |
| --- | ---: | ---: | ---: |
| Original analytic imports and new sampling argument | 26 | 1,582 | 2,288 |
| Standalone analytic project | 19 | 998 | 1,365 |

Seven unneeded modules contributed 380 code lines, including 135 for adelic valuations. Selecting the character definitions, the one-sided criterion and the applicable Lean settings removed a further 204 lines. Every project-owned source dependency is included. The revised project still contains the actual prime-weight definition, the analytic estimates and the functional-equation proofs. [Original-import verification](https://github.com/DomTheDeveloper/LeanReducer/actions/runs/45985738013) · [Source changes for the six retained upstream modules](conditional-slice.patch)

The 998 lines prove the implication. The remaining arithmetic obligation is a derivation of the sampled inequalities. The present unconditional project obtains the estimates through the covolume argument. An unconditional proof at the 1,000-code-line budget has only two additional lines available if it keeps this analytic project intact. A shorter common argument may change that budget.

## One exponent per level in 985 code lines

A further standalone proof requires just one exponent at each factorial level. Given a natural `k`, set `q = (k+1)!`, `M = 18480q` and `aₖ = −½ + 1/(4(k+1))`. For every prime `d ≡ 9240q−1 (mod M)`, assume `primeError d M (n⁴) ≤ (n⁴)^aₖ` for all sufficiently large natural `n`. The threshold may depend on `k` and `d`. These bounds imply all five original conclusions. The proof transfers the sample bound to the real exponent `−½ + 1/(k+1)` and uses the available margin to reach each required zero-free half-plane. The whole source is **985 code lines, 1,348 physical lines and 19 modules**. [Lean theorem](https://github.com/DomTheDeveloper/LeanReducer/blob/680cdffe8dca5e2f3de405a615318d0989f0f055/src/SampledGRH.lean) · [Complete project ZIP](https://github.com/DomTheDeveloper/LeanReducer/archive/680cdffe8dca5e2f3de405a615318d0989f0f055.zip) · [Lean 4.35 build, axiom check and replay](https://github.com/DomTheDeveloper/LeanReducer/actions/runs/45988169144)

Factoring the interpolation proof into a single transfer inequality allows the proof to discard the reverse implications and the quantified family of exponents. This saves thirteen source lines relative to the 998-line edition and weakens the arithmetic premise. Lean checked the public implication on the pinned Mathlib revision and `leanchecker` replayed every local module. The reported axioms are `propext`, `Classical.choice` and `Quot.sound`. [Source changes from 998 to 985](https://github.com/DomTheDeveloper/LeanReducer/compare/e9e575e17cead892a1047ae30da86098ce967cc3...680cdffe8dca5e2f3de405a615318d0989f0f055)

The arithmetic premise has a formal connection to the full proof. `UpstreamEstimate.samples_of_geometric` takes the exact statement of the upstream `eventually_primeError_le_rpow` theorem and proves all the fourth-power upper bounds in the 998-line edition. Each exponent prescribed in the 985-line edition lies in that family. The adapter builds against the original `Parameters` and `primeError` declarations. [Lean adapter](UpstreamEstimate.lean) · [Completed verification](https://github.com/DomTheDeveloper/LeanReducer/actions/runs/45987549345)

Counting each dependency once, the 985-line route leaves **49,015 further code lines** for a proof of the sampled estimates at a 50,000-line budget, or **15** at a 1,000-line budget. Any source restored to establish those estimates uses that allowance. Under a physical-line budget, the corresponding project already uses 1,348 lines. The original covolume route supplies a proof at the larger line count.

## Bounded height at each factorial level

There is also a direct target in the complex plane. The two-module project proves `LeanReducer.factorial_critical_boxes_iff`. For each natural $k$, let $M_k=18480(k+1)!$. Nonvanishing for every Dirichlet character of every positive modulus on the half-plane to the right of $1/2$, apart from the usual pole exception, is equivalent to testing every character of modulus $M_k$ only in the region

$$
\tfrac12 + \tfrac{1}{k+1} \leq \operatorname{Re}(s) < 1,
\qquad |\operatorname{Im}(s)| \leq k.
$$

For a point below real part one, choose $k$ large enough to reach its height, get to the left of its real part, and ensure that its character's modulus divides $M_k$. Change of level transfers nonvanishing back to that character. Mathlib supplies nonvanishing for real part at least one. The criterion still has infinitely many levels and continuously many complex arguments at each nonempty level. Its **93 code lines and 115 physical lines** include the two local modules above pinned Mathlib. The Lean 4.35 workflow checked a separate consumer of the implication, printed its three axioms, and replayed both modules. The 985-line prime-error project has its own source budget. [Lean proof](FactorialBoxes.lean) · [Two-module project](https://github.com/DomTheDeveloper/LeanReducer/tree/b99cee1d137cda79aaccbc181ae0f4097a8398b4) · [Successful build and replay](https://github.com/DomTheDeveloper/LeanReducer/actions/runs/45988875281)

## Arbitrarily sparse good levels in 976 code lines

The 985-line version requires the sampled estimate at every factorial level. The new branch only requires an unbounded set of good levels. A level $k$ is good when every prime $d$ in the specified residue class satisfies the one-exponent bound at that level. Its exact premise is

$$
\forall L\in\mathbb{N},\quad \exists k\ge L,\quad \mathrm{EstimateAt}(k).
$$

The same $k$ must work for every eligible prime at that level. The threshold in $n$ can depend on both $k$ and $d$. The proof permits gaps of arbitrary size between good levels. For a proposed zero of a character of modulus $m$, choose a good level whose index exceeds $m$ and makes the reciprocal margin small enough. Then $m$ divides the factorial modulus, so the estimate for that level and change of character level suffice.

Specializing the old general equivalence to the forward implication actually used in the proof removes nine code lines while weakening the arithmetic premise. The complete standalone project and its import closure both contain **976 code lines, 1,338 physical lines and 19 modules**. The pinned Lean 4.35 workflow checked the explicit unbounded-level implication against all five original conclusions. Its axiom audit reported `propext`, `Classical.choice` and `Quot.sound`, and all 19 modules passed kernel replay. The cofinal-modulus lemma also compiled separately on the same toolchain.

Holding these 976 lines fixed leaves **49,024 code lines** for the additional arithmetic proof and project-owned dependencies under 50,000, or **24** under 1,000. Proving every level good by the existing covolume argument supplies an unbounded set by taking $k=L$; it brings its original dependencies back into the count. [Standalone source](https://github.com/DomTheDeveloper/LeanReducer/tree/ae21d67f172b180b660d9bfa2183e3f806ab0ef2) · [Download ZIP](https://github.com/DomTheDeveloper/LeanReducer/archive/ae21d67f172b180b660d9bfa2183e3f806ab0ef2.zip) · [Clean build and kernel replay](https://github.com/DomTheDeveloper/LeanReducer/actions/runs/45989759982) · [Source changes against the 985-line edition](https://github.com/DomTheDeveloper/LeanReducer/compare/680cdffe8dca5e2f3de405a615318d0989f0f055...ae21d67f172b180b660d9bfa2183e3f806ab0ef2)

## Reproduce the combined source

From the LeanReducer root, with both named repositories available locally:

```sh
python3 examples/grh/package_candidate.py /path/to/grh-lean-astra GRH-76072.zip
python3 examples/grh/milestones.py /path/to/grh-lean GRH-milestones.zip
sha256sum GRH-76072.zip GRH-milestones.zip
```

To check both changes with the reducer, concatenate the two reviewed diffs and use the pinned case. Its five endpoint types and allowed axioms stay fixed while the implementation of an endpoint may move between source files.

```sh
cat examples/grh/share-ext.patch examples/grh/public-endpoints.patch > combined.patch
python3 -m leanreducer reduce --repo /path/to/grh-lean-astra --config examples/grh/case.json \
  --patch combined.patch --output checked-result --cache --target 50000
```

The milestone script expects the compact upstream commit above. The candidate script checks out the exact Astra revision from the supplied clone, applies both patches, checks byte-for-byte expansion of the shared command before the endpoint patch, and verifies all three published counts.

| Artifact | SHA-256 |
| --- | --- |
| `GRH-76072.zip` | `bfa537744deb18f7eefd4c9a5c051af96d05c77b13315480929a12261b848110` |
| `GRH-milestones.zip` | `3374140e77769502688302b0f60b5ea93c98b733a6fab05389c5e74e579b7b07` |

Sutherland's independent multi-kernel verification applies to the upstream compact revision at 76,149 code lines. The fork authors report a full build and axiom check of the 76,113-line Astra base. A local recheck of the changed arithmetic module stopped when available host memory fell to about 1.1 GiB. The combined candidate’s full build, five public type and axiom checks, and kernel replays have a separate [workflow run](https://github.com/DomTheDeveloper/LeanReducer/actions/runs/45983909693). [Independent upstream checks](https://math.mit.edu/~drew/shortgrh/) · [Candidate workflow status](https://github.com/DomTheDeveloper/LeanReducer/actions/workflows/grh.yml)
