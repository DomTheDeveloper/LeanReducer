# From 17.37 million lines to the next proof obligation

The combined RH and Dirichlet GRH candidate contains **76,072 code lines and 112,770 physical lines** in 794 project modules. Reaching 50,000 requires removing another **26,072 code lines** or **62,770 physical lines**, depending on which measure is intended. The unconditional 1,000-line goal remains open. The verified implication from prime-error estimates uses 944 physical project lines. [Full candidate](artifacts/GRH-76072.zip) · [Machine-readable measurements](combined-metrics.json)

## Comparable counts

| Source edition | Project modules | Physical lines | Code lines |
| --- | ---: | ---: | ---: |
| Original archive | 175,187 | 17,374,215 | 15,531,759 |
| Sernau and colleagues, readable | 803 | 477,124 | 299,902 |
| Sernau and colleagues, compact | 794 | 112,827 | 76,149 |
| EllaZhangCA Astra revision | 794 | 112,791 | 76,113 |
| Shared Ext command | 794 | 112,775 | 76,075 |
| Shared Ext command and direct public theorems | 794 | **112,770** | **76,072** |

Physical lines include comments and blank lines. Code lines exclude both and count imports. The compact candidate has 7,414,871 source bytes. All 794 modules are reachable from `Main`. The table counts project sources above the pinned toolchain and Mathlib dependency. All four inventories now use the same lexer. The original archive was rebuilt from the author's 14 parts and matched MIT's published SHA-256. The later counts use pinned releases. [Original archive inventory](https://riemannhypothesissolved.com/proof-in-numbers/) · [Independent verification and source hashes](https://math.mit.edu/~drew/shortgrh/) · [Compact edition](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact)

### What changed inside the source

The joined original archive is 239,275,554 bytes, with SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. LeanReducer measured **15,531,759 code lines** and **17,374,215 physical lines** in its 175,187 project modules. Using the same lexer on the 76,072-line combined revision gives a **204.17-fold** reduction in code lines and a **154.07-fold** reduction in physical lines. The original archive pins Lean 4.33.1 and the rewritten editions pin Lean 4.35.0. External libraries are excluded in every column. [Original archive provenance](https://math.mit.edu/~drew/grh/#provenance) · [Machine-readable results](edition-measurements.json)

| Edition | Modules reachable from Main | Median code lines per module | Import lines |
| --- | ---: | ---: | ---: |
| Original archive | 175,187 of 175,187 | 51 | 909,822 |
| Readable rewrite | 803 of 803 | 355 | 1,742 |
| Compact rewrite | 794 of 794 | 82 | 1,400 |
| Complete combined revision | 794 of 794 | 82 | 1,400 |

In the original archive 61,407 modules contained 25 code lines or fewer. Its `Development` directory alone contained 11,050,038 code lines. The first rewrite consolidated the development into hundreds of substantially larger modules. The number of import lines fell by 908,080, which accounts numerically for about 6% of the 15,231,857-code-line difference between the original and readable editions. The second rewrite removed another 223,753 code lines with just 342 fewer import lines. All four trees are reachable from their public entry. These measurements describe file structure and source size independently of any proposed mapping of individual arguments. [Line census](edition_census.py) · [Import reachability](edition_imports.py) · [Authors' proof guide](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/GUIDE.md)

To reproduce the original counts from the joined archive, run the following at the LeanReducer root.

```sh
PYTHONPATH=. python3 examples/grh/edition_census.py --original-archive lean.tar.gz
PYTHONPATH=. python3 examples/grh/edition_imports.py --original-archive lean.tar.gz
```

## What produced the reduction

The decisive reduction was a mathematical rewrite. The readable edition already reduced the original to 477,124 physical lines. Its library isolates results absent from Mathlib, and its proof-specific part makes the comparison of upper and lower bounds on a covolume explicit. The readable and compact editions differ by a further 364,297 physical lines. The independent kernel exports went from 4,485,867,644 to 5,172,274,528 uncompressed bytes, an increase of 15.3% as the code-line count fell by 74.6%. The shorter source and the exported proof therefore give different answers to the size question. In later Astra changes, Mathlib's theorem on integrality of character values replaces an argument through cyclic subgroups, and a prime-ideal count serves two local bounds. The available revisions establish the counts and show these instances. They do not attribute each original line to one transformation. [Earlier study and reproductions](RESULTS.md) · [Independent export sizes](https://math.mit.edu/~drew/shortgrh/) · [Astra changes](https://github.com/EllaZhangCA/grh-lean-astra/tree/a57c37471c835968b1932a0f8347978b89ba7ab6)

The shared command saves 38 code lines across 21 uses, counting the new definition. Its native scope test passed on both Lean 4.33.1 and the project’s pinned Lean 4.35.0. The next patch defines three public results where their underlying arguments are proved and removes three wrapper hops. The public RH result uses the public zeta result directly. The five challenge names and statement types are preserved in the source. The intermediate names `New.grh`, `New.zeros_on_line`, and `New.zeta_zeros_on_line` are retired. Downstream code using those names or the more general conditional helpers needs to adapt. [Ext patch and inverse check](check_ext.py) · [Public theorem changes](public-endpoints.patch) · [Frozen challenge contract](case.json)

An audit of the original compact kernel export independently identified the exact-type alias between `New.grh` and `LFunction_ne_zero_of_half_lt_re`. The SHA-256 of the 5,172,274,528-byte uncompressed export matched the published digest. Of 165,589 theorem records, 28,075 occur in 5,623 groups sharing a type node and universe parameters. The export includes Mathlib and generated declarations. A group is a search lead, and by itself establishes no removable project lines. [Streaming analyzer](kernel_types.py) · [Independent proof export](https://math.mit.edu/~drew/shortgrh/)

The source-level cross-check recognized 7,081 explicitly named public theorems and lemmas. Fifty-five occur in a duplicate-type group. Among earlier public declarations visible through the same module or its imports, the only pair the search found was `LFunction_ne_zero_of_half_lt_re` and `New.grh`. The direct-endpoint revision already removes that alias. The check compares exact exported type nodes and universe parameters. It does not explore definitional transformations or alternative proof strategies. [Source comparison](source_aliases.py) · [Measured result](source-aliases.json)

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

The statements, public endpoints and proof-specific `New` directory already fit in **24,841 code lines** or **34,943 physical lines** across 221 modules. Their project-owned `Lib` dependency contributes another **51,231 code lines** and **77,827 physical lines** across 573 modules. Together they account for the complete 76,072 code lines. A reader can start with the proof-specific layer while a full source-budget calculation includes both layers. [Directory counts](combined-metrics.json) · [Proof-specific source](https://github.com/DomTheDeveloper/LeanReducer/tree/41bbac1c78e806eced8fd373f6cb55e77a045af5/src/New)

On the combined revision, removing the import path through `New.Endgame.LongForms` removes **58,867 code lines** used exclusively on that path and leaves **17,205**. A new proof and its additional local imports could use at most **32,795 code lines** to finish under the inclusive 50,000-line limit. Using physical lines leaves 28,261 and a replacement budget of 21,739. These are budgets for a replacement that still proves all five endpoints. The module itself uses the upper covolume bound, enough independent forms and the lower bound for integral forms. A shorter derivation of the weighted prime estimate could bypass that comparison. [Exact import cut](combined-metrics.json) · [Upstream proof guide](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/GUIDE.md)

### Keeping the final covolume comparison

There are 791 possible module cuts after setting aside the entry `Main`, its immediate proof `New.Main`, and the covolume comparison `New.Endgame.LongForms`. Across **all 312,445 unordered pairs** of these modules, the smallest surviving source contains **53,195 code lines**. The best pair is `Lib.GaloisRep.Main.AvatarCompatibility` and `New.Selmer.FitTwistsExist`. Even a free replacement for that pair would exceed 50,000 by 3,195. This lower bound applies to this import-graph operation on this revision.

Three specific modules release enough code while retaining all three top-level modules. These are `New.Endgame.ShortAndEnough`, `New.Selmer.FitTwistsExist`, and `New.Rows.LiftVolumeHeight`. Among the retained modules, only `New.Endgame.LongForms` directly imports any of the three. Their roles are to construct enough short forms with the needed heights and indices, construct a family of twists satisfying the congruences, and bound the heights of lift-volume ratios. The replacement also needs every declaration their imports make available to the retained source and that source still uses.

| Graph operation | Code removed | Code retained | Code available for a replacement under 50,000 |
| --- | ---: | ---: | ---: |
| Best eligible pair | 22,877 | 53,195 | Already 3,195 over |
| Three named modules together | 38,183 | 37,889 | 12,111 |
| Whole covolume comparison | 58,867 | 17,205 | 32,795 |

Of the 38,183 lines, **30,576** survive each individual cut. Within that group, **25,457** survive every pair of the three and disappear only when all three are replaced. A second exhaustive computation directly traversed the full graph for each of the 312,445 candidate pairs and reproduced the 53,195-line minimum. The three-module cut leaves 59,618 physical lines, so the 12,111-line allowance applies to the code-line metric. [Machine-readable measurements](joint-cuts.json)

```sh
python3 -m leanreducer analyze /path/to/GRH-76072/src --entry Main --pair-audit \
  --exclude-from-pairs New.Main --exclude-from-pairs New.Endgame.LongForms \
  --cut New.Endgame.ShortAndEnough --cut New.Selmer.FitTwistsExist --cut New.Rows.LiftVolumeHeight
```

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

Holding these 976 lines fixed leaves **49,024 code lines** for the additional arithmetic proof and project-owned dependencies under 50,000, or **24** under 1,000. Proving every level good by the existing covolume argument supplies an unbounded set by taking $k=L$. Those original dependencies count toward the budget. [Standalone source](https://github.com/DomTheDeveloper/LeanReducer/tree/ae21d67f172b180b660d9bfa2183e3f806ab0ef2) · [Download ZIP](https://github.com/DomTheDeveloper/LeanReducer/archive/ae21d67f172b180b660d9bfa2183e3f806ab0ef2.zip) · [Clean build and kernel replay](https://github.com/DomTheDeveloper/LeanReducer/actions/runs/45989759982) · [Source changes against the 985-line edition](https://github.com/DomTheDeveloper/LeanReducer/compare/680cdffe8dca5e2f3de405a615318d0989f0f055...ae21d67f172b180b660d9bfa2183e3f806ab0ef2)

The generic LeanReducer checker also audited the exact pinned project against a second test that expands all arithmetic quantifiers and the five conclusion types. It reproduced the source and closure counts, confirmed the three axioms, and published its verification record. [Expanded contract](cofinal-case.json) · [Audited run and verification record](https://github.com/DomTheDeveloper/LeanReducer/actions/runs/45991669828)

## A divergent family of primes in 1,000 physical Lean lines

At arbitrarily large natural levels $k$, let $M = 18480(k+1)!$. It suffices to find a set of primes $S$ with the following three properties.

1. Every $d$ in $S$ is congruent to 7 modulo 8 and is coprime to $M$.
2. The sum of $\log(d)/d$ over $S$ diverges.
3. For each $d$ in $S$, the actual weighted prime error at $n^4$ is eventually at most $(n^4)^{-1/2+1/(4(k+1))}$. The threshold may depend on $d$ and $k$.

The zero-density estimate for exceptional quadratic twists implies that such a family contains a suitable twist at every fixed height. Fourth-power interpolation supplies the real-variable estimate, and the factorial levels recover every conductor. The checked compatibility theorem derives the divergence condition for any unit residue class from Dirichlet's theorem. This explains why a complete progression as in the 976-line proof is sufficient, and why an arbitrary infinite set of primes would require a further argument. [Exact arithmetic premise and five conclusions](https://github.com/DomTheDeveloper/LeanReducer/blob/b95fc6679ddb55033c7d11a62bfbb832b7f1812b/src/SampledGRH.lean) · [Zero-density argument](https://github.com/DomTheDeveloper/LeanReducer/blob/b95fc6679ddb55033c7d11a62bfbb832b7f1812b/src/Lib/Analytic/QuadraticTwist/ZeroFreeTwist.lean) · [Compatibility proof](https://github.com/DomTheDeveloper/LeanReducer/blob/b95fc6679ddb55033c7d11a62bfbb832b7f1812b/verification/MassFromClass.lean)

| Source | Modules | Code lines in the project | Physical lines in the project | Physical lines including the test |
| --- | ---: | ---: | ---: | ---: |
| Annotated | 18 | 957 | 1,312 | 1,330 |
| Standalone comments moved to Markdown | 18 | 957 | **982** | **1,000** |

Every code-containing line of all 18 published project modules matched between the two editions. The four definitions in `Statements.lean` also match the original compact file byte for byte. The remaining 18 physical lines are the compatibility test. Explanatory comments are available by source file and original line number. Lean 4.35 compiled the 982-line project, checked its expanded premise and the five conclusions with only `propext`, `Classical.choice` and `Quot.sound`, checked the compatibility theorem, and replayed all 18 project modules. [Complete 1,000-physical-line ZIP](https://github.com/DomTheDeveloper/LeanReducer/archive/b95fc6679ddb55033c7d11a62bfbb832b7f1812b.zip) · [Annotated edition](https://github.com/DomTheDeveloper/LeanReducer/tree/9419fe0c6392dc1eee7ae6e7f98007fccd6fdd82) · [Annotated proof verification](https://github.com/DomTheDeveloper/LeanReducer/actions/runs/45994390418) · [Module notes](https://github.com/DomTheDeveloper/LeanReducer/blob/b95fc6679ddb55033c7d11a62bfbb832b7f1812b/SOURCE-NOTES.md) · [Documentation transformation](compact_notes.py) · [Build, axiom check and replay](https://github.com/DomTheDeveloper/LeanReducer/actions/runs/45994424273)

The missing unconditional step is a short derivation of the sampled bound on a divergent admissible family at unbounded levels. Keeping the present proof uses 957 project code lines and leaves **49,043** further code lines for this step and its dependencies at 50,000, or **43** at 1,000. With source and documentation arranged as in the 982-physical-line project, the corresponding physical-line allowances are **49,018** and **18** before the independent compatibility test. The existing full source obtains the bound through the covolume comparison. [Frozen reducer contract](divergent-case.json)

### A 950-code-line formulation

The selected set may contain any natural numbers if the mass and the bounds both quantify only over its primes. Intersecting the set with the primes gives the equivalent prime-only formulation above. This removes the separate assertion that every set member is prime. The proof selects a nonexceptional quadratic twist directly from the divergent prime family. The complete source counts **950 code lines in 18 modules**, with **1,304 physical lines** in the annotated edition and **975 physical lines** when standalone comments move to Markdown. All code-containing lines match between these editions, and the challenge statement file is byte-identical. The 950-line annotated project passed a fresh Lean 4.35 build, an axiom audit and native replay of all 18 modules. [Annotated source and completed checks](https://github.com/DomTheDeveloper/LeanReducer/actions/runs/45994270811) · [Compact project ZIP](https://github.com/DomTheDeveloper/LeanReducer/archive/39d23a7d38d6d53c3618646c8831cd91fd8295eb.zip) · [Exact arithmetic contract](prime-weight-case.json)

The 975-physical-line edition also passed a fresh build, an audit of the summand with all quantifiers expanded, and native kernel replay of all 18 modules. An independent LeanReducer run reproduced both counts. Its separate theorem `OldToDivergent.old_level_implies_divergent` verifies that the older all-primes-in-a-residue-class condition supplies the divergent family, including the coprimality and fourth-power estimates. The downloaded ZIP contained 18 Lean files, with SHA-256 `a165ecaeb97d116f1767b737d2b40b0dd70c53bf732d7c17482651175899647f`. [Compact build and kernel replay](https://github.com/DomTheDeveloper/LeanReducer/actions/runs/45995433632) · [Independent checker and compatibility proof](https://github.com/DomTheDeveloper/LeanReducer/actions/runs/45996229428) · [Machine-readable verification](https://github.com/DomTheDeveloper/LeanReducer/actions/runs/45996229428/artifacts/15196132461)

Keeping this analytic proof leaves **49,050** additional code lines to reach 50,000 and **50** to reach 1,000. Counting every physical line in the compact edition instead gives **49,025** and **25**, respectively. The added lines must establish the displayed prime-error estimates on a divergent admissible family for arbitrarily large levels.

## Choosing the auxiliary modulus freely in 920 code lines

Fix a positive conductor $q$ and an accuracy $\varepsilon>0$. It suffices to find a positive multiple $M$ of $q$, an exponent $0<\delta\leq\min(1,\varepsilon)$, and a set $S$ for which the following conditions hold.

- The sum $\sum_{p\in S,\ p\text{ prime}}\log(p)/p$ diverges.
- Every prime $d\in S$ is congruent to 7 modulo 8 and coprime to $M$.
- For each such $d$ and every sufficiently large natural $n$, the upstream weighted error satisfies $R_{d,M}(n^4)\leq(n^4)^{-1/2+\delta/4}$. The threshold may depend on the chosen prime and modulus.

The choice of modulus and exponent may depend on both $q$ and $\varepsilon$. Given a possible zero with real part strictly above one half, choose the accuracy inside that real margin. The one-sided estimate excludes the zero for the character lifted to $M$. The Euler factors in the change-of-level formula transfer nonvanishing back to $q$. This replaces the factorial-level module with a direct argument and allows other choices of auxiliary moduli. [Statement and proof](https://github.com/DomTheDeveloper/LeanReducer/blob/440ee79d9a051dedbd983495a6557ef4bcca4c68/src/SampledGRH.lean)

| Version | Project code | Project physical | All checked-in Lean physical |
| --- | ---: | ---: | ---: |
| Free auxiliary moduli and an explicitly prime set | 927 | 951 | 987 |
| Free auxiliary moduli and a sum restricted to primes | **920** | **944** | **990** |

The second edition has 17 project modules and one separate, 46-line verification file. Three compatibility proofs cover unit residue classes, restricting a set to its primes, and extracting the new choices of modulus and accuracy from the earlier factorial hypothesis. Lean 4.35 built the project and replayed every local module. Its public implication uses only `propext`, `Classical.choice` and `Quot.sound`. An independently written LeanReducer contract expands all arithmetic quantifiers and the prime-mass summand before checking the theorem type. [Complete 920-code-line ZIP](https://github.com/DomTheDeveloper/LeanReducer/archive/440ee79d9a051dedbd983495a6557ef4bcca4c68.zip) · [Build, axioms and module replays](https://github.com/DomTheDeveloper/LeanReducer/actions/runs/45997603687) · [Compatibility proofs](https://github.com/DomTheDeveloper/LeanReducer/blob/440ee79d9a051dedbd983495a6557ef4bcca4c68/verification/MassFromClass.lean) · [Expanded contract](multiples-case.json) · [Reducer audit](https://github.com/DomTheDeveloper/LeanReducer/actions/runs/45997641927) · [927-line verification](https://github.com/DomTheDeveloper/LeanReducer/actions/runs/45995890365)

Keeping this analytic proof leaves **49,080 code lines** for an unconditional derivation of the arithmetic estimates and its dependencies under the 50,000-code-line target, or **80** under 1,000. The physical source budgets are **49,056** and **56**. Counting the independent test file as well leaves ten physical lines under 1,000. The existing covolume proof establishes sufficient estimates with a much larger dependency closure.

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
