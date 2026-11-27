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

The decisive reduction was a mathematical rewrite. The readable edition already reduced the original to 477,124 physical lines. Its library isolates results absent from Mathlib, and its proof-specific part makes the comparison of upper and lower bounds on a covolume explicit. The readable and compact editions differ by a further 364,297 physical lines. In later Astra changes, Mathlib's theorem on integrality of character values replaces an argument through cyclic subgroups, and a prime-ideal count serves two local bounds. The available revisions establish the counts and show these instances. They do not attribute each original line to one transformation. [Earlier study and reproductions](RESULTS.md) · [Astra changes](https://github.com/EllaZhangCA/grh-lean-astra/tree/a57c37471c835968b1932a0f8347978b89ba7ab6)

The shared command saves 38 code lines across 21 uses, counting the new definition. The next patch defines three public results where their underlying arguments are proved and removes three wrapper hops. The public RH result uses the public zeta result directly. The five challenge names and statement types are preserved in the source. The intermediate names `New.grh`, `New.zeros_on_line`, and `New.zeta_zeros_on_line` are retired. Downstream code using those names or the more general conditional helpers needs to adapt. [Ext patch and inverse check](check_ext.py) · [Public theorem changes](public-endpoints.patch) · [Frozen challenge contract](case.json)

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

## What would reach 50,000

On the combined revision, removing the import path through `New.Endgame.LongForms` removes **58,867 code lines** used exclusively on that path and leaves **17,205**. A new proof and its additional local imports could use at most **32,795 code lines** to finish under the inclusive 50,000-line limit. Using physical lines leaves 28,261 and a replacement budget of 21,739. These are budgets for a replacement that still proves all five endpoints. The module itself uses the upper covolume bound, enough independent forms and the lower bound for integral forms. A shorter derivation of the weighted prime estimate could bypass that comparison. [Exact import cut](combined-metrics.json) · [Upstream proof guide](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/GUIDE.md)

## What would reach 1,000

Lean checks a smaller target for the analytic endgame. Write `M(k) = 18480 × (k+1)!`. Nonvanishing for every Dirichlet character of every positive modulus on Re(s) > 1/2, with the principal pole excepted, is equivalent to nonvanishing for every character of modulus `M(k)` only on Re(s) > 1/2 + 1/(k+1), for every natural k. Given q and a point strictly right of 1/2, one factorial multiple is divisible by q and has a small enough margin. The Euler factors in change of level then transfer nonvanishing to q. The file compiles over the proof's pinned Lean 4.35.0 and Mathlib revision with axioms `propext`, `Classical.choice` and `Quot.sound`. [Complete Lean proof](FactorialLevels.lean)

There are two concrete missing pieces on the prime-sum route. First, prove the arithmetic estimate at the selected levels, with enough strength to obtain the specified half-plane for every character there. Fourth-power interpolation gives another possible restriction on where to estimate the prime sum, subject to its hypotheses and their connection to the actual prime error. Second, replace or shorten the current one-sided analytic criterion. Its present closure already costs **1,251 code lines** before adding the arithmetic proof. Neither count is a lower bound on a different proof. [Fourth-power equivalence](WeightedFourthPowers.lean) · [Analytic and arithmetic interfaces](RESULTS.md)

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

Sutherland's independent multi-kernel verification applies to the upstream compact revision at 76,149 code lines. The fork authors report a full build and axiom check of the 76,113-line Astra base. The combined candidate's own full build, endpoint checks and kernel replays have a separate status in the workflow. [Independent upstream checks](https://math.mit.edu/~drew/shortgrh/) · [Candidate workflow status](https://github.com/DomTheDeveloper/LeanReducer/actions/workflows/grh.yml)
