# Reducing the ordinary Riemann hypothesis proof

The shortest verified unconditional entry in this project, `FixedClassRH.ordinaryRH`, went from 76,054 to **76,045** project code lines. Reaching 49,999 still requires a cut of **26,046**. [Unconditional source](https://github.com/DomTheDeveloper/LeanReducer/tree/ffb79990c2f4c584abc37abe4b2709743c86c255) Count every project-owned Lean module imported by the entry, excluding comments and blank lines. Compare the strict limit against 49,999. The compact source descends from Luke Sernau’s rewrite of Levent Alpöge’s proof.

## The smaller geometric estimate

Write $d$ for the row dimension, $n$ for the number of independent rows, and $V$ for the upper bound on the log squared covolume at every conjugate. The index contributes $2\delta$. Write $h$ for the main height, $L=(\log b)\,\mathrm{budget}$ and $B=10\log(1+b^2)\,\mathrm{budget}$.

The lower bound pays for exactly $d-n$ extra rows. For the existing construction, each added row costs at most

$$
C=x^{99}+x_1^2 b^2+2m^2(2t x^{999}).
$$

Lean proves $d(h-2L)\le V+2\delta+(d-n)C$. It follows that $d(h-3L)\le V+2\delta$ whenever $(d-n)x_1^2 b\le d$. The previous bound on the missing fraction was $4/b^2$. The admissible scales imply $4x_1^2\le b$, so the previous assumption supplies the new one. [CompletionHeight.lean](src/CompletionHeight.lean)

There is also a way to use a smaller family. The height comparison on admissible data with enough thick places gives $h\ge3L+B$. For a family with cost $c$ per missing dimension, every positive rank suffices in the final comparison if $c+3L+B\le h$ and the two covolume bounds hold. The estimate for the current completion still contains $x_1^2 b^2$. [HalfRank.lean](src/HalfRank.lean) · [RankFromCovolume.lean](src/RankFromCovolume.lean)

## What would cross 50,000

`FixedClassRH.ofHeightCertificates` consumes a pair of upper bounds on the heights of a nonzero twisted-volume ratio and its inverse square. The product formula cancels the ratio. The estimate at modulus 18,480 then implies Mathlib’s ordinary `RiemannHypothesis`. The hypothesis quantifies over the admissible data at that modulus. A one-dimensional candidate still needs both height bounds on the same ratio. [HeightCriterion.lean](src/HeightCriterion.lean)

The complete covolume argument constructs these certificates on the required data using its actual twist family. The separate `HeightSupply` module checks this compatibility and exposes the full unconditional consequence. [HeightSupply.lean](src/HeightSupply.lean)

`certificate_of_one_volume` treats a single untwisted Gram value and its twisted counterparts. Bounds at every archimedean conjugate and every finite place give the forward height directly. The remaining inverse-square height must concern these same Gram values. [OneVolume.lean](src/OneVolume.lean)

For a construction, first pick a family whose ratios are nonzero at every required twist. Bound its untwisted size and finite-place index. Prove the inverse-square bound on that same family and charge the cost of its missing dimensions in the stated inequality. The per-row argument is especially relevant if the family lies on a single invariant line, where the determinant can be computed on that line. Its inverse-height estimate must be proved on the line itself. A full-space determinant controls a product of changes in length across rows.

The table counts the union of project source imported by each route. Each optional import is added independently to the same criterion.

| Route | Project code lines | Lines available through 49,999 |
| --- | ---: | ---: |
| Height criterion | 17,279 | 32,720 |
| Single-volume local estimates | 17,302 | 32,697 |
| Criterion with the general determinant | 17,381 | 32,618 |
| Criterion with filling moments | 31,821 | 18,178 |
| Criterion with the crude spanning rows | 37,870 | 12,129 |
| Criterion with the full row volume | 56,585 | 6,586 over |
| Criterion with the current short-form construction | 68,367 | 18,368 over |
| Criterion with the current existence theorem for fit twists | 69,210 | 19,211 over |
| Certificates supplied by the full geometric construction | 76,363 | 26,364 over |

The strict budget includes the implementation of every new lemma and its project dependencies. The workflow compiles the proof modules over pinned dependencies, replays them with `leanchecker`, checks the ordinary statement against Mathlib, and prints the declaration axioms and the line counts. [Kernel checks and measurements](https://github.com/DomTheDeveloper/LeanReducer/actions/runs/46059974136)
