# Notes from the conditional Lean source

Sections give the original source locations. Executable lines and inline comments stay in the Lean files.

## src/FactorialLevels.lean

Original lines 9–9

```lean
/-- The nonvanishing statement at a single positive modulus. -/
```

Original lines 19–19

```lean
/-- Any unbounded set of good factorial levels suffices, regardless of its gaps. -/
```

## src/FourthPowers.lean

Original lines 12–12

```lean
/-- Endpoints of a fourth-power interval have a gap of at most 15 n³ once n ≥ 1. -/
```

Original lines 17–18

```lean
/-- Quadratic reciprocal interpolation transfers fourth-power bounds to all large real inputs.
The small loss from a to b absorbs fixed constants. -/
```

## src/Lib/Analytic/DirichletTheta/MellinTheta.lean

Original lines 3–8

```lean
/-! Known result: the transformation formula and the Mellin transform of the theta series of a
Dirichlet character. The transformation is proved only in absolute value, so no root number appears,
first for any non-principal character against its finite Fourier transform and then for a primitive
character against itself. The Mellin formula holds for any bounded coefficients to the right of 1
and for such characters to the right of 0. Source: Davenport, Multiplicative Number Theory;
Montgomery–Vaughan ch. 10.
```

Original lines 10–11

```lean
This file: Gaussian theta series of a character: Poisson symmetry, Mellin transform is Gamma times
L. -/
```

Original lines 15–15

```lean
/-- The function g(x) = x^j e^{−πx²} of a real variable x. -/
```

Original lines 18–18

```lean
/-- The theta series ∑_{n ≥ 1} c(n) g(nt) with coefficients c, where g(x) = x^j e^{−πx²}. -/
```

Original lines 21–22

```lean
/-- The integral ∫_r^∞ |θ(t)| dt/√t, where θ(t) = ∑_{n ≥ 1} c(n) g(nt), g(x) = x^j e^{−πx²}, is
the theta series `gaussianTheta` j c. -/
```

Original lines 25–26

```lean
/-- The gamma factor Γ_j(s) = ∫_0^∞ g(t) t^{s−1} dt, the Mellin transform of g(t) = t^j
e^{−πt²}. -/
```

Original lines 31–32

```lean
/-- If f is measurable and |f(t)| ≤ D e^{−t} for t > 0, then its Mellin transform is holomorphic
in Re s > 0 and bounded on the strip 1/2 ≤ Re s ≤ 2. -/
```

Original lines 50–51

```lean
/-- The trivial bound: for j ∈ {0, 1}, |c(n)| ≤ 1 and t > 0, the series ∑_{n ≥ 1} c(n) g(nt),
g(x) = x^j e^{−πx²}, converges absolutely and has modulus at most 3e^{−t}/t. -/
```

Original lines 61–61

```lean
/-- For Re s > 0, Γ_j(s) = ½ π^{−(s+j)/2} Γ((s+j)/2). -/
```

Original lines 67–68

```lean
/-- Riemann's formula: if |c| ≤ 1 and Re s > 1, the Mellin transform at s of t ↦ ∑_{n ≥ 1} c(n)
g(nt), g = `gaussianMonomial` j, is Γ_j(s) ∑_{n ≥ 1} c(n) n^{−s}. -/
```

Original lines 81–82

```lean
/-- If Φ on ℤ/q satisfies Φ(−x) = (−1)^j Φ(x) and Φ(0) = 0, and ∑_{n ∈ ℤ} Φ(n) g(nt) converges
to S, g = `gaussianMonomial` j, then S = 2 ∑_{n ≥ 1} Φ(n) g(nt). -/
```

Original lines 88–89

```lean
/-- Poisson summation for g = `gaussianMonomial` j, j ≤ 1: for real a and t > 0, ∑_{n ∈ ℤ} g((n +
a)t) converges to some S, and ∑_{n ∈ ℤ} e^{2πian} g(n/t) converges to i^j t S. -/
```

Original lines 103–104

```lean
/-- For j ≤ 1, |Γ_j| has a positive lower bound on every compact subset of the half-plane Re s >
0. -/
```

Original lines 114–115

```lean
/-- For j ≤ 1, non-principal χ mod q with χ(−1) = (−1)^j and t > 0: t |θ_χ(t)| = |θ_φ(1/(qt))|,
where θ_c = `gaussianTheta` j c and φ(n) = q⁻¹ ∑_a χ(a) e^{2πian/q}.
```

Original lines 117–117

```lean
Known result: Theta series of a Dirichlet character: transformation formula and Mellin transform. -/
```

Original lines 135–136

```lean
/-- Theta functional equation in absolute value: for j ≤ 1, primitive non-principal χ mod q with
χ(−1) = (−1)^j and t > 0, √q t |θ(t)| = |θ(1/(qt))|, where θ = `gaussianTheta` j χ.
```

Original lines 138–138

```lean
Known result: Theta series of a Dirichlet character: transformation formula and Mellin transform. -/
```

Original lines 145–146

```lean
/-- For a non-principal character χ mod q with χ(−1) = (−1)^j, j ∈ {0, 1}, and t > 0: |∑_{n ≥ 1}
χ(n) g(nt)| ≤ 3q·e^{1−t}, where g(x) = x^j e^{−πx²}. -/
```

Original lines 156–157

```lean
/-- For j ≤ 1 and non-principal χ with χ(−1) = (−1)^j, the Mellin transform of t ↦ ∑_{n ≥ 1}
χ(n) g(nt), g = `gaussianMonomial` j, equals Γ_j(s) L(s, χ) for Re s > 0. -/
```

Original lines 166–167

```lean
/-- For j ≤ 1, primitive non-principal χ mod q with χ(−1) = (−1)^j, T > 0 and q ≤ T²: ∫_0^∞
|θ(t)| dt/√t ≤ 2 ∫_{1/T}^∞ |θ(t)| dt/√t, where θ = `gaussianTheta` j χ. -/
```

## src/Lib/Analytic/Landau/PolarLandau.lean

Original lines 1–1

```lean
-- Modified by LeanReducer to retain only the conditional analytic argument.
```

Original lines 4–7

```lean
/-! Known result: Landau's lemma on Dirichlet integrals of one sign. The form here allows real
simple poles of non-negative residue. It concludes that no pole lies right of the exponent of the
one-sided bound. Source: Montgomery and Vaughan, Multiplicative Number Theory I, 2007, Lemma 15.1
(Widder, The Laplace Transform, 1941, II Thm 5b).
```

Original lines 9–11

```lean
This file: Landau's lemma for one-sided bounds; Laplace transforms of
powers; logarithmic derivatives of
L-functions. -/
```

Original lines 19–20

```lean
/-- For a Dirichlet character χ mod N, a prime d and every integer n, the character `quadTwist` χ d
mod Nd takes at n the value χ(n)·(n/d), where (n/d) is the Legendre symbol. -/
```

Original lines 25–26

```lean
/-- For a Dirichlet character χ mod N and an odd prime d coprime to N, the twist of χ by the
Legendre symbol (·/d), a character mod Nd, is not principal. -/
```

Original lines 32–34

```lean
/-- E is measurable, O(e^v) on v ≥ 0; ∫₀^∞ E(v)e^{(1−s)v} dv continues from re s > 2 to a
meromorphic Φ with (s − 1)Φ(s) analytic on re s ≥ 1 and at most simple poles, of residue r(ρ), in re
ρ > 0. As (s − 1)Φ(s) takes the value 0 at s = 1, this allows no pole of Φ at 1. -/
```

Original lines 46–47

```lean
/-- Laplace transform of a power: for complex s with re s > 0 and every natural number k, ∫₀^∞
t^k e^{−st} dt = k!/s^{k+1}. -/
```

Original lines 76–78

```lean
/-- Removable singularity: if s ↦ (s − a)Ψ(s), with value 0 at a, is analytic on the disc of
radius ε about z, a ≠ z, and a, σ lie in that disc, then the Taylor series of Ψ at z
converges at σ. -/
```

Original lines 85–86

```lean
/-- Landau's lemma. Let E satisfy `IsPolar` with residues r, and let β > 0. If re r(x) ≥ 0 for
all real x > β and E(v) ≤ e^{(β−1)v} for large v, then r(ρ) = 0 whenever re ρ > β.
```

Original lines 88–88

```lean
Known result: Landau's lemma on Dirichlet integrals of one sign. -/
```

## src/Lib/Analytic/PolyaVinogradov/PolyaVinogradov.lean

Original lines 3–7

```lean
/-! Known result: the Pólya–Vinogradov inequality for sums of a non-principal Dirichlet character.
It is proved here for initial intervals only, with the explicit bound 2√q(1+log q) for any
non-principal character. The bound is obtained by sieving the inducing primitive character over
divisors. Source: Pólya 1918, Vinogradov 1918; Davenport, Multiplicative Number Theory;
Montgomery–Vaughan Thm 9.18.
```

Original lines 9–10

```lean
This file: Pólya–Vinogradov inequality for non-principal characters; modulus of primitive Gauss
sums. -/
```

Original lines 20–20

```lean
/-- The Gauss sum of a primitive character mod q has absolute value √q. -/
```

Original lines 26–27

```lean
/-- Pólya–Vinogradov inequality for a non-principal character χ mod q: |∑_{1 ≤ v ≤ X} χ(v)| ≤
2√q (1 + log q) for all X.
```

Original lines 29–29

```lean
Known result: Pólya–Vinogradov inequality for sums of a non-principal Dirichlet character. -/
```

Original lines 42–42

```lean
  -- of two complementary divisors one is at most `√r`
```

Original lines 44–44

```lean
  -- the primitive character: its sums are at most `√M (1 + log M)`
```

Original lines 54–54

```lean
  -- a geometric sum is at most `1 / sin (π x)`, `x = k / M`, and `sin (π x) ≥ 2 x (1 - x)`
```

## src/Lib/Analytic/Primes/AuxiliaryPrimes.lean

Original lines 4–7

```lean
/-! Known result: A prime in a long window (weak form of the Siegel-Walfisz theorem). From a small
zero-free disc at 1, this file only finds one prime congruent to 1 modulo a power of a fixed
multiple of 4, with its logarithm in a long window. It gives no asymptotic count. Source: Montgomery
and Vaughan, Multiplicative Number Theory I, 2007, Cor. 11.19.
```

Original lines 9–9

```lean
This file: A prime 1 modulo M^k with logarithm in a long window; zero-free disc. -/
```

Original lines 15–16

```lean
/-- For 0 < r < 1/9 there is C ≥ 0 with |L(s, χ)| ≤ C q^(2r) on the disc |s − 1| ≤ r, for every
modulus q and every non-principal character χ mod q. -/
```

Original lines 33–35

```lean
/-- Let M > 0 be a multiple of 4 and A natural. For small η > 0, all k ≥ 2 with M^k ≤ η^{−A},
all characters χ mod M^k and |s − 1| ≤ η, one has η|L̃′(s, χ)| < |L̃(s, χ)|, where L̃ is
`entireL`. -/
```

Original lines 65–66

```lean
/-- Let M > 0 be a multiple of 4 and A natural. For large W, all k ≥ 2 with M^k ≤ W^A and all U in
[W, W^A], there is a prime p ≡ 1 mod M^k with U ≤ log p ≤ U + W.
```

Original lines 68–68

```lean
Known result: A prime in a long window (weak form of the Siegel-Walfisz theorem). -/
```

## src/Lib/Analytic/QuadraticTwist/ZeroFreeTwist.lean

Original lines 1–1

```lean
-- Modified by LeanReducer to select twists from a set of primes of divergent weight.
```

Original lines 4–8

```lean
/-! Known result: Zero density for quadratic twists by mean values over real characters. This file
only finds one prime in a given class whose quadratic twists have no zero up to a given height right
of a line beyond the critical line. The proof uses a three-lines argument and a smoothed mean square
of Jacobi symbol sums. Source: Jutila, On mean values of Dirichlet polynomials with real characters,
Acta Arith. 27 (1975) 191-198.
```

Original lines 10–10

```lean
This file: Some prime in a class has quadratic twists zero-free on a half-strip; three lines. -/
```

Original lines 23–25

```lean
/-- Three lines: for j ≤ 1, some C gives |Γ_j(s)|² ≤ C T^(−2η) whenever χ ≠ 1 is primitive mod q
≤ T² of parity j, L(s, χ) = 0, 1/2 + 9η ≤ re s ≤ 1, and the integrals `thetaTailIntegral` from 1/T
of the theta series of χ and μχ total at most T^(2η). -/
```

Original lines 35–35

```lean
  -- `mellin f` is the Mellin transform of `f`, the series for `χ μ` cut at `1 / T`; `B` bounds it
```

Original lines 50–50

```lean
  -- on `re z = 1/2`: bound `mellin f` and `Γ_j L` by tail integrals; then use `J`
```

Original lines 57–57

```lean
  -- on `re z = 2`: `Γ_j² - Γ_j L · mellin f = Γ_j L ∫_0^{1/T} θ^μ(t) t ^ z dt / t`
```

Original lines 72–73

```lean
/-- If m ≥ 1 and neither m nor 2m is a square, then |∑_{1 ≤ v ≤ X} (−v/m)| ≤ 2√m (1 + log m) for
all X; the factor at 2 of the Jacobi symbol is the principal character. -/
```

Original lines 90–91

```lean
/-- Mean value estimate. For j ≤ 1, η > 0, t ≥ 1/T > 0, X ≤ T² and |c| ≤ 1: ∑_{1 ≤ v ≤ X} |∑_{n
≥ 1} c(n) (−v/n) g(nt)|² ≤ C T² t^{−1−2η}, with g = `gaussianMonomial` j and C = C(j, η). -/
```

Original lines 103–103

```lean
  -- the majorant: a sum over the triples `(a, b, u)` with `k n = a b²`, `m = a u²`, and a product
```

Original lines 109–109

```lean
  -- expand the square
```

Original lines 116–116

```lean
  -- if `k n m` is a square, `k = 1` or `2`, the trivial bound; else Pólya–Vinogradov
```

Original lines 130–131

```lean
/-- For j ≤ 1, η > 0, T > 0, X ≤ T² and |c| ≤ 1: ∑_{1 ≤ v ≤ X} ∫_{1/T}^∞ |∑_{n ≥ 1} c(n) (−v/n)
g(nt)| dt/√t ≤ C T^{2+η}, with g = `gaussianMonomial` j and C = C(j, η). -/
```

Original lines 143–145

```lean
/-- Zero-density bound for quadratic twists: for ξ mod N, η > 0 and real y, only O(x^{1−η/2})
primes d ≤ x, d ≡ 7 mod 8, d ∤ N, have a zero of L(s, ξ·(·/d)) with Re s ≥ 1/2 + 9η, |Im s|
≤ y.
```

Original lines 147–147

```lean
Known result: Zero density for quadratic twists by mean values over real characters. -/
```

Original lines 175–175

```lean
  -- reciprocity and `(2/d) = 1` give `(n/d) = (-d/n)`
```

Original lines 182–182

```lean
  -- the twist of a primitive character by the Legendre symbol of a new prime is primitive
```

Original lines 192–192

```lean
/-- The sum of log(p)/p over the primes in S diverges. -/
```

Original lines 196–196

```lean
/-- Some prime in S has all twisted L-functions nonvanishing on the specified box. -/
```

## src/Lib/General/Algebra/SumOverUnits.lean

Original lines 1–1

```lean
-- Modified by LeanReducer to retain only the conditional analytic argument.
```

Original lines 4–4

```lean
/-! General lemmas of commutative and general algebra (textbook or folklore).
```

Original lines 6–6

```lean
This file: Sum over Z/N, N prime, splits as zero term plus sum over units. -/
```

## src/Lib/General/LinearAlgebra/Base.lean

Original lines 1–1

```lean
-- Modified by LeanReducer to retain only the conditional analytic argument.
```

Original lines 12–14

```lean
-- Equality is classical: every proposition is decidable (by choice), and the instances that compute
-- equality on the types used as index sets rank below, so that each index set has one instance.
-- `open Calc` brings eight of these computing instances back.
```

Original lines 25–25

```lean
-- erases these simp lemmas for every importer; the lemmas are only named in order to be erased
```

Original lines 50–50

```lean
-- directions of library equivalences, for dot notation; the adjoint of a matrix
```

## src/Lib/General/NumberTheory/QuadField.lean

Original lines 1–1

```lean
-- Modified by LeanReducer to retain only the conditional analytic argument.
```

Original lines 13–14

```lean
/-- The Legendre symbol (·/d) as an integer-valued Dirichlet character modulo the prime d; for d
≡ 3 mod 4 it is the character χ_K of K = ℚ(√−d). -/
```

Original lines 19–20

```lean
/-- For a Dirichlet character χ mod N and a prime d, the character mod Nd that is the product of
χ and the Legendre symbol (·/d). -/
```

Original lines 24–25

```lean
/-- The entire function equal to L(s, χ) if χ is not principal, and to the continuation of (s −
1)L(s, χ) if χ is principal. -/
```

## src/Lib/General/NumberTheory/ZeroSymmetry.lean

Original lines 3–3

```lean
/-! General lemmas of algebraic number theory (textbook or folklore).
```

Original lines 5–6

```lean
This file: Symmetry of zeros of Dirichlet L-functions from the functional equation, imprimitive
characters included. -/
```

Original lines 12–13

```lean
/-- For a Dirichlet character χ, a natural number M and Re s ≠ 0, the product of the Euler
factors 1 − χ(p)p^{−s} over the primes p dividing M is not zero. -/
```

Original lines 19–20

```lean
/-- Every complex Dirichlet character χ mod N, with N ≥ 1, is induced by a primitive character ψ
mod M for some divisor M ≥ 1 of N. -/
```

Original lines 25–26

```lean
/-- Symmetry of the zeros: if L(s, χ) = 0, re s ≠ 0 and s ≠ 1, then either s is a pole of the
gamma factor of χ (where Mathlib gives it the value 0), or L(1 − s, χ⁻¹) = 0. -/
```

## src/New/Endgame/OneSidedCriterion.lean

Original lines 1–1

```lean
-- Modified by LeanReducer to retain only the conditional analytic argument.
```

Original lines 5–10

```lean
/-! A good second scale in every long window. If E and E' are O(e^v) and their transforms
∫E(v)e^((1−s)v)dv continue with no pole in Re s ≥ 1, then for large t and any X in [0, e^t] some u
in [t, t²] has E(u) − X E'(u) ≤ e^(−t), which replaces a pointwise prime number theorem in
progressions when the second scale of (⋆) is chosen. Localised one-sided bounds and sign changes for
prime-sum errors are known. Related work: Pintz, On the sign changes of π(x) − li(x), 1976–78;
Kaczorowski, On sign-changes in the remainder-term of the prime-number formula, 1984.
```

Original lines 12–18

```lean
One-sided bound for non-split primes gives a zero-free half-plane. If β > 1/2 and, for every prime d
of a unit class mod M forcing d ≡ 7 mod 8, the normalised error at x in the weighted count of
primes ≡ 1 mod M not split in Q(√−d) is eventually ≤ x^(β−1), then L(s,χ) has no zero in Re s > β
for χ mod M, and this takes (⋆) to GRH. It is known that a one-sided bound for a weighted sum over
primes 1 mod q gives a zero-free half-plane if there are no real zeros. Related work: M. Suzuki, On
variants of Chebyshev's conjecture, arXiv 2411.07436, 2024; Montgomery–Vaughan, Multiplicative
Number Theory I, §15.1–15.2, 2007; Landau, Über einen Satz von Tschebyschef, 1905.
```

Original lines 20–20

```lean
This file: One-sided bound gives a zero-free half-plane; small value in every long window. -/
```

Original lines 24–24

```lean
/-- Prime-error bounds on a set of auxiliary primes of divergent weight imply nonvanishing. -/
```

## src/New/Endgame/PrimeError.lean

Original lines 1–1

```lean
-- Modified by LeanReducer to retain only the conditional analytic argument.
```

Original lines 4–9

```lean
/-! The remainder `primeError` written as an exact finite prime sum. For an integer a and 0 < z ≤ a,
the normalised error at z in the class 1 mod M equals the sum over ν ≤ a, ν ≡ 1, of
Λ(ν)(1−χ_K(ν))(a/ν − a/z)₊, divided by a, less log z/φ(M) and a constant. This standard rewriting of
a weighted prime sum in a residue class as an exact finite identity turns the divisibility sums
∑ λ(ν)(a/ν − a/z)₊ over ν ≤ a into `primeError` at a single z ≤ a. Related work: Davenport,
Multiplicative Number Theory.
```

Original lines 11–12

```lean
Part of: One-sided bound for non-split primes gives a zero-free half-plane (see
New.Endgame.OneSidedCriterion).
```

Original lines 14–15

```lean
This file: Weighted non-split prime sums; their Mellin transform has poles at zeros of
L-functions. -/
```

Original lines 24–25

```lean
/-- The weight λ(ν) = Λ(ν)(1 − (ν/d)) for ν ≡ 1 mod M, and 0 otherwise; Λ is von Mangoldt's
function and (ν/d) the Legendre symbol. -/
```

Original lines 28–29

```lean
/-- The sum y^{−r} ∑_{1≤ν≤y} λ(ν) ν^{r−1}, with λ = `lambdaClass`: for r = 0 it is ∑ λ(ν)/ν, for r
= 1 it is y⁻¹ ∑ λ(ν). -/
```

Original lines 32–33

```lean
/-- The function φ(M)⁻¹(∑_ξ (L̃′/L̃(s, ξ·(·/d)) − L̃′/L̃(s, ξ)) − 1), summed over the characters
ξ mod M, where L̃ is `entireL`. -/
```

Original lines 37–38

```lean
/-- The remainder R_M(x) = ∑_{ν≤x} λ(ν)(1/ν − 1/x) − log x/φ(M) − Re `logDerivMean`(1), where λ(ν)
= Λ(ν)(1 − (ν/d)) for ν ≡ 1 mod M, else 0. -/
```

Original lines 53–54

```lean
/-- For 0 < z ≤ A, `primeError d M z` in terms of the sum ∑_{ν ≤ A} λ(ν)(A/ν − A/z)⁺, where λ is
`lambdaClass d M`. -/
```

Original lines 61–63

```lean
/-- For d ≡ 7 mod 8 prime to M, v ↦ R_M(e^v) is polar (`IsPolar`) with residue at s equal to
∑_ξ (ord_s L̃(ξ) − ord_s L̃(ξ(·/d))) / (φ(M) s(1 − s)), ξ over the characters mod M, L̃ =
`entireL`. -/
```

Original lines 72–72

```lean
  -- real on `(2, ∞)`, hence at `1`
```

## src/PrimeErrorFourthPowers.lean

Original lines 8–8

```lean
/-- The actual upstream prime error satisfies quadratic reciprocal interpolation. -/
```

## src/ReciprocalInterpolation.lean

Original lines 14–15

```lean
/-- A single cutoff contains all terms needed at the two endpoints and the interior point.
The weight can include the factor 1/A in the prime-error formula. -/
```

Original lines 20–20

```lean
/-- Interpolation in the variable 1/x. The explicit loss is quadratic in the mesh width. -/
```

## src/SampledGRH.lean

Original lines 11–11

```lean
/-- Only a set of qualifying primes with divergent log(p)/p weight is needed. -/
```

Original lines 18–18

```lean
/-- The good levels can be arbitrarily sparse as long as they are unbounded. -/
```

Original lines 43–44

```lean
/-- The final functional-equation arguments are adapted from Alpöge and Claude,
in Sernau and colleagues' Apache-2.0 compact edition, New/Main.lean. -/
```

## src/WeightedFourthPowers.lean

Original lines 8–8

```lean
/-- A common cutoff and nonnegative weights imply a quadratic interpolation bound. -/
```
