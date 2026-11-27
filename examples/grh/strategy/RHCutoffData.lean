import New.Data.Different
import Lib.Analytic.Primes.AuxiliaryPrimes

/-! Derived from the admissible data and existence proof in the compact edition of
Alpöge's proof. The construction accepts a real cutoff as input. -/

noncomputable section
namespace FixedClassRH.Cutoff
section
open Set NumberField Real

/-- Admissible data: scales x, x₁, b; exponent s and numbers m, r; thick places with a
three-term condition; primes g₀ ≠ g₁ and an integer of K of norm g₀g₁; existence of primes ≡
1 mod M_ω² in short windows. -/
structure AuxiliaryData (P : Parameters) (cutoff : ℝ) where
  /-- `logX = log x`, `logB = log b`, `logX₁ = log x₁`: the sizes are chosen on the logarithmic
  scale. -/
  (logX logB logX₁ : ℝ) (s m r : ℕ) s_le : s ≤ 32 * logX
  thick : Finset _
  g : Fin 2 → ℕ
  piG : 𝓞 P.K
  scale : 1e12 * cutoff ≤ log logB ∧ 100 * log logB ≤ logX ∧ 1e6 * logX ≤ logX₁ ∧ 1e6 * logX₁ ≤ logB ∧
    6 * log logX₁ ≤ log logB
  m_mem : ↑m ∈ Icc (exp (logX / 2)) (2 * exp (logX / 2))
  r_mem : ↑r ∈ Icc (exp (5 * logX)) (3 * exp (5 * logX))
  m_pow : ∃ e, m = 2 ^ (e + 1) ∧ s = (e + 1) * 22
  r_pow : ∃ e, r = 3 ^ (e + 1)
  thick_eq_neg_one_mod {m} (d : m ∣ P.N₁ s) : m ∣ P.N₀ * 3 ^ (.log 3 s + 5) → ∀ σ ∈ thick, P.placeClass d σ = -1
  three_term : let φ := P.placeClass P.two_pow_dvd_N₁; ∀ i j, 0 < i → i < j → j ≤ 324 * s →
         ∀ σ ∈ thick, ∀ τ ∈ thick, ∀ ρ ∈ thick, φ (τ / σ) ^ j = φ (ρ / σ) ^ i → φ (τ / σ) = 1
  g_prime i : (g i).Prime
  g_modEq_one i : g i ≡ 1 [MOD P.N₁ s * P.d]
  dvd_g_sub_one i : P.Mω s ^ 2 ∣ g i - 1
  g_injective : g.Injective
  g_mem i : ↑(g i) ∈ Icc (exp logB ^ 10) (exp logB ^ 11)
  norm_piG : piG * star piG = g 0 * g 1
  exists_prime_window : ∀ U ∈ Icc (100 * logB) (2 ^ s), ∃ p, p.Prime ∧ p ≡ 1 [MOD P.Mω s ^ 2] ∧
    log p ∈ Icc U (U + √logB)

end

open Finset Behrend Real Filter NumberField ClassGroup NeZero QuadField

/-- Behrend: let φ : G → H map commutative groups, L > 0, (LM)ⁿ ≤ ord φ(g). Some finite T ⊆
{cgᵉ} has |T| ≥ Mⁿ/(nM²), and σ, σy, σz ∈ T, φ(y)ʲ = φ(z)ⁱ, 0 < i < j ≤ L force φ(y) = 1.

Known result: Behrend's construction for several equations at once. -/
lemma exists_three_term_free {G H} [CommGroup G] [CommGroup H] (φ : G →* H) c g (n M L : ℕ)
    (hL : 0 < L) (h : (L * M) ^ n ≤ orderOf (φ g)) : ∃ T, (∀ σ ∈ T, ∃ e, σ = c * g ^ e) ∧
    (M ^ n / (n * M ^ 2) : ℝ) ≤ #T ∧ ∀ i j, 0 < i → i < j → j ≤ L → ∀ σ ∈ T, ∀ τ ∈ T, ∀ ρ ∈ T, φ
    (τ / σ) ^ j = φ (ρ / σ) ^ i → φ (τ / σ) = 1 := (exists_large_sphere n M).elim fun k _ ↦ by
  have := pow_injOn_Iio_orderOf.comp map_injOn fun _ k ↦ h.trans' (finFunctionFinEquiv (⟨_, k ·⟩)).2
  use image (c * g ^ map (L * M) ·) (sphere n M k)
  rw [card_image_iff.2 fun _ a _ b _ ↦ this.mono (fun v k ↦ show ∀ i, _ from fun i ↦ ?_)
    a b ?_] <;> simp_all
    [← map_pow, sphere, Behrend.box, -map_apply, ↓forall_mem_image] <;> try nlinarith [k.1 i]
  intro i j _ o _ u hu _ v hv _ w hw _ H
  obtain ⟨a, ha, rfl⟩ := lt_iff_exists_add.1 o
  have e := @this ((i + a) • v) (by simp; nlinarith [hv ·]) (i • w + a • u)
    (by simp; nlinarith [hu ·, hw ‹_›]) (by simpa [pow_add, pow_mul', ↓div_pow,
    div_eq_iff_eq_mul, ← mul_assoc, -map_apply, -nsmul_eq_mul] using H)
  simp [by simpa [← mul_sum, *, ← add_mul, ha.ne', mul_left_comm i] using show
    ∑ l, (i + a) * (a * Int.natAbs (u l - v l) ^ 2 + i * v l ^ 2) =
    ∑ l, i * (i * w l ^ 2 + a * u l ^ 2) by simp [funext_iff] at e; zify at *; grind]

/-- Pigeonhole in the class group: among h + 1 pairs of prime ideals (I_i, J_i) of a number
field of class number h, with every I_i J_i principal, there are i ≠ j with I_i J_j
principal. -/
lemma exists_mul_principal {K} [Field K] [NumberField K] {I J : Fin (classNumber K + 1) → FinPlace
  K} (H : ∀ i, ((I i).1 * (J i).1).IsPrincipal) : ∃ i j, i ≠ j ∧ ((I i).1 * (J j).1).IsPrincipal :=
  let c (v : FinPlace K) := mk0 ⟨_, mem_nonZeroDivisors_of_ne_zero v.3⟩
  have e v w : _ ↔ c v * c w = 1 := by rw [← map_mul, mk0_eq_one_iff]
  by simp_all; grind [Fintype.exists_ne_map_eq_of_card_lt (c ∘ I) (card_fin _).ge]

private theorem chi_at_one (P : Parameters) {s p : ℕ} (h : p ≡ 1 [MOD P.N₁ s * P.d]) :
    chiK P.d p = 1 := by
  simp [CharP.natCast_eq_natCast' _ _ h.of_mul_left]

/-- All auxiliary data exist with an arbitrary fixed lower scale cutoff. -/
theorem exists_auxiliary_data (P : Parameters) (cutoff : ℝ) {ε : ℝ}
    (e0 : 0 < ε / 6) (e1 : ε < 1 / 100) :
    ∀ᶠ x : ℝ in atTop, ∃ D : AuxiliaryData P cutoff,
      D.logX.exp = x ∧ D.logX₁ = x ^ (ε / 6) ∧ (1e6 * log x) ^ 2 ≤ D.logX₁ ∧
      log D.logB = ε * log x ∧ towerDeg D.s / D.logB ≤ #D.thick := by
  have ⟨n, h⟩ := exists_nat_gt (99 * P.N₀ * P.d / (ε / 6) ⊔ 6)
  have E (k : ℕ) := tendsto_exp_mul_div_rpow_atTop k _ e0
  have ev k c := E k (mem_atTop c)
  rw [← map_exp_atTop, eventually_map]
  filter_upwards [E 0 (exists_prime_modEq_one_log_mem (P.N₀ * P.d) n (by grind [Parameters])),
    ev 2 1e12, ev (n + 1)
    ((P.N₀ * 8019 + 2) * 10368 ^ n), mem_atTop 1, ev 0 (2 * classNumber P.K + 1e6), Ioi_mem_atTop 0,
    mem_atTop 2, ev 0 (1e12 * cutoff).exp, ev 1 (8019 * 2 ^ n * n)] with x hg h3 hL lx h5 x0 _ hf hC
  simp_all [↓rpow_natCast, le_div_iff₀, div_lt_iff₀, ← exp_mul, mul_comm x]
  have N (x y : ℝ) (e : 1 ≤ x := by simp; bound) (h : 1 < y := by simp) := exists_nat_pow_near e h
  obtain ⟨⟨h, n0⟩, ⟨o, m1, m2⟩, e, r1, r2⟩ := h, N (x / 2).exp 2, N (5 * x).exp 3
  let s := (o + 1) * 22
  have s8 : s ≤ 32 * x := by simp [s, pow_le_iff_le_log, exp_pos] at *; nlinarith [log_two_gt_d9]
  have W0 := exp_pos (ε / 6 * x)
  have ⟨k, k1, k2⟩ := N (2 ^ s / _) (2 ^ n) ((one_le_div W0).2 (by
    grw [pow_mul, ← le_self_pow₀, ← m2, e1] <;> bound)) (mod_cast by grind)
  set W := exp (_ * x)
  have Y i j (h : i ≤ j := by lia) : W ^ i ≤ W ^ j := by bound
  have s6 := @pow_le_of_le_log ((P.N₀ * P.d) ^ ((s + 6) * 2)) W n W0 (by
    grw [log_pow, log_exp, ← mul_assoc, ← h, log_le_self] <;> simp [field]; grind)
  have s5 : 2 ^ s ≤ W ^ n := s6.trans' (mod_cast by gcongr <;> nlinarith only [P.lt_d, pos P.N₀])
  obtain ⟨hg, w2⟩ := hg _ (by lia) s6, Y 2 6
  simp [pow_mul, field] at hg k2
  choose i1 p hp hm l u using fun i : Fin (classNumber P.K + 1) ↦ have : 0 ≤ i * W ∧ (i + 1) * W * 2
    ≤ W ^ 2 := ⟨by bound, by grw [i.is_le]; nlinarith only [h5]⟩; And.intro this (hg (10 * W ^ 6
    + 2 * i * W) (by bound) (by nlinarith only [this, Y 7 n, w2, h5]))
  have hN i := (hm i).of_dvd (P.N₁_mul_d_dvd_M_omega.pow out)
  choose I J nI nJ eJ using fun i ↦ have := Fact.mk (hp i); (FinPlace.exists_natCast_mem P.K
      (p i)).imp fun w h ↦ (prime_inert_or_eq_mul w h).imp fun _ ↦
      (·.2.resolve_left (by simp [(q_eq_iff_legendreSym_ne_neg_one w h).2, sq,
      chi_at_one P (hN i), (hp i).ne_one]))
  have ⟨i, j, ne, α, hα⟩ := exists_mul_principal (⟨_, eJ · |>.symm⟩)
  let M := P.N₀ * 3 ^ (Nat.log 3 s + 5)
  have := @Parameters.placeClass_placeOfInt P s (M + 1) (mod_cast by simp [M])
  have ⟨T, t1, t2, t⟩ := exists_three_term_free (P.placeClass P.two_pow_dvd_N₁) (P.placeOfInt s
    (-1)) (P.placeOfInt s (M + 1)) n (2 ^ k) (324 * s) (by lia) (le_of_mul_le_mul_left (.trans (by
    unfold M; norm_cast; grw [pow_add, Nat.pow_log_le_add_one]; rify
    grw [← (le_div_iff₀ W0).1 k1, lx, ← hL, s8, s8]; ring; rfl)
    (@two_pow_le_of_pow_eq_one (M + 1) (mod_cast by
    simp) _ s (orderOf_pos _) (this ▸ Units.ext_iff.1 (pow_orderOf_eq_one _)))) (pos _))
  refine ⟨⟨_, W ^ 6, W, s, _, _, s8, T, p ∘ ![i, j], α, ?_, ?_, ?_, ⟨o, rfl, rfl⟩, ⟨e, rfl⟩,
    fun _ k ↦ (by cases t1 · ·; simp [*, P.placeClass_placeOfInt isCoprime_one_left.neg_left,
    Units.ext_iff, (ZMod.natCast_eq_zero_iff M _).2 k]), t, ?_, ?_, fun _ ↦ (hm _).symm.dvd',
    (Fin.strictMono_iff_lt_succ.2 fun i ↦ by
    rify; grw [← log_lt_log_iff, u, ← l] <;> simp [(hp _).pos]; bound).injective.comp
    (by simpa), by
    simp [pow_le_iff_le_log, le_pow_iff_log_le, (hp _).pos, exp_pos]; grind, ?_, ?_⟩, ?_⟩ <;>
    simp [m2.le, r2.le, ← absNorm_span_eq_mul_star, ← hα, nI, nJ, hp, hN]
  simp [W]; and_intros <;> nlinarith only [e0, e1, w2, lx, h3, hf, h5]
  iterate 2 simpa [pow_succ']
  grw [← le_sqrt_of_sq_le w2]; intros
  apply hg <;> grind
  use by bound, by simp [W, field]
  grw [← t2, towerDeg, pow_add, Nat.pow_log_le_add_one]; simp; grw [k2, s8, pow_succ,
    pow_right_comm]
  field; grw [(lt_of_pow_lt_pow_left₀ n W0.le (by grw [← s5, pow_right_comm, k1]; bound) :), lx]
  nlinarith only [hC, Y 3 5]

end FixedClassRH.Cutoff
