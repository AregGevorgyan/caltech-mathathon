import TrotterAnalytic.Chain
import TrotterAnalytic.IntegralRemainder
import TrotterAnalytic.ProductFormula

/-!
# Lemma 3′ (chain form) and the grouped single-step theorem

For each chain item `a` with tail coefficients `c_j = c(tail, j)`, put

  `Pₐ(u) = ∑_{j<K} (1-u)^{K-j-1}/(K-j-1)! • ad_a^{K-j} c_j`   (`0 ≤ u ≤ 1`).

Then `‖V(τ) - ∑_{r<K} τ^r c_r‖ ≤ τ^K ∑_items ∫₀¹ ‖Pₐ(u)‖ du`.  This is Lemma 3′ of the write-up
(with `k = K - j`): all orders `k` of one item are normed together.  By the triangle inequality in
`j` and `∫₀¹ (1-u)^{k-1}/(k-1)! du = 1/k!` it is never worse than Lemma 3 (`Chain.lean`).

The assembled product-formula theorem with these constants is `norm_prodExp_sub_exp_le_grouped`;
the universal constants of the paper are obtained from it by writing each `Pₐ(u)` over
right-nested commutators and applying the triangle inequality under the integral.
-/

open NormedSpace Finset intervalIntegral MeasureTheory

set_option linter.unusedSectionVars false

namespace Trotter

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- The grouped polynomial `Pₐ(u)`. -/
noncomputable def groupedP (a : 𝔸) (K : ℕ) (c : ℕ → 𝔸) (u : ℝ) : 𝔸 :=
  ∑ j ∈ range K, ((1 - u) ^ (K - j - 1) / ((K - j - 1).factorial : ℝ)) • (ad a)^[K - j] (c j)

theorem continuous_groupedP (a : 𝔸) (K : ℕ) (c : ℕ → 𝔸) : Continuous (groupedP a K c) := by
  unfold groupedP
  exact continuous_finsetSum _ fun j _ =>
    (((continuous_const.sub continuous_id).pow _).div_const _).smul continuous_const

/-- Substitution `σ = τ u` in the Lemma 3′ integral. -/
theorem integral_grouped_subst (a : 𝔸) (K : ℕ) (hK : 1 ≤ K) (c : ℕ → 𝔸) {τ : ℝ} (hτ : 0 ≤ τ) :
    ∫ σ in (0 : ℝ)..τ, ‖∑ j ∈ range K,
        (τ ^ j * ((τ - σ) ^ (K - j - 1) / ((K - j - 1).factorial : ℝ))) • (ad a)^[K - j] (c j)‖
      = τ ^ K * ∫ u in (0 : ℝ)..1, ‖groupedP a K c u‖ := by
  rcases hτ.eq_or_lt with h0 | hpos
  · subst h0; simp [zero_pow (by omega : K ≠ 0)]
  have hpt : ∀ u : ℝ, ‖∑ j ∈ range K,
        (τ ^ j * ((τ - τ * u) ^ (K - j - 1) / ((K - j - 1).factorial : ℝ))) • (ad a)^[K - j] (c j)‖
      = τ ^ (K - 1) * ‖groupedP a K c u‖ := by
    intro u
    have : ∑ j ∈ range K,
        (τ ^ j * ((τ - τ * u) ^ (K - j - 1) / ((K - j - 1).factorial : ℝ))) • (ad a)^[K - j] (c j)
        = τ ^ (K - 1) • groupedP a K c u := by
      unfold groupedP
      rw [smul_sum]
      apply sum_congr rfl; intro j hj
      rw [smul_smul]; congr 1
      have hjK : j + (K - j - 1) = K - 1 := by have := mem_range.mp hj; omega
      rw [show τ - τ * u = τ * (1 - u) by ring, mul_pow, ← hjK, pow_add]; ring
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hτ _)]
  have hsub := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1)
    (fun σ => ‖∑ j ∈ range K,
        (τ ^ j * ((τ - σ) ^ (K - j - 1) / ((K - j - 1).factorial : ℝ))) • (ad a)^[K - j] (c j)‖)
    hpos.ne'
  simp only [mul_zero, mul_one] at hsub
  rw [show (∫ σ in (0 : ℝ)..τ, ‖∑ j ∈ range K,
        (τ ^ j * ((τ - σ) ^ (K - j - 1) / ((K - j - 1).factorial : ℝ))) • (ad a)^[K - j] (c j)‖)
      = τ • ∫ u in (0 : ℝ)..1, ‖∑ j ∈ range K,
        (τ ^ j * ((τ - τ * u) ^ (K - j - 1) / ((K - j - 1).factorial : ℝ))) • (ad a)^[K - j] (c j)‖ by
    rw [hsub, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]]
  simp only [hpt, intervalIntegral.integral_const_mul, smul_eq_mul]
  rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hK]

/-- Lemma 3′ constant of a chain. -/
noncomputable def chainBg (Z : 𝔸) : List 𝔸 → ℕ → ℝ
  | [], _ => 0
  | a :: L, K => chainBg Z L K + ∫ u in (0 : ℝ)..1, ‖groupedP a K (chainC Z L) u‖

/-- **Lemma 3′ (chain form).** -/
theorem norm_chain_sub_taylor_le_grouped (Z : 𝔸) :
    ∀ (L : List 𝔸), (∀ a ∈ L, ∀ s : ℝ, ‖exp (s • a)‖ ≤ 1) →
      ∀ (K : ℕ), 1 ≤ K → ∀ {τ : ℝ}, 0 ≤ τ →
        ‖chainV Z L τ - ∑ r ∈ range K, τ ^ r • chainC Z L r‖ ≤ τ ^ K * chainBg Z L K
  | [], _, K, hK, τ, _ => by
    simp only [chainV, chainC, chainBg, mul_zero]
    rw [sum_ite_zero_smul K hK τ Z, sub_self, norm_zero]
  | a :: L, hL, K, hK, τ, hτ => by
    have ha : ∀ s : ℝ, ‖exp (s • a)‖ ≤ 1 := hL a (by simp)
    have hL' : ∀ b ∈ L, ∀ s : ℝ, ‖exp (s • b)‖ ≤ 1 := fun b hb => hL b (by simp [hb])
    have ih := norm_chain_sub_taylor_le_grouped Z L hL' K hK hτ
    set c : ℕ → 𝔸 := chainC Z L with hc
    set P : 𝔸 := ∑ j ∈ range K, τ ^ j • c j with hP
    set E : 𝔸 := chainV Z L τ - P with hE
    have hAdlin : Ad a τ (E + P) = Ad a τ E + ∑ j ∈ range K, τ ^ j • Ad a τ (c j) := by
      simp only [hP, Ad, mul_add, add_mul, mul_sum, sum_mul, mul_smul_comm, smul_mul_assoc]
    have hdiag : ∑ j ∈ range K, τ ^ j • taylorAd a (K - j) (c j) τ
        = ∑ m ∈ range K, τ ^ m •
            ∑ k ∈ range (m + 1), (1 / ((m - k).factorial : ℝ)) • (ad a)^[m - k] (c k) := by
      simp only [taylorAd, smul_sum]
      rw [← sum_range_diag_flip K (fun m k => τ ^ m • (τ ^ k / (k.factorial : ℝ)) • (ad a)^[k] (c m))]
      apply sum_congr rfl; intro m _
      apply sum_congr rfl; intro k hk
      have hkm : k ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hk)
      rw [smul_smul, smul_smul]
      congr 1
      rw [div_eq_mul_one_div (τ ^ (m - k)), ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hkm]
    have hexp : chainV Z (a :: L) τ - ∑ r ∈ range K, τ ^ r • chainC Z (a :: L) r
        = Ad a τ E + ∑ j ∈ range K, τ ^ j • (Ad a τ (c j) - taylorAd a (K - j) (c j) τ) := by
      have h1 : chainV Z L τ = E + P := by rw [hE]; abel
      simp only [chainV, chainC, smul_add, sum_add_distrib]
      rw [sum_ite_zero_smul K hK τ a, h1, hAdlin]
      rw [← hdiag]
      simp only [smul_sub, sum_sub_distrib]
      abel
    rw [hexp]
    have hg := norm_grouped_remainder_le a ha K c hτ
    rw [integral_grouped_subst a K hK c hτ] at hg
    calc ‖Ad a τ E + ∑ j ∈ range K, τ ^ j • (Ad a τ (c j) - taylorAd a (K - j) (c j) τ)‖
        ≤ ‖Ad a τ E‖ + ‖∑ j ∈ range K, τ ^ j • (Ad a τ (c j) - taylorAd a (K - j) (c j) τ)‖ :=
          norm_add_le _ _
      _ ≤ τ ^ K * chainBg Z L K + τ ^ K * ∫ u in (0 : ℝ)..1, ‖groupedP a K c u‖ :=
          add_le_add ((norm_Ad_le a ha τ E).trans ih) hg
      _ = τ ^ K * chainBg Z (a :: L) K := by simp only [chainBg, mul_add, hc]

variable [NormOneClass 𝔸]

/-- **Single-step theorem with Lemma 3′ constants**, for any product formula. -/
theorem norm_prodExp_sub_exp_le_grouped (L : List 𝔸) (hL : ∀ a ∈ L, ∀ s : ℝ, ‖exp (s • a)‖ ≤ 1)
    (H : 𝔸) (hH : ∀ s : ℝ, ‖exp (s • H)‖ ≤ 1) (K : ℕ) (hK : 1 ≤ K) {t : ℝ} (ht : 0 ≤ t) :
    ‖prodExp L t - exp (t • H)‖
      ≤ ∑ r ∈ range K, ‖chainC 0 L r - (if r = 0 then H else 0)‖ * (t ^ (r + 1) / (r + 1))
        + chainBg 0 L K * (t ^ (K + 1) / (K + 1)) := by
  set D : ℝ → 𝔸 := fun τ => (chainV 0 L τ - H) * prodExp L τ
  have hS : ∀ τ, HasDerivAt (prodExp L) (H * prodExp L τ + D τ) τ := by
    intro τ
    convert hasDerivAt_prodExp L τ using 1
    simp only [D, sub_mul]; abel
  have hDc : Continuous D := by
    refine ((continuous_chainV 0 L).sub continuous_const).mul ?_
    exact continuous_iff_continuousAt.2 fun τ => (hasDerivAt_prodExp L τ).continuousAt
  have hb : ∀ τ ∈ Set.Icc 0 t, ‖D τ‖ ≤
      ∑ r ∈ range (K + 1), (if r < K then ‖chainC 0 L r - (if r = 0 then H else 0)‖
        else chainBg 0 L K) * τ ^ r := by
    intro τ hτ
    have hτ0 := hτ.1
    have htay := norm_chain_sub_taylor_le_grouped (0 : 𝔸) L hL K hK hτ0
    have hHsum : ∑ r ∈ range K, τ ^ r • (if r = 0 then H else 0) = H := sum_ite_zero_smul K hK τ H
    calc ‖D τ‖ ≤ ‖chainV 0 L τ - H‖ * ‖prodExp L τ‖ := norm_mul_le _ _
      _ ≤ ‖chainV 0 L τ - H‖ * 1 := by gcongr; exact norm_prodExp_le L hL τ
      _ = ‖(chainV 0 L τ - ∑ r ∈ range K, τ ^ r • chainC 0 L r)
            + ∑ r ∈ range K, τ ^ r • (chainC 0 L r - (if r = 0 then H else 0))‖ := by
          rw [mul_one]; congr 1
          simp only [smul_sub, sum_sub_distrib, hHsum]; abel
      _ ≤ τ ^ K * chainBg 0 L K
            + ∑ r ∈ range K, τ ^ r * ‖chainC 0 L r - (if r = 0 then H else 0)‖ := by
          refine (norm_add_le _ _).trans (add_le_add htay ?_)
          refine (norm_sum_le _ _).trans (le_of_eq ?_)
          apply sum_congr rfl; intro r _
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hτ0 r)]
      _ = _ := by
          rw [sum_range_succ, if_neg (lt_irrefl K)]
          rw [add_comm]; congr 1
          · apply sum_congr rfl; intro r hr; rw [if_pos (mem_range.mp hr)]; ring
          · ring
  have := norm_sub_exp_le_poly H hH (prodExp L) D hS hDc (prodExp_zero L) ht (range (K + 1)) _ hb
  refine this.trans (le_of_eq ?_)
  rw [sum_range_succ, if_neg (lt_irrefl K)]
  congr 1
  apply sum_congr rfl; intro r hr; rw [if_pos (mem_range.mp hr)]

end Trotter
