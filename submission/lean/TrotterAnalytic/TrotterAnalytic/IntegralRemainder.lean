import TrotterAnalytic.ConjTaylor

/-!
# Integral form of the conjugation remainder, and Lemma 3′ for one chain item

`Ad_τ X - ∑_{i≤k} τ^i/i! ad^i X = ∫₀^τ (τ-σ)^k/k! • Ad_σ(ad^{k+1} X) dσ`

(proved with the telescoping primitive `Φ(σ) = ∑_{i≤k} (τ-σ)^i/i! • Ad_σ(ad^i X)`, no Fubini).

**Lemma 3′ (one item).**  For coefficients `c_j` (`j < K`) the combined remainder
`Q = ∑_{j<K} τ^j • (Ad_τ c_j - T_{K-j}(c_j))` satisfies

  `‖Q‖ ≤ ∫₀^τ ‖∑_{j<K} (τ^j (τ-σ)^{K-j-1}/(K-j-1)!) • ad^{K-j} c_j‖ dσ`,

i.e. the different orders are normed *together* (they share the conjugation `Ad_σ`).
-/

open NormedSpace Finset intervalIntegral MeasureTheory

set_option linter.unusedSectionVars false

namespace Trotter

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

theorem Ad_sum_arg (a : 𝔸) (τ : ℝ) {ι : Type*} (s : Finset ι) (f : ι → 𝔸) :
    Ad a τ (∑ i ∈ s, f i) = ∑ i ∈ s, Ad a τ (f i) := by
  simp only [Ad, mul_sum, sum_mul]

theorem Ad_smul_arg' (a : 𝔸) (τ c : ℝ) (X : 𝔸) : Ad a τ (c • X) = c • Ad a τ X := by
  simp only [Ad, mul_smul_comm, smul_mul_assoc]

/-- The telescoping primitive. -/
noncomputable def primΦ (a X : 𝔸) (τ : ℝ) (k : ℕ) (σ : ℝ) : 𝔸 :=
  ∑ i ∈ range k, ((τ - σ) ^ i / (i.factorial : ℝ)) • Ad a σ ((ad a)^[i] X)

theorem hasDerivAt_primΦ (a X : 𝔸) (τ : ℝ) : ∀ (k : ℕ) (σ : ℝ),
    HasDerivAt (primΦ a X τ (k + 1))
      (((τ - σ) ^ k / (k.factorial : ℝ)) • Ad a σ ((ad a)^[k + 1] X)) σ
  | 0, σ => by
    have h := hasDerivAt_Ad a X σ
    have e : primΦ a X τ 1 = fun σ => Ad a σ X := by funext σ; simp [primΦ]
    rw [e]; simpa using h
  | k + 1, σ => by
    have ih := hasDerivAt_primΦ a X τ k σ
    -- new term: f(σ) • g(σ), f = (τ-σ)^(k+1)/(k+1)!, g = Ad_σ(ad^(k+1) X)
    have hf : HasDerivAt (fun σ : ℝ => (τ - σ) ^ (k + 1) / ((k + 1).factorial : ℝ))
        (-((τ - σ) ^ k / (k.factorial : ℝ))) σ := by
      have h1 : HasDerivAt (fun σ : ℝ => τ - σ) (-1) σ := by
        simpa using (hasDerivAt_id σ).const_sub τ
      have h2 := (h1.pow (k + 1)).div_const ((k + 1).factorial : ℝ)
      convert h2 using 1
      rw [Nat.factorial_succ, Nat.cast_mul]
      have : (k.factorial : ℝ) ≠ 0 := by positivity
      field_simp
      push_cast
      ring
    have hg := hasDerivAt_Ad a ((ad a)^[k + 1] X) σ
    have hterm := hf.smul hg
    have hsum : primΦ a X τ (k + 1 + 1) = fun σ => primΦ a X τ (k + 1) σ +
        ((τ - σ) ^ (k + 1) / ((k + 1).factorial : ℝ)) • Ad a σ ((ad a)^[k + 1] X) := by
      funext σ; simp only [primΦ]; rw [sum_range_succ]
    rw [hsum]
    convert ih.add hterm using 1
    rw [Function.iterate_succ_apply' (ad a) (k + 1)]
    simp only [neg_smul]
    abel

theorem continuous_primΦ_deriv (a X : 𝔸) (τ : ℝ) (k : ℕ) :
    Continuous fun σ => ((τ - σ) ^ k / (k.factorial : ℝ)) • Ad a σ ((ad a)^[k + 1] X) :=
  (((continuous_const.sub continuous_id).pow k).div_const _).smul (continuous_Ad a _)

/-- **Integral form of the remainder.** -/
theorem Ad_sub_taylor_eq_integral (a X : 𝔸) (τ : ℝ) (k : ℕ) :
    Ad a τ X - taylorAd a (k + 1) X τ
      = ∫ σ in (0 : ℝ)..τ, ((τ - σ) ^ k / (k.factorial : ℝ)) • Ad a σ ((ad a)^[k + 1] X) := by
  rw [integral_eq_sub_of_hasDerivAt (fun σ _ => hasDerivAt_primΦ a X τ k σ)
    ((continuous_primΦ_deriv a X τ k).intervalIntegrable _ _)]
  congr 1
  · simp only [primΦ, sub_self]
    rw [sum_eq_single 0]
    · simp
    · intro b _ hb; simp [zero_pow hb]
    · intro h; simp at h
  · simp only [primΦ, taylorAd, sub_zero, Ad_zero]

/-- **Lemma 3′ for one chain item** (orders grouped under one integral). -/
theorem norm_grouped_remainder_le (a : 𝔸) (ha : ∀ s : ℝ, ‖exp (s • a)‖ ≤ 1) (K : ℕ)
    (c : ℕ → 𝔸) {τ : ℝ} (hτ : 0 ≤ τ) :
    ‖∑ j ∈ range K, τ ^ j • (Ad a τ (c j) - taylorAd a (K - j) (c j) τ)‖
      ≤ ∫ σ in (0 : ℝ)..τ, ‖∑ j ∈ range K,
          (τ ^ j * ((τ - σ) ^ (K - j - 1) / ((K - j - 1).factorial : ℝ))) •
            (ad a)^[K - j] (c j)‖ := by
  have hrepr : ∑ j ∈ range K, τ ^ j • (Ad a τ (c j) - taylorAd a (K - j) (c j) τ)
      = ∫ σ in (0 : ℝ)..τ, Ad a σ (∑ j ∈ range K,
          (τ ^ j * ((τ - σ) ^ (K - j - 1) / ((K - j - 1).factorial : ℝ))) •
            (ad a)^[K - j] (c j)) := by
    have hj : ∀ j ∈ range K, τ ^ j • (Ad a τ (c j) - taylorAd a (K - j) (c j) τ)
        = ∫ σ in (0 : ℝ)..τ, (τ ^ j * ((τ - σ) ^ (K - j - 1) / ((K - j - 1).factorial : ℝ))) •
            Ad a σ ((ad a)^[K - j] (c j)) := by
      intro j hj
      obtain ⟨m, hm⟩ : ∃ m, K - j = m + 1 := ⟨K - j - 1, by have := mem_range.mp hj; omega⟩
      simp only [hm, Nat.add_sub_cancel]
      rw [Ad_sub_taylor_eq_integral, ← intervalIntegral.integral_smul]
      apply integral_congr; intro σ _
      simp only [smul_smul]
    rw [sum_congr rfl hj, ← intervalIntegral.integral_finsetSum]
    · apply integral_congr; intro σ _
      simp only [Ad_sum_arg, Ad_smul_arg']
    · intro j _
      exact ((continuous_const.mul (((continuous_const.sub continuous_id).pow _).div_const _)).smul
        (continuous_Ad a _)).intervalIntegrable _ _
  rw [hrepr]
  refine (intervalIntegral.norm_integral_le_integral_norm hτ).trans ?_
  apply integral_mono_on hτ
  · refine (Continuous.norm ?_).intervalIntegrable _ _
    have : (fun σ => Ad a σ (∑ j ∈ range K,
        (τ ^ j * ((τ - σ) ^ (K - j - 1) / ((K - j - 1).factorial : ℝ))) • (ad a)^[K - j] (c j)))
        = fun σ => ∑ j ∈ range K, (τ ^ j * ((τ - σ) ^ (K - j - 1) / ((K - j - 1).factorial : ℝ))) •
            Ad a σ ((ad a)^[K - j] (c j)) := by
      funext σ; simp only [Ad_sum_arg, Ad_smul_arg']
    rw [this]
    exact continuous_finsetSum _ fun j _ =>
      (continuous_const.mul (((continuous_const.sub continuous_id).pow _).div_const _)).smul
        (continuous_Ad a _)
  · refine (Continuous.norm ?_).intervalIntegrable _ _
    exact continuous_finsetSum _ fun j _ =>
      (continuous_const.mul (((continuous_const.sub continuous_id).pow _).div_const _)).smul
        continuous_const
  · intro σ _; exact norm_Ad_le a ha σ _

end Trotter
