import Mathlib

/-!
# Variation of constants (Lemma 1)

`𝔸` is a real Banach algebra and `H : 𝔸` generates a contraction group:
`‖exp (s • H)‖ ≤ 1` for all real `s` (e.g. `H` anti-Hermitian in a C*-algebra, so
`exp (s • H)` is unitary).  If `S : ℝ → 𝔸` satisfies `S 0 = 1` and
`S' τ = H * S τ + D τ` (the *defect* `D = S' - H S`), then for `t ≥ 0`

  `‖S t - exp (t • H)‖ ≤ ∫₀ᵗ ‖D τ‖ dτ`.

With a split product `S = L R` the defect is `L T R` (Lemma 1 of the write-up); when `L`, `R`
are contractions, `‖D τ‖ ≤ ‖T τ‖`.  A polynomial bound `‖D τ‖ ≤ ∑ cₙ τⁿ` then integrates to
`‖S t - exp (t • H)‖ ≤ ∑ cₙ tⁿ⁺¹/(n+1)`, the shape of the bound (★).
-/

open NormedSpace intervalIntegral MeasureTheory

set_option linter.unusedSectionVars false

namespace Trotter

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- `exp(t•H) * exp(t•(-H)) = 1`. -/
theorem exp_smul_mul_exp_smul_neg (H : 𝔸) (t : ℝ) :
    exp (t • H) * exp (t • (-H)) = 1 := by
  let +nondep : NormedAlgebra ℚ 𝔸 := .restrictScalars ℚ ℝ 𝔸
  rw [smul_neg, ← exp_add_of_commute (Commute.neg_right (Commute.refl _)), add_neg_cancel,
    exp_zero]

/-- **Lemma 1 (variation of constants), norm form.** -/
theorem norm_sub_exp_le_integral (H : 𝔸) (hU : ∀ s : ℝ, ‖exp (s • H)‖ ≤ 1)
    (S D : ℝ → 𝔸) (hS : ∀ τ, HasDerivAt S (H * S τ + D τ) τ) (hD : Continuous D)
    (hS0 : S 0 = 1) {t : ℝ} (ht : 0 ≤ t) :
    ‖S t - exp (t • H)‖ ≤ ∫ τ in (0 : ℝ)..t, ‖D τ‖ := by
  -- f τ = exp(τ•(-H)) * S τ has derivative exp(τ•(-H)) * D τ
  set g : ℝ → 𝔸 := fun τ => exp (τ • (-H)) with hg
  have hgd : ∀ τ, HasDerivAt g (g τ * (-H)) τ := fun τ => hasDerivAt_exp_smul_const (-H) τ
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun τ => (hgd τ).continuousAt
  have hgn : ∀ τ, ‖g τ‖ ≤ 1 := by
    intro τ
    have : τ • (-H) = (-τ) • H := by rw [smul_neg, neg_smul]
    simp only [hg, this]; exact hU _
  have hfd : ∀ τ, HasDerivAt (fun τ => g τ * S τ) (g τ * D τ) τ := by
    intro τ
    have := (hgd τ).mul (hS τ)
    convert this using 1
    noncomm_ring
  have hint : IntervalIntegrable (fun τ => g τ * D τ) volume 0 t :=
    (hgc.mul hD).intervalIntegrable _ _
  have hftc := integral_eq_sub_of_hasDerivAt (fun τ _ => hfd τ) hint
  have hf0 : g 0 * S 0 = 1 := by simp [hg, hS0]
  -- S t - exp(tH) = exp(tH) * (g t * S t - 1)
  have hrepr : S t - exp (t • H) = exp (t • H) * (g t * S t - g 0 * S 0) := by
    rw [hf0, mul_sub, ← mul_assoc, exp_smul_mul_exp_smul_neg, one_mul, mul_one]
  rw [hrepr]
  calc ‖exp (t • H) * (g t * S t - g 0 * S 0)‖
      ≤ ‖exp (t • H)‖ * ‖g t * S t - g 0 * S 0‖ := norm_mul_le _ _
    _ ≤ 1 * ‖g t * S t - g 0 * S 0‖ := by gcongr; exact hU t
    _ = ‖∫ τ in (0 : ℝ)..t, g τ * D τ‖ := by rw [one_mul, hftc]
    _ ≤ ∫ τ in (0 : ℝ)..t, ‖g τ * D τ‖ := norm_integral_le_integral_norm ht
    _ ≤ ∫ τ in (0 : ℝ)..t, ‖D τ‖ := by
        apply integral_mono_on ht
        · exact (hgc.mul hD).norm.intervalIntegrable _ _
        · exact hD.norm.intervalIntegrable _ _
        · intro τ _
          calc ‖g τ * D τ‖ ≤ ‖g τ‖ * ‖D τ‖ := norm_mul_le _ _
            _ ≤ 1 * ‖D τ‖ := by gcongr; exact hgn τ
            _ = ‖D τ‖ := one_mul _

/-- **Split form of Lemma 1.**  If the defect factorises as `L τ * T τ * R τ` with contractions
`L τ`, `R τ` (products of unitary stage exponentials), only `‖T τ‖` enters. -/
theorem norm_sub_exp_le_integral_split (H : 𝔸) (hU : ∀ s : ℝ, ‖exp (s • H)‖ ≤ 1)
    (S L T R : ℝ → 𝔸) (hS : ∀ τ, HasDerivAt S (H * S τ + L τ * T τ * R τ) τ)
    (hc : Continuous fun τ => L τ * T τ * R τ) (hT : Continuous T)
    (hL : ∀ τ, ‖L τ‖ ≤ 1) (hR : ∀ τ, ‖R τ‖ ≤ 1) (hS0 : S 0 = 1) {t : ℝ} (ht : 0 ≤ t) :
    ‖S t - exp (t • H)‖ ≤ ∫ τ in (0 : ℝ)..t, ‖T τ‖ := by
  refine (norm_sub_exp_le_integral H hU S _ hS hc hS0 ht).trans ?_
  apply integral_mono_on ht (hc.norm.intervalIntegrable _ _) (hT.norm.intervalIntegrable _ _)
  intro τ _
  calc ‖L τ * T τ * R τ‖ ≤ ‖L τ‖ * ‖T τ‖ * ‖R τ‖ := by
        refine (norm_mul_le _ _).trans ?_; gcongr; exact norm_mul_le _ _
    _ ≤ 1 * ‖T τ‖ * 1 := by gcongr; exacts [hL τ, hR τ]
    _ = ‖T τ‖ := by ring

/-- Integrating a polynomial defect bound gives the shape of (★):
`‖D τ‖ ≤ ∑ₙ cₙ τⁿ` on `[0,t]` implies `∫₀ᵗ ‖D‖ ≤ ∑ₙ cₙ tⁿ⁺¹/(n+1)`. -/
theorem integral_le_of_poly_bound (D : ℝ → 𝔸) (hD : Continuous D) {t : ℝ} (ht : 0 ≤ t)
    (s : Finset ℕ) (c : ℕ → ℝ) (hb : ∀ τ ∈ Set.Icc 0 t, ‖D τ‖ ≤ ∑ n ∈ s, c n * τ ^ n) :
    ∫ τ in (0 : ℝ)..t, ‖D τ‖ ≤ ∑ n ∈ s, c n * (t ^ (n + 1) / (n + 1)) := by
  calc ∫ τ in (0 : ℝ)..t, ‖D τ‖ ≤ ∫ τ in (0 : ℝ)..t, ∑ n ∈ s, c n * τ ^ n := by
        apply integral_mono_on ht (hD.norm.intervalIntegrable _ _)
        · exact (continuous_finsetSum _ fun n _ => continuous_const.mul (continuous_pow n)).intervalIntegrable _ _
        · exact hb
    _ = ∑ n ∈ s, c n * (t ^ (n + 1) / (n + 1)) := by
        rw [intervalIntegral.integral_finsetSum]
        · apply Finset.sum_congr rfl; intro n _
          rw [intervalIntegral.integral_const_mul, integral_pow]; simp
        · intro n _; exact (continuous_const.mul (continuous_pow n)).intervalIntegrable _ _

/-- **Lemma 1 + polynomial defect bound** (the analytic content of (★)). -/
theorem norm_sub_exp_le_poly (H : 𝔸) (hU : ∀ s : ℝ, ‖exp (s • H)‖ ≤ 1)
    (S D : ℝ → 𝔸) (hS : ∀ τ, HasDerivAt S (H * S τ + D τ) τ) (hD : Continuous D)
    (hS0 : S 0 = 1) {t : ℝ} (ht : 0 ≤ t) (s : Finset ℕ) (c : ℕ → ℝ)
    (hb : ∀ τ ∈ Set.Icc 0 t, ‖D τ‖ ≤ ∑ n ∈ s, c n * τ ^ n) :
    ‖S t - exp (t • H)‖ ≤ ∑ n ∈ s, c n * (t ^ (n + 1) / (n + 1)) :=
  (norm_sub_exp_le_integral H hU S D hS hD hS0 ht).trans (integral_le_of_poly_bound D hD ht s c hb)

end Trotter
