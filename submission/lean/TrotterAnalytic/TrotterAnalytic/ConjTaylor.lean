import Mathlib

/-!
# Taylor expansion of a unitary conjugation with sharp remainder (core of Lemma 3)

For `a` generating a contraction group (`‖exp (s • a)‖ ≤ 1` for all real `s`; e.g. `a`
anti-Hermitian), put `Ad τ Y = exp (τ • a) * Y * exp (τ • (-a))` and `ad Y = a * Y - Y * a`.
Then for every `K`, every `Y` and every `τ ≥ 0`

  `‖Ad τ Y - ∑_{k<K} (τ^k / k!) • ad^[k] Y‖ ≤ τ^K / K! * ‖ad^[K] Y‖`.

This is the estimate behind Lemma 3: each remainder term is an exact nested commutator, and
the conjugations drop out of the norm.  The constant `1/K!` is sharp (it is the integral of
`(τ-σ)^(K-1)/(K-1)!`), better than generic Taylor bounds which give `1/(K-1)!`.
-/

open NormedSpace intervalIntegral MeasureTheory Finset

set_option linter.unusedSectionVars false

namespace Trotter

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- `ad a Y = a Y - Y a`. -/
def ad (a : 𝔸) (Y : 𝔸) : 𝔸 := a * Y - Y * a

/-- Conjugation `Ad τ Y = e^{τa} Y e^{-τa}`. -/
noncomputable def Ad (a : 𝔸) (τ : ℝ) (Y : 𝔸) : 𝔸 := exp (τ • a) * Y * exp (τ • (-a))

/-- Taylor polynomial `∑_{k<K} τ^k/k! • ad^k Y`. -/
noncomputable def taylorAd (a : 𝔸) (K : ℕ) (Y : 𝔸) (τ : ℝ) : 𝔸 :=
  ∑ k ∈ range K, (τ ^ k / k.factorial) • (ad a)^[k] Y

theorem hasDerivAt_Ad (a Y : 𝔸) (τ : ℝ) :
    HasDerivAt (fun τ => Ad a τ Y) (Ad a τ (ad a Y)) τ := by
  have h1 := hasDerivAt_exp_smul_const a τ
  have h2 := hasDerivAt_exp_smul_const' (-a) τ
  have key : HasDerivAt (fun τ => exp (τ • a) * Y * exp (τ • (-a)))
      (exp (τ • a) * a * Y * exp (τ • -a) + exp (τ • a) * Y * (-a * exp (τ • -a))) τ :=
    (h1.mul_const Y).mul h2
  unfold Ad ad
  convert key using 1
  noncomm_ring

theorem continuous_Ad (a Y : 𝔸) : Continuous fun τ => Ad a τ Y :=
  continuous_iff_continuousAt.2 fun τ => (hasDerivAt_Ad a Y τ).continuousAt

theorem Ad_zero (a Y : 𝔸) : Ad a 0 Y = Y := by simp [Ad]

theorem norm_Ad_le (a : 𝔸) (ha : ∀ s : ℝ, ‖exp (s • a)‖ ≤ 1) (τ : ℝ) (Y : 𝔸) :
    ‖Ad a τ Y‖ ≤ ‖Y‖ := by
  have h2 : ‖exp (τ • (-a))‖ ≤ 1 := by rw [smul_neg, ← neg_smul]; exact ha _
  calc ‖Ad a τ Y‖ ≤ ‖exp (τ • a)‖ * ‖Y‖ * ‖exp (τ • (-a))‖ := by
        refine (norm_mul_le _ _).trans ?_; gcongr; exact norm_mul_le _ _
    _ ≤ 1 * ‖Y‖ * 1 := by gcongr; exact ha τ
    _ = ‖Y‖ := by ring

/-- Derivative of the Taylor polynomial: `d/dτ T_{K+1}(Y) = T_K(ad Y)`. -/
theorem hasDerivAt_taylorAd (a : 𝔸) (K : ℕ) (Y : 𝔸) (τ : ℝ) :
    HasDerivAt (taylorAd a (K + 1) Y) (taylorAd a K (ad a Y) τ) τ := by
  unfold taylorAd
  have hs : (fun τ : ℝ => ∑ k ∈ range (K + 1), (τ ^ k / k.factorial) • (ad a)^[k] Y)
      = fun τ : ℝ => Y + ∑ k ∈ range K, (τ ^ (k + 1) / (k + 1).factorial) • (ad a)^[k] (ad a Y) := by
    funext τ
    rw [sum_range_succ']
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_smul,
      Function.iterate_zero, id, Function.iterate_succ_apply]
    abel
  rw [hs]
  apply HasDerivAt.const_add
  apply HasDerivAt.fun_sum
  intro k _
  apply HasDerivAt.smul_const
  have hp := (hasDerivAt_pow (k + 1) τ).div_const ((k + 1).factorial : ℝ)
  convert hp using 1
  rw [Nat.factorial_succ, Nat.cast_mul]
  have : (k.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  push_cast
  ring

theorem continuous_taylorAd (a : 𝔸) (K : ℕ) (Y : 𝔸) : Continuous (taylorAd a K Y) := by
  unfold taylorAd
  exact continuous_finsetSum _ fun k _ => ((continuous_pow k).div_const _).smul continuous_const

/-- **Lemma 3 (core).** Sharp Taylor remainder for a contraction-group conjugation. -/
theorem norm_Ad_sub_taylor_le (a : 𝔸) (ha : ∀ s : ℝ, ‖exp (s • a)‖ ≤ 1) :
    ∀ (K : ℕ) (Y : 𝔸) {τ : ℝ}, 0 ≤ τ →
      ‖Ad a τ Y - taylorAd a K Y τ‖ ≤ τ ^ K / K.factorial * ‖(ad a)^[K] Y‖
  | 0, Y, τ, _ => by simpa [taylorAd] using norm_Ad_le a ha τ Y
  | K + 1, Y, τ, hτ => by
    set F : ℝ → 𝔸 := fun σ => Ad a σ Y - taylorAd a (K + 1) Y σ
    set F' : ℝ → 𝔸 := fun σ => Ad a σ (ad a Y) - taylorAd a K (ad a Y) σ
    have hF : ∀ σ, HasDerivAt F (F' σ) σ := fun σ =>
      (hasDerivAt_Ad a Y σ).sub (hasDerivAt_taylorAd a K Y σ)
    have hF'c : Continuous F' := (continuous_Ad a _).sub (continuous_taylorAd a K _)
    have hF0 : F 0 = 0 := by
      simp only [F, Ad_zero, taylorAd, sum_range_succ', pow_zero, Nat.factorial_zero,
        Nat.cast_one, div_one, one_smul, Function.iterate_zero, id]
      simp
    have hftc := integral_eq_sub_of_hasDerivAt (fun σ _ => hF σ) (hF'c.intervalIntegrable 0 τ)
    rw [hF0, sub_zero] at hftc
    have hIH : ∀ σ ∈ Set.Icc 0 τ,
        ‖F' σ‖ ≤ σ ^ K / K.factorial * ‖(ad a)^[K + 1] Y‖ := by
      intro σ hσ
      have := norm_Ad_sub_taylor_le a ha K (ad a Y) hσ.1
      simpa [F', Function.iterate_succ_apply] using this
    calc ‖F τ‖ = ‖∫ σ in (0 : ℝ)..τ, F' σ‖ := by rw [hftc]
      _ ≤ ∫ σ in (0 : ℝ)..τ, ‖F' σ‖ := norm_integral_le_integral_norm hτ
      _ ≤ ∫ σ in (0 : ℝ)..τ, σ ^ K / K.factorial * ‖(ad a)^[K + 1] Y‖ := by
          apply integral_mono_on hτ (hF'c.norm.intervalIntegrable _ _)
          · exact (((continuous_pow K).div_const _).mul continuous_const).intervalIntegrable _ _
          · exact hIH
      _ = τ ^ (K + 1) / (K + 1).factorial * ‖(ad a)^[K + 1] Y‖ := by
          rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_div, integral_pow]
          rw [Nat.factorial_succ, Nat.cast_mul]
          have : (K.factorial : ℝ) ≠ 0 := by positivity
          field_simp
          push_cast
          ring

end Trotter
