import TrotterAnalytic.Midpoint

/-!
# Euler–Maclaurin-corrected midpoint telescoping (Theorem D′, item 3)

`‖∑_{j<r} δ • Ad_{mⱼ}(ad Y)‖ ≤ 2‖Y‖ + δ²/12 ‖ad² Y‖ + r δ⁵ (1/1920 + 1/576) ‖ad⁵ Y‖`,  `mⱼ = (j+½)δ`.

Cell estimate: `‖Ad_{c+h}Y - Ad_{c-h}Y - 2h Ad_c(ad Y) - (2h)³/24 Ad_c(ad³ Y)‖ ≤ (2h)⁵/1920 ‖ad⁵ Y‖`
(the `K = 4` conjugation remainder at `±u`; odd orders cancel).  The `δ³/24` correction term is
itself an `[H,·]` term (`ad³Y = ad(ad²Y)`) and is telescoped with the first-order midpoint lemma.
-/

open NormedSpace intervalIntegral MeasureTheory Finset

set_option linter.unusedSectionVars false

namespace Trotter

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

theorem norm_Ad_sub_four_le (a : 𝔸) (ha : ∀ s : ℝ, ‖exp (s • a)‖ ≤ 1) (X : 𝔸) {u : ℝ}
    (hu : 0 ≤ u) :
    ‖Ad a u X - (X + u • ad a X + (u ^ 2 / 2) • ad a (ad a X) + (u ^ 3 / 6) • ad a (ad a (ad a X)))‖
      ≤ u ^ 4 / 24 * ‖ad a (ad a (ad a (ad a X)))‖ := by
  have := norm_Ad_sub_taylor_le a ha 4 X hu
  have e : taylorAd a 4 X u
      = X + u • ad a X + (u ^ 2 / 2) • ad a (ad a X) + (u ^ 3 / 6) • ad a (ad a (ad a X)) := by
    simp only [taylorAd, sum_range_succ, range_zero, sum_empty, Function.iterate_succ_apply',
      Function.iterate_zero, id, Nat.factorial]
    norm_num
  rw [e] at this
  simpa [Function.iterate_succ_apply', Nat.factorial] using this

/-- Symmetric fourth-order difference. -/
theorem norm_second_diff4_le (a : 𝔸) (ha : ∀ s : ℝ, ‖exp (s • a)‖ ≤ 1) (c : ℝ) (X : 𝔸)
    {u : ℝ} (hu : 0 ≤ u) :
    ‖Ad a (c + u) X + Ad a (c - u) X - (2 : ℝ) • Ad a c X - u ^ 2 • Ad a c (ad a (ad a X))‖
      ≤ u ^ 4 / 12 * ‖ad a (ad a (ad a (ad a X)))‖ := by
  set P1 := Ad a u X - (X + u • ad a X + (u ^ 2 / 2) • ad a (ad a X) + (u ^ 3 / 6) • ad a (ad a (ad a X)))
  set P2 := Ad (-a) u X - (X + u • ad (-a) X + (u ^ 2 / 2) • ad (-a) (ad (-a) X)
    + (u ^ 3 / 6) • ad (-a) (ad (-a) (ad (-a) X)))
  have e : Ad a (c + u) X + Ad a (c - u) X - (2 : ℝ) • Ad a c X - u ^ 2 • Ad a c (ad a (ad a X))
      = Ad a c (P1 + P2) := by
    rw [Ad_add, sub_eq_add_neg c u, Ad_add, Ad_neg]
    simp only [P1, P2, ad_neg, ad, Ad, smul_neg, two_smul, smul_sub, smul_add, mul_sub, sub_mul,
      mul_add, add_mul, mul_smul_comm, smul_mul_assoc, neg_mul, mul_neg, neg_neg]
    module
  rw [e]
  refine (norm_Ad_le a ha c _).trans ?_
  refine (norm_add_le _ _).trans ?_
  have h1 := norm_Ad_sub_four_le a ha X hu
  have h2 := norm_Ad_sub_four_le (-a) (contraction_neg a ha) X hu
  have e4 : ad (-a) (ad (-a) (ad (-a) (ad (-a) X))) = ad a (ad a (ad a (ad a X))) := by
    simp only [ad]; noncomm_ring
  rw [e4] at h2
  linarith

/-- **Corrected midpoint cell.** -/
theorem norm_cell4_le (a : 𝔸) (ha : ∀ s : ℝ, ‖exp (s • a)‖ ≤ 1) (c : ℝ) (Y : 𝔸) {h : ℝ}
    (hh : 0 ≤ h) :
    ‖Ad a (c + h) Y - Ad a (c - h) Y - (2 * h) • Ad a c (ad a Y)
        - ((2 * h) ^ 3 / 24) • Ad a c (ad a (ad a (ad a Y)))‖
      ≤ (2 * h) ^ 5 / 1920 * ‖ad a (ad a (ad a (ad a (ad a Y))))‖ := by
  set X := ad a Y
  set φ : ℝ → 𝔸 := fun u => Ad a (c + 1 * u) Y - Ad a (c + (-1) * u) Y - (2 * u) • Ad a c X
    - ((2 * u) ^ 3 / 24) • Ad a c (ad a (ad a X))
  set φ' : ℝ → 𝔸 := fun u => Ad a (c + 1 * u) X + Ad a (c + (-1) * u) X - (2 : ℝ) • Ad a c X
    - u ^ 2 • Ad a c (ad a (ad a X))
  have hφ : ∀ u, HasDerivAt φ (φ' u) u := by
    intro u
    have h1 := hasDerivAt_Ad_comp a Y c 1 u
    have h2 := hasDerivAt_Ad_comp a Y c (-1) u
    have h3 : HasDerivAt (fun u : ℝ => (2 * u) • Ad a c X) ((2 : ℝ) • Ad a c X) u := by
      simpa using ((hasDerivAt_id u).const_mul (2 : ℝ)).smul_const (Ad a c X)
    have h4 : HasDerivAt (fun u : ℝ => ((2 * u) ^ 3 / 24) • Ad a c (ad a (ad a X)))
        (u ^ 2 • Ad a c (ad a (ad a X))) u := by
      have := ((((hasDerivAt_id u).const_mul (2 : ℝ)).pow 3).div_const 24).smul_const
        (Ad a c (ad a (ad a X)))
      refine this.congr_deriv ?_
      congr 1; simp only [id]; norm_num; ring
    convert ((h1.sub h2).sub h3).sub h4 using 1
    simp only [φ', one_smul, neg_one_smul, sub_neg_eq_add, X]
  have hc : Continuous φ' := by
    refine Continuous.sub (Continuous.sub (Continuous.add ?_ ?_) continuous_const)
      ((continuous_pow 2).smul continuous_const)
    · exact (continuous_Ad a _).comp (continuous_const.add (continuous_const.mul continuous_id))
    · exact (continuous_Ad a _).comp (continuous_const.add (continuous_const.mul continuous_id))
  have hftc := integral_eq_sub_of_hasDerivAt (fun u _ => hφ u) (hc.intervalIntegrable 0 h)
  have hφ0 : φ 0 = 0 := by simp [φ]
  rw [hφ0, sub_zero] at hftc
  have hb : ∀ u ∈ Set.Icc (0 : ℝ) h, ‖φ' u‖ ≤ u ^ 4 / 12 * ‖ad a (ad a (ad a (ad a X)))‖ := by
    intro u hu
    have := norm_second_diff4_le a ha c X hu.1
    simpa [φ', sub_eq_add_neg] using this
  have hφh : φ h = Ad a (c + h) Y - Ad a (c - h) Y - (2 * h) • Ad a c (ad a Y)
      - ((2 * h) ^ 3 / 24) • Ad a c (ad a (ad a (ad a Y))) := by
    simp [φ, X, sub_eq_add_neg]
  rw [← hφh, ← hftc]
  calc ‖∫ u in (0 : ℝ)..h, φ' u‖ ≤ ∫ u in (0 : ℝ)..h, ‖φ' u‖ :=
        intervalIntegral.norm_integral_le_integral_norm hh
    _ ≤ ∫ u in (0 : ℝ)..h, u ^ 4 / 12 * ‖ad a (ad a (ad a (ad a X)))‖ := by
        apply integral_mono_on hh (hc.norm.intervalIntegrable _ _)
        · exact (((continuous_pow 4).div_const _).mul continuous_const).intervalIntegrable _ _
        · exact hb
    _ = (2 * h) ^ 5 / 1920 * ‖ad a (ad a (ad a (ad a (ad a Y))))‖ := by
        rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_div, integral_pow]
        simp only [X]; ring

/-- **Theorem D′, item 3.** Euler–Maclaurin-corrected midpoint telescoping. -/
theorem norm_sum_midpoint2_le (a : 𝔸) (ha : ∀ s : ℝ, ‖exp (s • a)‖ ≤ 1) (Y : 𝔸) {δ : ℝ}
    (hδ : 0 ≤ δ) (r : ℕ) :
    ‖∑ j ∈ range r, δ • Ad a ((j + 1 / 2 : ℝ) * δ) (ad a Y)‖
      ≤ 2 * ‖Y‖ + δ ^ 2 / 12 * ‖ad a (ad a Y)‖
        + r * (δ ^ 5 * (1 / 1920 + 1 / 576) * ‖ad a (ad a (ad a (ad a (ad a Y))))‖) := by
  set m : ℕ → ℝ := fun j => (j + 1 / 2 : ℝ) * δ
  set e : ℕ → 𝔸 := fun j =>
    Ad a ((j + 1 : ℝ) * δ) Y - Ad a ((j : ℝ) * δ) Y - δ • Ad a (m j) (ad a Y)
      - (δ ^ 3 / 24) • Ad a (m j) (ad a (ad a (ad a Y)))
  have he : ∀ j, ‖e j‖ ≤ δ ^ 5 / 1920 * ‖ad a (ad a (ad a (ad a (ad a Y))))‖ := by
    intro j
    have := norm_cell4_le a ha (m j) Y (h := δ / 2) (by linarith)
    have e1 : m j + δ / 2 = (j + 1 : ℝ) * δ := by simp only [m]; ring
    have e2 : m j - δ / 2 = (j : ℝ) * δ := by simp only [m]; ring
    rw [e1, e2, show 2 * (δ / 2) = δ by ring] at this
    exact this
  have tel := sum_range_sub (fun j : ℕ => Ad a ((j : ℝ) * δ) Y) r
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_mul, Ad_zero] at tel
  -- the δ³ correction telescopes with the first-order midpoint lemma applied to ad² Y
  have hcorr := norm_sum_midpoint_le a ha (ad a (ad a Y)) hδ r
  have hsum : ∑ j ∈ range r, δ • Ad a (m j) (ad a Y)
      = (Ad a ((r : ℝ) * δ) Y - Y) - ∑ j ∈ range r, e j
        - (δ ^ 2 / 24) • ∑ j ∈ range r, δ • Ad a (m j) (ad a (ad a (ad a Y))) := by
    rw [← tel, smul_sum, ← sum_sub_distrib, ← sum_sub_distrib]
    apply sum_congr rfl; intro j _
    simp only [e, smul_smul]
    rw [show δ ^ 2 / 24 * δ = δ ^ 3 / 24 by ring]
    try abel
  rw [hsum]
  have hAd : ‖Ad a ((r : ℝ) * δ) Y - Y‖ ≤ 2 * ‖Y‖ := by
    refine (norm_sub_le _ _).trans ?_; linarith [norm_Ad_le a ha ((r : ℝ) * δ) Y]
  have hE : ‖∑ j ∈ range r, e j‖ ≤ r * (δ ^ 5 / 1920 * ‖ad a (ad a (ad a (ad a (ad a Y))))‖) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ j ∈ range r, ‖e j‖ ≤ ∑ _j ∈ range r, δ ^ 5 / 1920 * ‖ad a (ad a (ad a (ad a (ad a Y))))‖ :=
          sum_le_sum fun j _ => he j
      _ = _ := by simp
  have hC : ‖(δ ^ 2 / 24) • ∑ j ∈ range r, δ • Ad a (m j) (ad a (ad a (ad a Y)))‖
      ≤ δ ^ 2 / 24 * (2 * ‖ad a (ad a Y)‖
        + r * (δ ^ 3 / 24 * ‖ad a (ad a (ad a (ad a (ad a Y))))‖)) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    gcongr
  calc ‖(Ad a ((r : ℝ) * δ) Y - Y) - ∑ j ∈ range r, e j
        - (δ ^ 2 / 24) • ∑ j ∈ range r, δ • Ad a (m j) (ad a (ad a (ad a Y)))‖
      ≤ ‖Ad a ((r : ℝ) * δ) Y - Y‖ + ‖∑ j ∈ range r, e j‖
        + ‖(δ ^ 2 / 24) • ∑ j ∈ range r, δ • Ad a (m j) (ad a (ad a (ad a Y)))‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ 2 * ‖Y‖ + r * (δ ^ 5 / 1920 * ‖ad a (ad a (ad a (ad a (ad a Y))))‖)
        + δ ^ 2 / 24 * (2 * ‖ad a (ad a Y)‖
          + r * (δ ^ 3 / 24 * ‖ad a (ad a (ad a (ad a (ad a Y))))‖)) := by gcongr
    _ = _ := by ring

end Trotter
