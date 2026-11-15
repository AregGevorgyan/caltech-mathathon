import TrotterAnalytic.ConjTaylor

/-!
# Midpoint telescoping of the `[H, ·]` part (Theorem D, Step 3)

With `Ad a s Y = e^{sa} Y e^{-sa}` (contraction group) and midpoints `mⱼ = (j + 1/2) δ`:

  `‖∑_{j<r} δ • Ad a mⱼ (ad a Y)‖ ≤ 2 ‖Y‖ + r δ³/24 ‖ad³ Y‖`.

Each cell contributes `Ad a ((j+1)δ) Y - Ad a (jδ) Y` (exact derivative) up to the midpoint
error `δ³/24 ‖ad³ Y‖`, which comes from the sharp `K = 2` Taylor remainder of
`ConjTaylor.lean` applied for `±u`.  The sum of the exact parts telescopes to
`Ad a (rδ) Y - Y`, of norm `≤ 2‖Y‖`.
-/

open NormedSpace intervalIntegral MeasureTheory Finset

set_option linter.unusedSectionVars false

namespace Trotter

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

theorem exp_smul_add (a : 𝔸) (s u : ℝ) : exp ((s + u) • a) = exp (s • a) * exp (u • a) := by
  let +nondep : NormedAlgebra ℚ 𝔸 := .restrictScalars ℚ ℝ 𝔸
  rw [add_smul, exp_add_of_commute ((Commute.refl a).smul_left s |>.smul_right u)]

theorem Ad_add (a : 𝔸) (s u : ℝ) (Y : 𝔸) : Ad a (s + u) Y = Ad a s (Ad a u Y) := by
  simp only [Ad]
  have h1 := exp_smul_add a s u
  have h2 : exp ((s + u) • (-a)) = exp (u • (-a)) * exp (s • (-a)) := by
    rw [add_comm]; exact exp_smul_add (-a) u s
  rw [h1, h2]; noncomm_ring

theorem Ad_neg (a : 𝔸) (u : ℝ) (Y : 𝔸) : Ad a (-u) Y = Ad (-a) u Y := by
  simp only [Ad, neg_smul, smul_neg, neg_neg]

theorem ad_neg (a Y : 𝔸) : ad (-a) Y = -ad a Y := by simp only [ad]; noncomm_ring

theorem ad_smul (a W : 𝔸) (c : ℝ) : ad a (c • W) = c • ad a W := by
  simp only [ad, mul_smul_comm, smul_mul_assoc, smul_sub]

theorem iterate_ad_neg (a Y : 𝔸) (k : ℕ) : (ad (-a))^[k] Y = (-1 : ℝ) ^ k • (ad a)^[k] Y := by
  induction k generalizing Y with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply', ad_neg, ad_smul,
      pow_succ, mul_neg_one, neg_smul]

theorem norm_iterate_ad_neg (a Y : 𝔸) (k : ℕ) : ‖(ad (-a))^[k] Y‖ = ‖(ad a)^[k] Y‖ := by
  rw [iterate_ad_neg, norm_smul]; simp

/-- `K = 2` case of the conjugation Taylor bound, in explicit form. -/
theorem norm_Ad_sub_two_le (a : 𝔸) (ha : ∀ s : ℝ, ‖exp (s • a)‖ ≤ 1) (X : 𝔸) {u : ℝ}
    (hu : 0 ≤ u) : ‖Ad a u X - X - u • ad a X‖ ≤ u ^ 2 / 2 * ‖ad a (ad a X)‖ := by
  have := norm_Ad_sub_taylor_le a ha 2 X hu
  simpa [taylorAd, sum_range_succ, sub_sub, Function.iterate_succ_apply] using this

theorem contraction_neg (a : 𝔸) (ha : ∀ s : ℝ, ‖exp (s • a)‖ ≤ 1) :
    ∀ s : ℝ, ‖exp (s • (-a))‖ ≤ 1 := fun s => by rw [smul_neg, ← neg_smul]; exact ha _

/-- Symmetric second difference: `‖Ad_{c+u}X + Ad_{c-u}X - 2 Ad_c X‖ ≤ u² ‖ad² X‖`. -/
theorem norm_second_diff_le (a : 𝔸) (ha : ∀ s : ℝ, ‖exp (s • a)‖ ≤ 1) (c : ℝ) (X : 𝔸)
    {u : ℝ} (hu : 0 ≤ u) :
    ‖Ad a (c + u) X + Ad a (c - u) X - (2 : ℝ) • Ad a c X‖ ≤ u ^ 2 * ‖ad a (ad a X)‖ := by
  have e : Ad a (c + u) X + Ad a (c - u) X - (2 : ℝ) • Ad a c X
      = Ad a c ((Ad a u X - X - u • ad a X) + (Ad (-a) u X - X - u • ad (-a) X)) := by
    rw [Ad_add, sub_eq_add_neg c u, Ad_add, Ad_neg, ad_neg]
    simp only [Ad, two_smul, smul_neg]
    noncomm_ring
  rw [e]
  refine (norm_Ad_le a ha c _).trans ?_
  refine (norm_add_le _ _).trans ?_
  have h1 := norm_Ad_sub_two_le a ha X hu
  have h2 : ‖Ad (-a) u X - X - u • ad (-a) X‖ ≤ u ^ 2 / 2 * ‖ad a (ad a X)‖ := by
    have := norm_Ad_sub_two_le (-a) (contraction_neg a ha) X hu
    rwa [show ad (-a) (ad (-a) X) = ad a (ad a X) by simp only [ad]; noncomm_ring] at this
  linarith

theorem hasDerivAt_Ad_comp (a Y : 𝔸) (c σ : ℝ) (u : ℝ) :
    HasDerivAt (fun u => Ad a (c + σ * u) Y) (σ • Ad a (c + σ * u) (ad a Y)) u := by
  have hin : HasDerivAt (fun u : ℝ => c + σ * u) σ u := by
    simpa using ((hasDerivAt_id u).const_mul σ).const_add c
  exact (hasDerivAt_Ad a Y (c + σ * u)).scomp u hin

/-- **Midpoint cell.** `‖Ad_{c+h}Y - Ad_{c-h}Y - 2h Ad_c(ad Y)‖ ≤ (2h)³/24 ‖ad³ Y‖`. -/
theorem norm_cell_le (a : 𝔸) (ha : ∀ s : ℝ, ‖exp (s • a)‖ ≤ 1) (c : ℝ) (Y : 𝔸) {h : ℝ}
    (hh : 0 ≤ h) :
    ‖Ad a (c + h) Y - Ad a (c - h) Y - (2 * h) • Ad a c (ad a Y)‖
      ≤ (2 * h) ^ 3 / 24 * ‖ad a (ad a (ad a Y))‖ := by
  set φ : ℝ → 𝔸 := fun u => Ad a (c + 1 * u) Y - Ad a (c + (-1) * u) Y - (2 * u) • Ad a c (ad a Y)
  set φ' : ℝ → 𝔸 := fun u =>
    Ad a (c + 1 * u) (ad a Y) + Ad a (c + (-1) * u) (ad a Y) - (2 : ℝ) • Ad a c (ad a Y)
  have hφ : ∀ u, HasDerivAt φ (φ' u) u := by
    intro u
    have h1 := hasDerivAt_Ad_comp a Y c 1 u
    have h2 := hasDerivAt_Ad_comp a Y c (-1) u
    have h3 : HasDerivAt (fun u : ℝ => (2 * u) • Ad a c (ad a Y)) ((2 : ℝ) • Ad a c (ad a Y)) u := by
      simpa using ((hasDerivAt_id u).const_mul (2 : ℝ)).smul_const (Ad a c (ad a Y))
    convert (h1.sub h2).sub h3 using 1
    simp only [φ', one_smul, neg_one_smul, sub_neg_eq_add]
  have hc : Continuous φ' := by
    refine Continuous.sub (Continuous.add ?_ ?_) continuous_const
    · exact (continuous_Ad a _).comp (continuous_const.add (continuous_const.mul continuous_id))
    · exact (continuous_Ad a _).comp (continuous_const.add (continuous_const.mul continuous_id))
  have hftc := integral_eq_sub_of_hasDerivAt (fun u _ => hφ u) (hc.intervalIntegrable 0 h)
  have hφ0 : φ 0 = 0 := by simp [φ]
  rw [hφ0, sub_zero] at hftc
  have hb : ∀ u ∈ Set.Icc (0 : ℝ) h, ‖φ' u‖ ≤ u ^ 2 * ‖ad a (ad a (ad a Y))‖ := by
    intro u hu
    have := norm_second_diff_le a ha c (ad a Y) hu.1
    simpa [φ', sub_eq_add_neg] using this
  have hφh : φ h = Ad a (c + h) Y - Ad a (c - h) Y - (2 * h) • Ad a c (ad a Y) := by
    simp [φ, sub_eq_add_neg]
  rw [← hφh, ← hftc]
  calc ‖∫ u in (0 : ℝ)..h, φ' u‖ ≤ ∫ u in (0 : ℝ)..h, ‖φ' u‖ := norm_integral_le_integral_norm hh
    _ ≤ ∫ u in (0 : ℝ)..h, u ^ 2 * ‖ad a (ad a (ad a Y))‖ := by
        apply integral_mono_on hh (hc.norm.intervalIntegrable _ _)
        · exact ((continuous_pow 2).mul continuous_const).intervalIntegrable _ _
        · exact hb
    _ = (2 * h) ^ 3 / 24 * ‖ad a (ad a (ad a Y))‖ := by
        rw [intervalIntegral.integral_mul_const, integral_pow]; ring

/-- **Theorem D, Step 3.** Midpoint telescoping of `[H, ·]` terms. -/
theorem norm_sum_midpoint_le (a : 𝔸) (ha : ∀ s : ℝ, ‖exp (s • a)‖ ≤ 1) (Y : 𝔸) {δ : ℝ}
    (hδ : 0 ≤ δ) (r : ℕ) :
    ‖∑ j ∈ range r, δ • Ad a ((j + 1 / 2 : ℝ) * δ) (ad a Y)‖
      ≤ 2 * ‖Y‖ + r * (δ ^ 3 / 24 * ‖ad a (ad a (ad a Y))‖) := by
  set e : ℕ → 𝔸 := fun j =>
    Ad a ((j + 1 : ℝ) * δ) Y - Ad a ((j : ℝ) * δ) Y - δ • Ad a ((j + 1 / 2 : ℝ) * δ) (ad a Y)
  have he : ∀ j, ‖e j‖ ≤ δ ^ 3 / 24 * ‖ad a (ad a (ad a Y))‖ := by
    intro j
    have := norm_cell_le a ha ((j + 1 / 2 : ℝ) * δ) Y (h := δ / 2) (by linarith)
    have e1 : (j + 1 / 2 : ℝ) * δ + δ / 2 = (j + 1 : ℝ) * δ := by ring
    have e2 : (j + 1 / 2 : ℝ) * δ - δ / 2 = (j : ℝ) * δ := by ring
    rw [e1, e2, show 2 * (δ / 2) = δ by ring] at this
    exact this
  have hsum : ∑ j ∈ range r, δ • Ad a ((j + 1 / 2 : ℝ) * δ) (ad a Y)
      = (Ad a ((r : ℝ) * δ) Y - Y) - ∑ j ∈ range r, e j := by
    have tel := sum_range_sub (fun j : ℕ => Ad a ((j : ℝ) * δ) Y) r
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_mul, Ad_zero] at tel
    rw [← tel, ← sum_sub_distrib]
    apply sum_congr rfl; intro j _; simp only [e]; abel
  rw [hsum]
  calc ‖(Ad a ((r : ℝ) * δ) Y - Y) - ∑ j ∈ range r, e j‖
      ≤ ‖Ad a ((r : ℝ) * δ) Y - Y‖ + ‖∑ j ∈ range r, e j‖ := norm_sub_le _ _
    _ ≤ (‖Ad a ((r : ℝ) * δ) Y‖ + ‖Y‖) + ∑ j ∈ range r, ‖e j‖ :=
        add_le_add (norm_sub_le _ _) (norm_sum_le _ _)
    _ ≤ (‖Y‖ + ‖Y‖) + ∑ _j ∈ range r, δ ^ 3 / 24 * ‖ad a (ad a (ad a Y))‖ := by
        gcongr with j
        · exact norm_Ad_le a ha _ _
        · exact he j
    _ = 2 * ‖Y‖ + r * (δ ^ 3 / 24 * ‖ad a (ad a (ad a Y))‖) := by simp; ring

end Trotter
