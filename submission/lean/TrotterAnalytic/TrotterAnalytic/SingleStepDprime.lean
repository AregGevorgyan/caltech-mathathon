import TrotterAnalytic.SingleStepD
import TrotterAnalytic.TheoremDprime

/-!
# The single-step input of Theorem D′, and Theorem D′ end to end

With the notation of `SingleStepD.lean` and, in addition, `ĉ₆ = c₆` and
`W₇ = c₆/7 - ad_H² E₅/8`:

  `‖M(δ) - δ⁵ Ad_{U(-δ/2)} E₅ - δ⁷ Ad_{U(-δ/2)} W₇‖`
  `   ≤ δ⁸ B̂₇/8 + δ⁸ ‖ad_H³ E₅‖/48 + δ⁸ ‖[H, W₇]‖/2 + B̂₄ β δ⁵/5`   (the `ρ₈` of the write-up).
-/

open NormedSpace Finset intervalIntegral MeasureTheory

set_option linter.unusedSectionVars false

namespace Trotter

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]

theorem norm_Ad_sub_three_le (a : 𝔸) (ha : ∀ s : ℝ, ‖exp (s • a)‖ ≤ 1) (X : 𝔸) {u : ℝ}
    (hu : 0 ≤ u) :
    ‖Ad a u X - (X + u • ad a X + (u ^ 2 / 2) • ad a (ad a X))‖
      ≤ u ^ 3 / 6 * ‖ad a (ad a (ad a X))‖ := by
  have := norm_Ad_sub_taylor_le a ha 3 X hu
  have e : taylorAd a 3 X u = X + u • ad a X + (u ^ 2 / 2) • ad a (ad a X) := by
    simp only [taylorAd, sum_range_succ, range_zero, sum_empty, Function.iterate_succ_apply',
      Function.iterate_zero, id, Nat.factorial]
    norm_num
  rw [e] at this
  simpa [Function.iterate_succ_apply', Nat.factorial] using this

theorem norm_Ad_sub_one_le (a : 𝔸) (ha : ∀ s : ℝ, ‖exp (s • a)‖ ≤ 1) (X : 𝔸) {u : ℝ}
    (hu : 0 ≤ u) : ‖Ad a u X - X‖ ≤ u * ‖ad a X‖ := by
  have := norm_Ad_sub_taylor_le a ha 1 X hu
  simpa [taylorAd] using this

/-- **Single-step input of Theorem D′** (`ρ₈`). -/
theorem singleStep_input2 (H E₅ c₆ W₇ : 𝔸) (L : List 𝔸) (hH : ∀ s : ℝ, ‖exp (s • H)‖ ≤ 1)
    (hL : ∀ a ∈ L, ∀ s : ℝ, ‖exp (s • a)‖ ≤ 1)
    (h0 : ∀ r < 4, chainC 0 ((-H) :: L) r = 0)
    (h4 : chainC 0 ((-H) :: L) 4 = (5 : ℝ) • E₅)
    (h5 : chainC 0 ((-H) :: L) 5 = (-3 : ℝ) • ad H E₅)
    (h6 : chainC 0 ((-H) :: L) 6 = c₆)
    (hW : W₇ = (1 / 7 : ℝ) • c₆ - (1 / 8 : ℝ) • ad H (ad H E₅))
    {δ β : ℝ} (hδ : 0 ≤ δ) (hβ : ∀ τ ∈ Set.Icc 0 δ, ‖prodExp ((-H) :: L) τ - 1‖ ≤ β) :
    ‖(prodExp ((-H) :: L) δ - 1) - δ ^ 5 • Ad (-H) (δ / 2) E₅ - δ ^ 7 • Ad (-H) (δ / 2) W₇‖
      ≤ δ ^ 8 * chainBg 0 ((-H) :: L) 7 / 8 + δ ^ 8 / 48 * ‖ad H (ad H (ad H E₅))‖
        + δ ^ 8 / 2 * ‖ad H W₇‖ + chainBg 0 ((-H) :: L) 4 * β * δ ^ 5 / 5 := by
  set Lh := (-H) :: L with hLh
  have hLh' : ∀ a ∈ Lh, ∀ s : ℝ, ‖exp (s • a)‖ ≤ 1 := by
    intro a ha s
    rcases List.mem_cons.mp ha with rfl | ha
    · exact contraction_neg H hH s
    · exact hL a ha s
  set V := chainV 0 Lh
  set S := prodExp Lh
  have hVc : Continuous V := continuous_chainV 0 Lh
  have hSc : Continuous S := continuous_prodExp Lh
  have hftc : S δ - 1 = ∫ τ in (0 : ℝ)..δ, V τ * S τ := by
    rw [integral_eq_sub_of_hasDerivAt (fun τ _ => hasDerivAt_prodExp Lh τ)
      ((hVc.mul hSc).intervalIntegrable _ _), prodExp_zero]
  set P : ℝ → 𝔸 := fun τ => (5 * τ ^ 4) • E₅ + (-3 * τ ^ 5) • ad H E₅ + τ ^ 6 • c₆
  have hPc : Continuous P :=
    (((continuous_const.mul (continuous_pow 4)).smul continuous_const).add
      ((continuous_const.mul (continuous_pow 5)).smul continuous_const)).add
      ((continuous_pow 6).smul continuous_const)
  have hsum7 : ∀ τ : ℝ, ∑ r ∈ range 7, τ ^ r • chainC 0 Lh r = P τ := by
    intro τ
    simp only [sum_range_succ, range_zero, sum_empty, h0 0 (by norm_num), h0 1 (by norm_num),
      h0 2 (by norm_num), h0 3 (by norm_num), h4, h5, h6, smul_zero, zero_add, smul_smul, P]
    ring_nf
  have hsum4 : ∀ τ : ℝ, ∑ r ∈ range 4, τ ^ r • chainC 0 Lh r = 0 := by
    intro τ
    simp [sum_range_succ, h0 0 (by norm_num), h0 1 (by norm_num), h0 2 (by norm_num),
      h0 3 (by norm_num)]
  have hR7 : ∀ τ ∈ Set.Icc 0 δ, ‖V τ - P τ‖ ≤ τ ^ 7 * chainBg 0 Lh 7 := by
    intro τ hτ
    rw [← hsum7 τ]; exact norm_chain_sub_taylor_le_grouped 0 Lh hLh' 7 (by norm_num) hτ.1
  have hV4 : ∀ τ ∈ Set.Icc 0 δ, ‖V τ‖ ≤ τ ^ 4 * chainBg 0 Lh 4 := by
    intro τ hτ
    have := norm_chain_sub_taylor_le_grouped 0 Lh hLh' 4 (by norm_num) hτ.1
    rwa [hsum4 τ, sub_zero] at this
  have hintP : ∫ τ in (0 : ℝ)..δ, P τ
      = δ ^ 5 • E₅ - (δ ^ 6 / 2) • ad H E₅ + (δ ^ 7 / 7) • c₆ := by
    have i1 : IntervalIntegrable (fun τ : ℝ => (5 * τ ^ 4) • E₅) volume 0 δ :=
      ((continuous_const.mul (continuous_pow 4)).smul continuous_const).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun τ : ℝ => (-3 * τ ^ 5) • ad H E₅) volume 0 δ :=
      ((continuous_const.mul (continuous_pow 5)).smul continuous_const).intervalIntegrable _ _
    have i3 : IntervalIntegrable (fun τ : ℝ => τ ^ 6 • c₆) volume 0 δ :=
      ((continuous_pow 6).smul continuous_const).intervalIntegrable _ _
    simp only [P]
    rw [intervalIntegral.integral_add (i1.add i2) i3, intervalIntegral.integral_add i1 i2,
      intervalIntegral.integral_smul_const, intervalIntegral.integral_smul_const,
      intervalIntegral.integral_smul_const, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, integral_pow, integral_pow, integral_pow]
    simp only [sub_eq_add_neg, ← neg_smul]
    congr 1
    · congr 1 <;> congr 1 <;> ring
    · congr 1; push_cast; ring
  have hA3 := norm_Ad_sub_three_le (-H) (contraction_neg H hH) E₅ (u := δ / 2) (by linarith)
  have hA1 := norm_Ad_sub_one_le (-H) (contraction_neg H hH) W₇ (u := δ / 2) (by linarith)
  have n3 : ‖ad (-H) (ad (-H) (ad (-H) E₅))‖ = ‖ad H (ad H (ad H E₅))‖ := by
    rw [show ad (-H) (ad (-H) (ad (-H) E₅)) = -ad H (ad H (ad H E₅)) by simp only [ad]; noncomm_ring,
      norm_neg]
  have n1 : ‖ad (-H) W₇‖ = ‖ad H W₇‖ := by rw [ad_neg, norm_neg]
  rw [n3] at hA3
  rw [n1] at hA1
  have e1 : ad (-H) E₅ = -ad H E₅ := ad_neg H E₅
  have e2 : ad (-H) (-ad H E₅) = ad H (ad H E₅) := by simp only [ad]; noncomm_ring
  rw [e1, e2] at hA3
  set R3 := Ad (-H) (δ / 2) E₅ - (E₅ + (δ / 2) • -ad H E₅ + ((δ / 2) ^ 2 / 2) • ad H (ad H E₅))
  set R1 := Ad (-H) (δ / 2) W₇ - W₇
  have hsplit : S δ - 1 - δ ^ 5 • Ad (-H) (δ / 2) E₅ - δ ^ 7 • Ad (-H) (δ / 2) W₇
      = (∫ τ in (0 : ℝ)..δ, (V τ - P τ)) + (∫ τ in (0 : ℝ)..δ, V τ * (S τ - 1))
        - δ ^ 5 • R3 - δ ^ 7 • R1 := by
    rw [hftc, intervalIntegral.integral_sub (hVc.intervalIntegrable _ _) (hPc.intervalIntegrable _ _),
      hintP]
    have : ∫ τ in (0 : ℝ)..δ, V τ * S τ
        = (∫ τ in (0 : ℝ)..δ, V τ) + ∫ τ in (0 : ℝ)..δ, V τ * (S τ - 1) := by
      have e : (∫ τ in (0 : ℝ)..δ, V τ * S τ) = ∫ τ in (0 : ℝ)..δ, (V τ + V τ * (S τ - 1)) := by
        congr 1; funext τ; noncomm_ring
      have hi1 : IntervalIntegrable (fun τ => V τ) volume 0 δ := hVc.intervalIntegrable _ _
      have hi2 : IntervalIntegrable (fun τ => V τ * (S τ - 1)) volume 0 δ :=
        (hVc.mul (hSc.sub continuous_const)).intervalIntegrable _ _
      rw [e, intervalIntegral.integral_add hi1 hi2]
    rw [this]
    simp only [R3, R1, hW, smul_sub, smul_add, smul_neg, smul_smul]
    rw [show δ ^ 5 * (δ / 2) = δ ^ 6 / 2 by ring, show δ ^ 5 * ((δ / 2) ^ 2 / 2) = δ ^ 7 * (1 / 8) by ring,
      show δ ^ 7 * (1 / 7) = δ ^ 7 / 7 by ring]
    abel
  rw [hsplit]
  have hI1 : ‖∫ τ in (0 : ℝ)..δ, (V τ - P τ)‖ ≤ δ ^ 8 * chainBg 0 Lh 7 / 8 := by
    refine (intervalIntegral.norm_integral_le_integral_norm hδ).trans ?_
    calc ∫ τ in (0 : ℝ)..δ, ‖V τ - P τ‖ ≤ ∫ τ in (0 : ℝ)..δ, τ ^ 7 * chainBg 0 Lh 7 :=
          integral_mono_on hδ ((hVc.sub hPc).norm.intervalIntegrable _ _)
            (((continuous_pow 7).mul continuous_const).intervalIntegrable _ _) hR7
      _ = δ ^ 8 * chainBg 0 Lh 7 / 8 := by
          rw [intervalIntegral.integral_mul_const, integral_pow]; ring
  have hI2 : ‖∫ τ in (0 : ℝ)..δ, V τ * (S τ - 1)‖ ≤ chainBg 0 Lh 4 * β * δ ^ 5 / 5 := by
    refine (intervalIntegral.norm_integral_le_integral_norm hδ).trans ?_
    calc ∫ τ in (0 : ℝ)..δ, ‖V τ * (S τ - 1)‖
        ≤ ∫ τ in (0 : ℝ)..δ, τ ^ 4 * chainBg 0 Lh 4 * β := by
          apply integral_mono_on hδ ((hVc.mul (hSc.sub continuous_const)).norm.intervalIntegrable _ _)
            ((((continuous_pow 4).mul continuous_const).mul continuous_const).intervalIntegrable _ _)
          intro τ hτ
          refine (norm_mul_le _ _).trans ?_
          have hB : 0 ≤ τ ^ 4 * chainBg 0 Lh 4 := (norm_nonneg _).trans (hV4 τ hτ)
          exact mul_le_mul (hV4 τ hτ) (hβ τ hτ) (norm_nonneg _) hB
      _ = chainBg 0 Lh 4 * β * δ ^ 5 / 5 := by
          rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const, integral_pow]
          ring
  have hI3 : ‖δ ^ 5 • R3‖ ≤ δ ^ 8 / 48 * ‖ad H (ad H (ad H E₅))‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hδ 5)]
    calc δ ^ 5 * ‖R3‖ ≤ δ ^ 5 * ((δ / 2) ^ 3 / 6 * ‖ad H (ad H (ad H E₅))‖) := by gcongr
      _ = _ := by ring
  have hI4 : ‖δ ^ 7 • R1‖ ≤ δ ^ 8 / 2 * ‖ad H W₇‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hδ 7)]
    calc δ ^ 7 * ‖R1‖ ≤ δ ^ 7 * (δ / 2 * ‖ad H W₇‖) := by gcongr
      _ = _ := by ring
  calc ‖(∫ τ in (0 : ℝ)..δ, (V τ - P τ)) + (∫ τ in (0 : ℝ)..δ, V τ * (S τ - 1))
        - δ ^ 5 • R3 - δ ^ 7 • R1‖
      ≤ ‖∫ τ in (0 : ℝ)..δ, (V τ - P τ)‖ + ‖∫ τ in (0 : ℝ)..δ, V τ * (S τ - 1)‖
        + ‖δ ^ 5 • R3‖ + ‖δ ^ 7 • R1‖ :=
        (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
          (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    _ ≤ _ := by linarith

/-- **Theorem D′ end to end**: from the algebraic identities only. -/
theorem theoremDprime_full (H E₅ c₆ W₇ Y Z Y₇ Z₇ : 𝔸) (L : List 𝔸)
    (hH : ∀ s : ℝ, ‖exp (s • H)‖ ≤ 1) (hL : ∀ a ∈ L, ∀ s : ℝ, ‖exp (s • a)‖ ≤ 1)
    (h0 : ∀ r < 4, chainC 0 ((-H) :: L) r = 0)
    (h4 : chainC 0 ((-H) :: L) 4 = (5 : ℝ) • E₅)
    (h5 : chainC 0 ((-H) :: L) 5 = (-3 : ℝ) • ad H E₅)
    (h6 : chainC 0 ((-H) :: L) 6 = c₆)
    (hW : W₇ = (1 / 7 : ℝ) • c₆ - (1 / 8 : ℝ) • ad H (ad H E₅))
    (hE : E₅ = ad H Y + Z) (hW' : W₇ = ad H Y₇ + Z₇)
    {δ β : ℝ} (hδ : 0 ≤ δ) (hβ : ∀ τ ∈ Set.Icc 0 δ, ‖prodExp ((-H) :: L) τ - 1‖ ≤ β) (r : ℕ) :
    ‖prodExp L δ ^ r - exp (δ • H) ^ r‖
      ≤ δ ^ 5 * (r * ‖Z‖) + δ ^ 4 * (2 * ‖Y‖ + δ ^ 2 / 12 * ‖ad H (ad H Y)‖
          + r * (δ ^ 5 * (1 / 1920 + 1 / 576) * ‖ad H (ad H (ad H (ad H (ad H Y))))‖))
        + δ ^ 7 * (r * ‖Z₇‖) + δ ^ 6 * (2 * ‖Y₇‖ + r * (δ ^ 3 / 24 * ‖ad H (ad H (ad H Y₇))‖))
        + r * (δ ^ 8 * chainBg 0 ((-H) :: L) 7 / 8 + δ ^ 8 / 48 * ‖ad H (ad H (ad H E₅))‖
          + δ ^ 8 / 2 * ‖ad H W₇‖ + chainBg 0 ((-H) :: L) 4 * β * δ ^ 5 / 5)
        + ‖prodExp L δ - exp (δ • H)‖ ^ 2 * (r * (r - 1) / 2 : ℝ) := by
  have hρ := singleStep_input2 H E₅ c₆ W₇ L hH hL h0 h4 h5 h6 hW hδ hβ
  simp only [prodExp] at hρ
  have hS : ∀ k, ‖prodExp L δ ^ k‖ ≤ 1 := by
    intro k
    rcases k with _ | k
    · simp
    · exact (norm_pow_le' _ (Nat.succ_pos k)).trans
        (pow_le_one₀ (norm_nonneg _) (norm_prodExp_le L hL δ))
  exact theoremDprime H hH hδ r (prodExp L δ) hS E₅ Y Z W₇ Y₇ Z₇ hE hW' _ hρ

end Trotter
