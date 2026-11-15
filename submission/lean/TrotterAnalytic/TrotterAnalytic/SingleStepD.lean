import TrotterAnalytic.ChainGrouped
import TrotterAnalytic.TheoremD

/-!
# The single-step input of Theorem D (Step 2), and Theorem D end to end

Let `Ŝ(τ) = e^{-τH} S(τ) = prodExp ((-H) :: L) τ` (a product formula whose generators sum to `0`).
By Lemma 2 (`m = 0`), `Ŝ' = V̂ Ŝ` with `V̂ = chainV 0 ((-H) :: L)`, so `M(δ) = Ŝ(δ) - 1 = ∫₀^δ V̂ Ŝ`.

Algebraic input (exact identities between Lie polynomials, computed in exact arithmetic):
`ĉ₀ = … = ĉ₃ = 0`, `ĉ₄ = 5 E₅`, `ĉ₅ = -3 [H, E₅]` for the Taylor coefficients `ĉ_r` of `V̂`.

Then, with `B̂_K` the Lemma 3′ constants of the chain and `‖Ŝ(τ) - 1‖ ≤ β` on `[0, δ]`,

  `‖M(δ) - δ⁵ Ad_{U(-δ/2)} E₅‖ ≤ δ⁷ B̂₆/7 + δ⁷ ‖ad_H² E₅‖/8 + B̂₄ β δ⁵/5`,

which is the `ρ` of the write-up.  Combined with `theoremD` this gives Theorem D with only the
algebraic identities as hypotheses.
-/

open NormedSpace Finset intervalIntegral MeasureTheory

set_option linter.unusedSectionVars false

namespace Trotter

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]

theorem continuous_prodExp (L : List 𝔸) : Continuous (prodExp L) :=
  continuous_iff_continuousAt.2 fun τ => (hasDerivAt_prodExp L τ).continuousAt

/-- **Step 2 of Theorem D** (the single-step input `ρ`). -/
theorem singleStep_input (H E₅ : 𝔸) (L : List 𝔸) (hH : ∀ s : ℝ, ‖exp (s • H)‖ ≤ 1)
    (hL : ∀ a ∈ L, ∀ s : ℝ, ‖exp (s • a)‖ ≤ 1)
    (h0 : ∀ r < 4, chainC 0 ((-H) :: L) r = 0)
    (h4 : chainC 0 ((-H) :: L) 4 = (5 : ℝ) • E₅)
    (h5 : chainC 0 ((-H) :: L) 5 = (-3 : ℝ) • ad H E₅)
    {δ β : ℝ} (hδ : 0 ≤ δ) (hβ : ∀ τ ∈ Set.Icc 0 δ, ‖prodExp ((-H) :: L) τ - 1‖ ≤ β) :
    ‖(prodExp ((-H) :: L) δ - 1) - δ ^ 5 • Ad (-H) (δ / 2) E₅‖
      ≤ δ ^ 7 * chainBg 0 ((-H) :: L) 6 / 7 + δ ^ 7 / 8 * ‖ad H (ad H E₅)‖
        + chainBg 0 ((-H) :: L) 4 * β * δ ^ 5 / 5 := by
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
  -- FTC: S δ - 1 = ∫ V S
  have hftc : S δ - 1 = ∫ τ in (0 : ℝ)..δ, V τ * S τ := by
    rw [integral_eq_sub_of_hasDerivAt (fun τ _ => hasDerivAt_prodExp Lh τ)
      ((hVc.mul hSc).intervalIntegrable _ _), prodExp_zero]
  -- the polynomial part P(τ) = 5 τ⁴ E₅ - 3 τ⁵ [H, E₅]
  set P : ℝ → 𝔸 := fun τ => (5 * τ ^ 4) • E₅ + (-3 * τ ^ 5) • ad H E₅
  have hPc : Continuous P :=
    ((continuous_const.mul (continuous_pow 4)).smul continuous_const).add
      ((continuous_const.mul (continuous_pow 5)).smul continuous_const)
  have hsum6 : ∀ τ : ℝ, ∑ r ∈ range 6, τ ^ r • chainC 0 Lh r = P τ := by
    intro τ
    simp only [sum_range_succ, range_zero, sum_empty, h0 0 (by norm_num), h0 1 (by norm_num),
      h0 2 (by norm_num), h0 3 (by norm_num), h4, h5, smul_zero, zero_add, smul_smul, P]
    ring_nf
  have hsum4 : ∀ τ : ℝ, ∑ r ∈ range 4, τ ^ r • chainC 0 Lh r = 0 := by
    intro τ
    simp [sum_range_succ, h0 0 (by norm_num), h0 1 (by norm_num), h0 2 (by norm_num),
      h0 3 (by norm_num)]
  have hR6 : ∀ τ ∈ Set.Icc 0 δ, ‖V τ - P τ‖ ≤ τ ^ 6 * chainBg 0 Lh 6 := by
    intro τ hτ
    rw [← hsum6 τ]; exact norm_chain_sub_taylor_le_grouped 0 Lh hLh' 6 (by norm_num) hτ.1
  have hV4 : ∀ τ ∈ Set.Icc 0 δ, ‖V τ‖ ≤ τ ^ 4 * chainBg 0 Lh 4 := by
    intro τ hτ
    have := norm_chain_sub_taylor_le_grouped 0 Lh hLh' 4 (by norm_num) hτ.1
    rwa [hsum4 τ, sub_zero] at this
  -- ∫ P = δ⁵ E₅ - δ⁶/2 [H,E₅]
  have hintP : ∫ τ in (0 : ℝ)..δ, P τ = δ ^ 5 • E₅ - (δ ^ 6 / 2) • ad H E₅ := by
    simp only [P]
    rw [intervalIntegral.integral_add, intervalIntegral.integral_smul_const,
      intervalIntegral.integral_smul_const, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, integral_pow, integral_pow]
    · simp only [sub_eq_add_neg, ← neg_smul]; congr 1 <;> congr 1 <;> ring
    · exact ((continuous_const.mul (continuous_pow 4)).smul continuous_const).intervalIntegrable _ _
    · exact ((continuous_const.mul (continuous_pow 5)).smul continuous_const).intervalIntegrable _ _
  -- decomposition of M - δ⁵ Ad E₅
  have hAd := norm_Ad_sub_two_le (-H) (contraction_neg H hH) E₅ (u := δ / 2) (by linarith)
  have e2 : ad (-H) (-ad H E₅) = ad H (ad H E₅) := by simp only [ad]; noncomm_ring
  rw [ad_neg, e2] at hAd
  have hsplit : S δ - 1 - δ ^ 5 • Ad (-H) (δ / 2) E₅
      = (∫ τ in (0 : ℝ)..δ, (V τ - P τ)) + (∫ τ in (0 : ℝ)..δ, V τ * (S τ - 1))
        - δ ^ 5 • (Ad (-H) (δ / 2) E₅ - E₅ - (δ / 2) • -ad H E₅) := by
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
    simp only [smul_sub, smul_neg, smul_smul]
    rw [show δ ^ 5 * (δ / 2) = δ ^ 6 / 2 by ring]
    abel
  rw [hsplit]
  have hI1 : ‖∫ τ in (0 : ℝ)..δ, (V τ - P τ)‖ ≤ δ ^ 7 * chainBg 0 Lh 6 / 7 := by
    refine (intervalIntegral.norm_integral_le_integral_norm hδ).trans ?_
    calc ∫ τ in (0 : ℝ)..δ, ‖V τ - P τ‖ ≤ ∫ τ in (0 : ℝ)..δ, τ ^ 6 * chainBg 0 Lh 6 :=
          integral_mono_on hδ ((hVc.sub hPc).norm.intervalIntegrable _ _)
            (((continuous_pow 6).mul continuous_const).intervalIntegrable _ _) hR6
      _ = δ ^ 7 * chainBg 0 Lh 6 / 7 := by
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
  have hI3 : ‖δ ^ 5 • (Ad (-H) (δ / 2) E₅ - E₅ - (δ / 2) • -ad H E₅)‖
      ≤ δ ^ 7 / 8 * ‖ad H (ad H E₅)‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hδ 5)]
    calc δ ^ 5 * ‖Ad (-H) (δ / 2) E₅ - E₅ - (δ / 2) • -ad H E₅‖
        ≤ δ ^ 5 * ((δ / 2) ^ 2 / 2 * ‖ad H (ad H E₅)‖) := by gcongr
      _ = δ ^ 7 / 8 * ‖ad H (ad H E₅)‖ := by ring
  calc ‖(∫ τ in (0 : ℝ)..δ, (V τ - P τ)) + (∫ τ in (0 : ℝ)..δ, V τ * (S τ - 1))
        - δ ^ 5 • (Ad (-H) (δ / 2) E₅ - E₅ - (δ / 2) • -ad H E₅)‖
      ≤ ‖∫ τ in (0 : ℝ)..δ, (V τ - P τ)‖ + ‖∫ τ in (0 : ℝ)..δ, V τ * (S τ - 1)‖
        + ‖δ ^ 5 • (Ad (-H) (δ / 2) E₅ - E₅ - (δ / 2) • -ad H E₅)‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := by linarith

/-- **Theorem D end to end**: from the algebraic identities only (Taylor coefficients of `Ŝ` and
`E₅ = [H,Y] + Z`) to the many-step bound. -/
theorem theoremD_full (H E₅ Y Z : 𝔸) (L : List 𝔸) (hH : ∀ s : ℝ, ‖exp (s • H)‖ ≤ 1)
    (hL : ∀ a ∈ L, ∀ s : ℝ, ‖exp (s • a)‖ ≤ 1)
    (h0 : ∀ r < 4, chainC 0 ((-H) :: L) r = 0)
    (h4 : chainC 0 ((-H) :: L) 4 = (5 : ℝ) • E₅)
    (h5 : chainC 0 ((-H) :: L) 5 = (-3 : ℝ) • ad H E₅) (hE : E₅ = ad H Y + Z)
    {δ β : ℝ} (hδ : 0 ≤ δ) (hβ : ∀ τ ∈ Set.Icc 0 δ, ‖prodExp ((-H) :: L) τ - 1‖ ≤ β) (r : ℕ) :
    ‖prodExp L δ ^ r - exp (δ • H) ^ r‖
      ≤ δ ^ 5 * (r * ‖Z‖) + δ ^ 4 * (2 * ‖Y‖) + r * (δ ^ 7 / 24 * ‖ad H (ad H (ad H Y))‖)
        + r * (δ ^ 7 * chainBg 0 ((-H) :: L) 6 / 7 + δ ^ 7 / 8 * ‖ad H (ad H E₅)‖
          + chainBg 0 ((-H) :: L) 4 * β * δ ^ 5 / 5)
        + ‖prodExp L δ - exp (δ • H)‖ ^ 2 * (r * (r - 1) / 2 : ℝ) := by
  have hρ := singleStep_input H E₅ L hH hL h0 h4 h5 hδ hβ
  simp only [prodExp] at hρ
  have hS : ∀ k, ‖prodExp L δ ^ k‖ ≤ 1 := by
    intro k
    rcases k with _ | k
    · simp
    · exact (norm_pow_le' _ (Nat.succ_pos k)).trans
        (pow_le_one₀ (norm_nonneg _) (norm_prodExp_le L hL δ))
  exact theoremD H hH hδ r (prodExp L δ) hS E₅ Y Z hE _ hρ

end Trotter
