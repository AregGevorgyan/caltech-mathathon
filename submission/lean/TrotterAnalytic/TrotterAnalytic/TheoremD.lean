import TrotterAnalytic.Telescope
import TrotterAnalytic.Duhamel
import TrotterAnalytic.Midpoint

/-!
# Theorem D: the many-step bound, reduced to a single-step estimate

Setting: `H` generates a contraction group (`‖exp (s•H)‖ ≤ 1` for all real `s`), `δ ≥ 0`,
`U = exp (δ•H)` (one exact step), `S` one Trotter step with `‖S^k‖ ≤ 1` (unitary).
Put `M = exp (δ•(-H)) * S - 1`, so `S - U = U M`.  Write `Ad_{U(-s)} X = e^{-sH} X e^{sH}`
(`= Ad (-H) s X`).

Hypotheses (supplied by the exact-arithmetic computation, Step 2 of the write-up):
* `E₅ = [H, Y] + Z` (an exact identity between Lie polynomials, certified in Lean core in
  `lean/S4Leading.lean` for the universal `Y`, `Z`),
* `‖M - δ⁵ Ad_{U(-δ/2)} E₅‖ ≤ ρ`.

Conclusion (Theorem D):
  `‖S^r - U^r‖ ≤ δ⁵ r ‖Z‖ + 2 δ⁴ ‖Y‖ + r δ⁷/24 ‖ad_H³ Y‖ + r ρ + ‖S - U‖² r(r-1)/2`.
The secular term is `T δ⁴ ‖Z‖` (`T = rδ`) instead of `T δ⁴ ‖E₅‖`.
-/

open NormedSpace Finset

set_option linter.unusedSectionVars false

namespace Trotter

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

theorem exp_nsmul_smul (H : 𝔸) (δ : ℝ) (k : ℕ) : exp (δ • H) ^ k = exp (((k : ℝ) * δ) • H) := by
  let +nondep : NormedAlgebra ℚ 𝔸 := .restrictScalars ℚ ℝ 𝔸
  rw [← exp_nsmul, mul_smul, Nat.cast_smul_eq_nsmul]

theorem Ad_add_arg (a : 𝔸) (τ : ℝ) (X W : 𝔸) : Ad a τ (X + W) = Ad a τ X + Ad a τ W := by
  simp only [Ad]; noncomm_ring

theorem Ad_sub_arg (a : 𝔸) (τ : ℝ) (X W : 𝔸) : Ad a τ (X - W) = Ad a τ X - Ad a τ W := by
  simp only [Ad]; noncomm_ring

theorem Ad_neg_arg (a : 𝔸) (τ : ℝ) (X : 𝔸) : Ad a τ (-X) = -Ad a τ X := by
  simp only [Ad]; noncomm_ring

theorem Ad_smul_arg (a : 𝔸) (τ c : ℝ) (X : 𝔸) : Ad a τ (c • X) = c • Ad a τ X := by
  simp only [Ad, mul_smul_comm, smul_mul_assoc]

/-- **Theorem D** (reduction to the single-step estimate). -/
theorem theoremD (H : 𝔸) (hH : ∀ s : ℝ, ‖exp (s • H)‖ ≤ 1) {δ : ℝ} (hδ : 0 ≤ δ) (r : ℕ)
    (S : 𝔸) (hS : ∀ k, ‖S ^ k‖ ≤ 1) (E₅ Y Z : 𝔸) (hE : E₅ = ad H Y + Z) (ρ : ℝ)
    (hρ : ‖(exp (δ • (-H)) * S - 1) - δ ^ 5 • Ad (-H) (δ / 2) E₅‖ ≤ ρ) :
    ‖S ^ r - exp (δ • H) ^ r‖
      ≤ δ ^ 5 * (r * ‖Z‖) + δ ^ 4 * (2 * ‖Y‖) + r * (δ ^ 7 / 24 * ‖ad H (ad H (ad H Y))‖)
        + r * ρ + ‖S - exp (δ • H)‖ ^ 2 * (r * (r - 1) / 2 : ℝ) := by
  set U := exp (δ • H) with hU
  set M := exp (δ • (-H)) * S - 1 with hM
  clear_value U M
  have hneg : ∀ s : ℝ, ‖exp (s • (-H))‖ ≤ 1 := contraction_neg H hH
  have hUk : ∀ k, ‖U ^ k‖ ≤ 1 := fun k => by rw [hU, exp_nsmul_smul]; exact hH _
  -- S - U = U M
  have hSU : S - U = U * M := by
    rw [hM, mul_sub, ← mul_assoc, hU, exp_smul_mul_exp_smul_neg, one_mul, mul_one]
  -- each coherent term is U^r · Ad_{U(-jδ)} M
  have hterm : ∀ j ∈ range r, U ^ (r - 1 - j) * (S - U) * U ^ j
      = U ^ r * Ad (-H) ((j : ℝ) * δ) M := by
    intro j hj
    have hjr : j < r := mem_range.mp hj
    have e1 : U ^ (r - 1 - j) * U = U ^ (r - j) := by
      rw [← pow_succ]; congr 1; omega
    have e2 : U ^ j * exp (((j : ℝ) * δ) • (-H)) = 1 := by
      rw [hU, exp_nsmul_smul, exp_smul_mul_exp_smul_neg]
    have e3 : U ^ r = U ^ (r - j) * U ^ j := (pow_sub_mul_pow U hjr.le).symm
    have e4 : exp (((j : ℝ) * δ) • (- -H)) = U ^ j := by rw [neg_neg, hU, exp_nsmul_smul]
    rw [hSU, Ad, e4]
    calc U ^ (r - 1 - j) * (U * M) * U ^ j = (U ^ (r - 1 - j) * U) * M * U ^ j := by
          simp only [mul_assoc]
      _ = U ^ (r - j) * M * U ^ j := by rw [e1]
      _ = U ^ (r - j) * (U ^ j * exp (((j : ℝ) * δ) • -H)) * M * U ^ j := by rw [e2, mul_one]
      _ = U ^ r * (exp (((j : ℝ) * δ) • -H) * M * U ^ j) := by rw [e3]; simp only [mul_assoc]
  have hC : ∑ j ∈ range r, U ^ (r - 1 - j) * (S - U) * U ^ j
      = U ^ r * ∑ j ∈ range r, Ad (-H) ((j : ℝ) * δ) M := by
    rw [sum_congr rfl hterm, mul_sum]
  -- split M = (M - δ⁵ Ad E₅) + δ⁵ Ad E₅ and the midpoint sum
  have hsplit : ∑ j ∈ range r, Ad (-H) ((j : ℝ) * δ) M
      = ∑ j ∈ range r, Ad (-H) ((j : ℝ) * δ) (M - δ ^ 5 • Ad (-H) (δ / 2) E₅)
        + δ ^ 5 • ∑ j ∈ range r, Ad (-H) ((j + 1 / 2 : ℝ) * δ) E₅ := by
    rw [smul_sum, ← sum_add_distrib]
    apply sum_congr rfl; intro j _
    rw [Ad_sub_arg, Ad_smul_arg, ← Ad_add, show (j : ℝ) * δ + δ / 2 = (j + 1 / 2 : ℝ) * δ by ring]
    abel
  have hE' : ∀ τ, Ad (-H) τ E₅ = -Ad (-H) τ (ad (-H) Y) + Ad (-H) τ Z := by
    intro τ; rw [hE, Ad_add_arg, ad_neg, Ad_neg_arg, neg_neg]
  have hmid := norm_sum_midpoint_le (-H) hneg Y hδ r
  have had3 : ‖ad (-H) (ad (-H) (ad (-H) Y))‖ = ‖ad H (ad H (ad H Y))‖ := by
    rw [show ad (-H) (ad (-H) (ad (-H) Y)) = -ad H (ad H (ad H Y)) by simp only [ad]; noncomm_ring,
      norm_neg]
  rw [had3] at hmid
  -- bound the E₅ midpoint sum
  have hE5sum : δ ^ 5 * ‖∑ j ∈ range r, Ad (-H) ((j + 1 / 2 : ℝ) * δ) E₅‖
      ≤ δ ^ 5 * (r * ‖Z‖) + δ ^ 4 * (2 * ‖Y‖) + r * (δ ^ 7 / 24 * ‖ad H (ad H (ad H Y))‖) := by
    simp only [hE', sum_add_distrib, sum_neg_distrib]
    have hZ : ‖∑ j ∈ range r, Ad (-H) ((j + 1 / 2 : ℝ) * δ) Z‖ ≤ r * ‖Z‖ := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ j ∈ range r, ‖Ad (-H) ((j + 1 / 2 : ℝ) * δ) Z‖ ≤ ∑ _j ∈ range r, ‖Z‖ :=
            sum_le_sum fun j _ => norm_Ad_le (-H) hneg _ _
        _ = r * ‖Z‖ := by simp
    have hY : δ * ‖∑ j ∈ range r, Ad (-H) ((j + 1 / 2 : ℝ) * δ) (ad (-H) Y)‖
        ≤ 2 * ‖Y‖ + r * (δ ^ 3 / 24 * ‖ad H (ad H (ad H Y))‖) := by
      have e : ‖∑ j ∈ range r, δ • Ad (-H) ((j + 1 / 2 : ℝ) * δ) (ad (-H) Y)‖
          = δ * ‖∑ j ∈ range r, Ad (-H) ((j + 1 / 2 : ℝ) * δ) (ad (-H) Y)‖ := by
        rw [← smul_sum, norm_smul, Real.norm_eq_abs, abs_of_nonneg hδ]
      rw [← e]; exact hmid
    calc δ ^ 5 * ‖-∑ j ∈ range r, Ad (-H) ((j + 1 / 2 : ℝ) * δ) (ad (-H) Y)
            + ∑ j ∈ range r, Ad (-H) ((j + 1 / 2 : ℝ) * δ) Z‖
        ≤ δ ^ 5 * (‖∑ j ∈ range r, Ad (-H) ((j + 1 / 2 : ℝ) * δ) (ad (-H) Y)‖
            + ‖∑ j ∈ range r, Ad (-H) ((j + 1 / 2 : ℝ) * δ) Z‖) := by
          gcongr; exact (norm_add_le _ _).trans (by rw [norm_neg])
      _ = δ ^ 4 * (δ * ‖∑ j ∈ range r, Ad (-H) ((j + 1 / 2 : ℝ) * δ) (ad (-H) Y)‖)
            + δ ^ 5 * ‖∑ j ∈ range r, Ad (-H) ((j + 1 / 2 : ℝ) * δ) Z‖ := by ring
      _ ≤ δ ^ 4 * (2 * ‖Y‖ + r * (δ ^ 3 / 24 * ‖ad H (ad H (ad H Y))‖)) + δ ^ 5 * (r * ‖Z‖) := by
          gcongr
      _ = δ ^ 5 * (r * ‖Z‖) + δ ^ 4 * (2 * ‖Y‖) + r * (δ ^ 7 / 24 * ‖ad H (ad H (ad H Y))‖) := by
          ring
  have hrest : ‖∑ j ∈ range r, Ad (-H) ((j : ℝ) * δ) (M - δ ^ 5 • Ad (-H) (δ / 2) E₅)‖ ≤ r * ρ := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ j ∈ range r, ‖Ad (-H) ((j : ℝ) * δ) (M - δ ^ 5 • Ad (-H) (δ / 2) E₅)‖
        ≤ ∑ _j ∈ range r, ρ := sum_le_sum fun j _ => (norm_Ad_le (-H) hneg _ _).trans hρ
      _ = r * ρ := by simp
  have hcoh : ‖∑ j ∈ range r, U ^ (r - 1 - j) * (S - U) * U ^ j‖
      ≤ δ ^ 5 * (r * ‖Z‖) + δ ^ 4 * (2 * ‖Y‖) + r * (δ ^ 7 / 24 * ‖ad H (ad H (ad H Y))‖)
        + r * ρ := by
    rw [hC, hsplit]
    calc ‖U ^ r * (∑ j ∈ range r, Ad (-H) ((j : ℝ) * δ) (M - δ ^ 5 • Ad (-H) (δ / 2) E₅)
            + δ ^ 5 • ∑ j ∈ range r, Ad (-H) ((j + 1 / 2 : ℝ) * δ) E₅)‖
        ≤ ‖U ^ r‖ * ‖∑ j ∈ range r, Ad (-H) ((j : ℝ) * δ) (M - δ ^ 5 • Ad (-H) (δ / 2) E₅)
            + δ ^ 5 • ∑ j ∈ range r, Ad (-H) ((j + 1 / 2 : ℝ) * δ) E₅‖ := norm_mul_le _ _
      _ ≤ 1 * (r * ρ + δ ^ 5 * ‖∑ j ∈ range r, Ad (-H) ((j + 1 / 2 : ℝ) * δ) E₅‖) := by
          gcongr
          · exact hUk r
          · refine (norm_add_le _ _).trans ?_
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
            gcongr
      _ ≤ _ := by linarith
  have h1 := norm_pow_sub_pow_sub_coherent_le S U hS hUk r
  calc ‖S ^ r - U ^ r‖
      ≤ ‖S ^ r - U ^ r - ∑ j ∈ range r, U ^ (r - 1 - j) * (S - U) * U ^ j‖
        + ‖∑ j ∈ range r, U ^ (r - 1 - j) * (S - U) * U ^ j‖ := norm_le_norm_sub_add _ _
    _ ≤ _ := by linarith

end Trotter
