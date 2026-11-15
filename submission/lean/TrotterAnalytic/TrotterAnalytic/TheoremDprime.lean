import TrotterAnalytic.TheoremD
import TrotterAnalytic.Midpoint2

/-!
# Theorem D′ (second-order processing), reduced to its single-step input

Hypotheses: `E₅ = [H,Y] + Z`, `W₇ = [H,Y₇] + Z₇` (exact Lie identities, computed in exact arithmetic)
and the single-step estimate `‖M - δ⁵ Ad_{U(-δ/2)} E₅ - δ⁷ Ad_{U(-δ/2)} W₇‖ ≤ ρ₈`.

Conclusion (Theorem D′ of the write-up, with `c₅ = 1/1920 + 1/576`):

  `‖S^r - U^r‖ ≤ δ⁵ r‖Z‖ + δ⁴(2‖Y‖ + δ²‖ad_H²Y‖/12 + r δ⁵ c₅ ‖ad_H⁵Y‖)`
  `           + δ⁷ r‖Z₇‖ + δ⁶(2‖Y₇‖ + r δ³‖ad_H³Y₇‖/24) + r ρ₈ + ‖S-U‖² r(r-1)/2`.
-/

open NormedSpace Finset

set_option linter.unusedSectionVars false

namespace Trotter

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- Midpoint sum of an element `[H,Y] + Z`, given a bound on the `[H,Y]` part. -/
theorem midsum_split (H Y Z : 𝔸) (hneg : ∀ s : ℝ, ‖exp (s • (-H))‖ ≤ 1) {δ : ℝ} (hδ : 0 ≤ δ)
    (r : ℕ) (Bd : ℝ)
    (hB : ‖∑ j ∈ range r, δ • Ad (-H) ((j + 1 / 2 : ℝ) * δ) (ad (-H) Y)‖ ≤ Bd) :
    δ * ‖∑ j ∈ range r, Ad (-H) ((j + 1 / 2 : ℝ) * δ) (ad H Y + Z)‖ ≤ Bd + δ * (r * ‖Z‖) := by
  have hE' : ∀ τ, Ad (-H) τ (ad H Y + Z) = -Ad (-H) τ (ad (-H) Y) + Ad (-H) τ Z := by
    intro τ; rw [Ad_add_arg, ad_neg, Ad_neg_arg, neg_neg]
  simp only [hE', sum_add_distrib, sum_neg_distrib]
  have hZ : ‖∑ j ∈ range r, Ad (-H) ((j + 1 / 2 : ℝ) * δ) Z‖ ≤ r * ‖Z‖ := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ j ∈ range r, ‖Ad (-H) ((j + 1 / 2 : ℝ) * δ) Z‖ ≤ ∑ _j ∈ range r, ‖Z‖ :=
          sum_le_sum fun j _ => norm_Ad_le (-H) hneg _ _
      _ = r * ‖Z‖ := by simp
  have e : ‖∑ j ∈ range r, δ • Ad (-H) ((j + 1 / 2 : ℝ) * δ) (ad (-H) Y)‖
      = δ * ‖∑ j ∈ range r, Ad (-H) ((j + 1 / 2 : ℝ) * δ) (ad (-H) Y)‖ := by
    rw [← smul_sum, norm_smul, Real.norm_eq_abs, abs_of_nonneg hδ]
  calc δ * ‖-∑ j ∈ range r, Ad (-H) ((j + 1 / 2 : ℝ) * δ) (ad (-H) Y)
          + ∑ j ∈ range r, Ad (-H) ((j + 1 / 2 : ℝ) * δ) Z‖
      ≤ δ * (‖∑ j ∈ range r, Ad (-H) ((j + 1 / 2 : ℝ) * δ) (ad (-H) Y)‖
          + ‖∑ j ∈ range r, Ad (-H) ((j + 1 / 2 : ℝ) * δ) Z‖) := by
        gcongr; exact (norm_add_le _ _).trans (by rw [norm_neg])
    _ ≤ Bd + δ * (r * ‖Z‖) := by rw [mul_add, ← e]; gcongr

/-- **Theorem D′** (reduction to the single-step estimate). -/
theorem theoremDprime (H : 𝔸) (hH : ∀ s : ℝ, ‖exp (s • H)‖ ≤ 1) {δ : ℝ} (hδ : 0 ≤ δ) (r : ℕ)
    (S : 𝔸) (hS : ∀ k, ‖S ^ k‖ ≤ 1) (E₅ Y Z W₇ Y₇ Z₇ : 𝔸) (hE : E₅ = ad H Y + Z)
    (hW : W₇ = ad H Y₇ + Z₇) (ρ : ℝ)
    (hρ : ‖(exp (δ • (-H)) * S - 1) - δ ^ 5 • Ad (-H) (δ / 2) E₅ - δ ^ 7 • Ad (-H) (δ / 2) W₇‖ ≤ ρ) :
    ‖S ^ r - exp (δ • H) ^ r‖
      ≤ δ ^ 5 * (r * ‖Z‖) + δ ^ 4 * (2 * ‖Y‖ + δ ^ 2 / 12 * ‖ad H (ad H Y)‖
          + r * (δ ^ 5 * (1 / 1920 + 1 / 576) * ‖ad H (ad H (ad H (ad H (ad H Y))))‖))
        + δ ^ 7 * (r * ‖Z₇‖) + δ ^ 6 * (2 * ‖Y₇‖ + r * (δ ^ 3 / 24 * ‖ad H (ad H (ad H Y₇))‖))
        + r * ρ + ‖S - exp (δ • H)‖ ^ 2 * (r * (r - 1) / 2 : ℝ) := by
  set U := exp (δ • H) with hU
  set M := exp (δ • (-H)) * S - 1 with hM
  clear_value U M
  have hneg : ∀ s : ℝ, ‖exp (s • (-H))‖ ≤ 1 := contraction_neg H hH
  have hUk : ∀ k, ‖U ^ k‖ ≤ 1 := fun k => by rw [hU, exp_nsmul_smul]; exact hH _
  have hSU : S - U = U * M := by
    rw [hM, mul_sub, ← mul_assoc, hU, exp_smul_mul_exp_smul_neg, one_mul, mul_one]
  have hterm : ∀ j ∈ range r, U ^ (r - 1 - j) * (S - U) * U ^ j
      = U ^ r * Ad (-H) ((j : ℝ) * δ) M := by
    intro j hj
    have hjr : j < r := mem_range.mp hj
    have e1 : U ^ (r - 1 - j) * U = U ^ (r - j) := by rw [← pow_succ]; congr 1; omega
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
  set R := M - δ ^ 5 • Ad (-H) (δ / 2) E₅ - δ ^ 7 • Ad (-H) (δ / 2) W₇ with hR
  have hsplit : ∑ j ∈ range r, Ad (-H) ((j : ℝ) * δ) M
      = ∑ j ∈ range r, Ad (-H) ((j : ℝ) * δ) R
        + δ ^ 5 • ∑ j ∈ range r, Ad (-H) ((j + 1 / 2 : ℝ) * δ) E₅
        + δ ^ 7 • ∑ j ∈ range r, Ad (-H) ((j + 1 / 2 : ℝ) * δ) W₇ := by
    rw [smul_sum, smul_sum, ← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl; intro j _
    have hm : (j : ℝ) * δ + δ / 2 = (j + 1 / 2 : ℝ) * δ := by ring
    rw [hR, Ad_sub_arg, Ad_sub_arg, Ad_smul_arg, Ad_smul_arg, ← Ad_add, ← Ad_add, hm]
    abel
  -- first telescoping (Euler–Maclaurin corrected)
  have hm2 := norm_sum_midpoint2_le (-H) hneg Y hδ r
  have n2 : ‖ad (-H) (ad (-H) Y)‖ = ‖ad H (ad H Y)‖ := by
    rw [show ad (-H) (ad (-H) Y) = ad H (ad H Y) by simp only [ad]; noncomm_ring]
  have n5 : ‖ad (-H) (ad (-H) (ad (-H) (ad (-H) (ad (-H) Y))))‖
      = ‖ad H (ad H (ad H (ad H (ad H Y))))‖ := by
    rw [show ad (-H) (ad (-H) (ad (-H) (ad (-H) (ad (-H) Y))))
        = -ad H (ad H (ad H (ad H (ad H Y)))) by simp only [ad]; noncomm_ring, norm_neg]
  rw [n2, n5] at hm2
  have hE5 := midsum_split H Y Z hneg hδ r _ hm2
  rw [← hE] at hE5
  -- second telescoping (first order)
  have hm1 := norm_sum_midpoint_le (-H) hneg Y₇ hδ r
  have n3 : ‖ad (-H) (ad (-H) (ad (-H) Y₇))‖ = ‖ad H (ad H (ad H Y₇))‖ := by
    rw [show ad (-H) (ad (-H) (ad (-H) Y₇)) = -ad H (ad H (ad H Y₇)) by simp only [ad]; noncomm_ring,
      norm_neg]
  rw [n3] at hm1
  have hW7 := midsum_split H Y₇ Z₇ hneg hδ r _ hm1
  rw [← hW] at hW7
  have hrest : ‖∑ j ∈ range r, Ad (-H) ((j : ℝ) * δ) R‖ ≤ r * ρ := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ j ∈ range r, ‖Ad (-H) ((j : ℝ) * δ) R‖ ≤ ∑ _j ∈ range r, ρ :=
          sum_le_sum fun j _ => (norm_Ad_le (-H) hneg _ _).trans hρ
      _ = r * ρ := by simp
  set SE := ∑ j ∈ range r, Ad (-H) ((j + 1 / 2 : ℝ) * δ) E₅
  set SW := ∑ j ∈ range r, Ad (-H) ((j + 1 / 2 : ℝ) * δ) W₇
  have hd5 : δ ^ 5 * ‖SE‖ ≤ δ ^ 5 * (r * ‖Z‖) + δ ^ 4 * (2 * ‖Y‖ + δ ^ 2 / 12 * ‖ad H (ad H Y)‖
          + r * (δ ^ 5 * (1 / 1920 + 1 / 576) * ‖ad H (ad H (ad H (ad H (ad H Y))))‖)) := by
    have := mul_le_mul_of_nonneg_left hE5 (pow_nonneg hδ 4)
    calc δ ^ 5 * ‖SE‖ = δ ^ 4 * (δ * ‖SE‖) := by ring
      _ ≤ _ := this
      _ = _ := by ring
  have hd7 : δ ^ 7 * ‖SW‖ ≤ δ ^ 7 * (r * ‖Z₇‖)
      + δ ^ 6 * (2 * ‖Y₇‖ + r * (δ ^ 3 / 24 * ‖ad H (ad H (ad H Y₇))‖)) := by
    have := mul_le_mul_of_nonneg_left hW7 (pow_nonneg hδ 6)
    calc δ ^ 7 * ‖SW‖ = δ ^ 6 * (δ * ‖SW‖) := by ring
      _ ≤ _ := this
      _ = _ := by ring
  have hcoh : ‖∑ j ∈ range r, U ^ (r - 1 - j) * (S - U) * U ^ j‖
      ≤ r * ρ + δ ^ 5 * ‖SE‖ + δ ^ 7 * ‖SW‖ := by
    rw [hC, hsplit]
    calc ‖U ^ r * (∑ j ∈ range r, Ad (-H) ((j : ℝ) * δ) R + δ ^ 5 • SE + δ ^ 7 • SW)‖
        ≤ ‖U ^ r‖ * ‖∑ j ∈ range r, Ad (-H) ((j : ℝ) * δ) R + δ ^ 5 • SE + δ ^ 7 • SW‖ :=
          norm_mul_le _ _
      _ ≤ 1 * (r * ρ + δ ^ 5 * ‖SE‖ + δ ^ 7 * ‖SW‖) := by
          gcongr
          · exact hUk r
          · refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
              (add_le_add hrest (le_of_eq ?_))) (le_of_eq ?_))
            · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
            · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      _ = _ := one_mul _
  have h1 := norm_pow_sub_pow_sub_coherent_le S U hS hUk r
  calc ‖S ^ r - U ^ r‖
      ≤ ‖S ^ r - U ^ r - ∑ j ∈ range r, U ^ (r - 1 - j) * (S - U) * U ^ j‖
        + ‖∑ j ∈ range r, U ^ (r - 1 - j) * (S - U) * U ^ j‖ := norm_le_norm_sub_add _ _
    _ ≤ _ := by linarith

end Trotter
