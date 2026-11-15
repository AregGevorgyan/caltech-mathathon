import Mathlib

/-!
# Many-step telescoping (Theorem D, Step 1)

In any (noncommutative) ring,
  `S^r - U^r = ∑_{j<r} U^(r-1-j) * (S - U) * S^j`,
and in a normed ring with power-bounded `S`, `U` (e.g. unitaries) this gives
  `‖S^r - U^r‖ ≤ r ‖S - U‖`   and the second-order refinement
  `‖S^r - U^r - ∑_{j<r} U^(r-1-j) (S-U) U^j‖ ≤ ‖S - U‖² · r(r-1)/2`,
which is Step 1 of Theorem D (the first sum is the coherent part that is then telescoped
further through `E₅ = [H,Y] + Z`).
-/

open Finset

namespace Trotter

variable {R : Type*}

section Ring
variable [Ring R]

/-- The same identity with the "exact" propagator on the left:
`S^r - U^r = ∑ U^(r-1-j) (S-U) S^j`. -/
theorem pow_sub_pow_eq_sum' (S U : R) : ∀ r : ℕ,
    S ^ r - U ^ r = ∑ j ∈ range r, U ^ (r - 1 - j) * (S - U) * S ^ j
  | 0 => by simp
  | r + 1 => by
    have h : S ^ (r + 1) - U ^ (r + 1) = U * (S ^ r - U ^ r) + (S - U) * S ^ r := by
      simp only [pow_succ']; noncomm_ring
    rw [h, pow_sub_pow_eq_sum' S U r, mul_sum, sum_range_succ]
    congr 1
    · apply sum_congr rfl
      intro j hj
      have := mem_range.mp hj
      have e : r + 1 - 1 - j = (r - 1 - j) + 1 := by omega
      rw [e, pow_succ', mul_assoc, mul_assoc, mul_assoc]
    · simp

end Ring

section Normed
variable [NormedRing R]

/-- First-order telescoping bound: `‖S^r - U^r‖ ≤ r ‖S - U‖` for power-bounded `S`, `U`. -/
theorem norm_pow_sub_pow_le (S U : R) (hS : ∀ k, ‖S ^ k‖ ≤ 1) (hU : ∀ k, ‖U ^ k‖ ≤ 1)
    (r : ℕ) : ‖S ^ r - U ^ r‖ ≤ r * ‖S - U‖ := by
  rw [pow_sub_pow_eq_sum' S U r]
  calc ‖∑ j ∈ range r, U ^ (r - 1 - j) * (S - U) * S ^ j‖
      ≤ ∑ j ∈ range r, ‖U ^ (r - 1 - j) * (S - U) * S ^ j‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ range r, ‖S - U‖ := by
        apply sum_le_sum; intro j _
        calc ‖U ^ (r - 1 - j) * (S - U) * S ^ j‖
            ≤ ‖U ^ (r - 1 - j)‖ * ‖S - U‖ * ‖S ^ j‖ := by
              refine (norm_mul_le _ _).trans ?_
              gcongr; exact norm_mul_le _ _
          _ ≤ 1 * ‖S - U‖ * 1 := by
              gcongr
              · exact hU _
              · exact hS _
          _ = ‖S - U‖ := by ring
    _ = r * ‖S - U‖ := by simp

/-- Second-order telescoping (Theorem D, Step 1):
`‖S^r - U^r - ∑_{j<r} U^(r-1-j) (S-U) U^j‖ ≤ ‖S-U‖² r(r-1)/2`. -/
theorem norm_pow_sub_pow_sub_coherent_le (S U : R) (hS : ∀ k, ‖S ^ k‖ ≤ 1)
    (hU : ∀ k, ‖U ^ k‖ ≤ 1) (r : ℕ) :
    ‖S ^ r - U ^ r - ∑ j ∈ range r, U ^ (r - 1 - j) * (S - U) * U ^ j‖
      ≤ ‖S - U‖ ^ 2 * (r * (r - 1) / 2 : ℝ) := by
  rw [pow_sub_pow_eq_sum' S U r, ← sum_sub_distrib]
  have key : ∀ j ∈ range r, ‖U ^ (r - 1 - j) * (S - U) * S ^ j - U ^ (r - 1 - j) * (S - U) * U ^ j‖
      ≤ ‖S - U‖ ^ 2 * j := by
    intro j _
    rw [← mul_sub]
    calc ‖U ^ (r - 1 - j) * (S - U) * (S ^ j - U ^ j)‖
        ≤ ‖U ^ (r - 1 - j)‖ * ‖S - U‖ * ‖S ^ j - U ^ j‖ := by
          refine (norm_mul_le _ _).trans ?_
          gcongr; exact norm_mul_le _ _
      _ ≤ 1 * ‖S - U‖ * (j * ‖S - U‖) := by
          gcongr
          · exact hU _
          · exact norm_pow_sub_pow_le S U hS hU j
      _ = ‖S - U‖ ^ 2 * j := by ring
  calc ‖∑ j ∈ range r, (U ^ (r - 1 - j) * (S - U) * S ^ j - U ^ (r - 1 - j) * (S - U) * U ^ j)‖
      ≤ ∑ j ∈ range r, ‖U ^ (r - 1 - j) * (S - U) * S ^ j - U ^ (r - 1 - j) * (S - U) * U ^ j‖ :=
        norm_sum_le _ _
    _ ≤ ∑ j ∈ range r, ‖S - U‖ ^ 2 * (j : ℝ) := sum_le_sum key
    _ = ‖S - U‖ ^ 2 * (r * (r - 1) / 2 : ℝ) := by
        rw [← mul_sum]
        congr 1
        have := sum_range_id_mul_two r
        have h2 : (∑ j ∈ range r, (j : ℝ)) * 2 = r * (r - 1) := by
          have : ((∑ j ∈ range r, j : ℕ) : ℝ) * 2 = ((r * (r - 1) : ℕ) : ℝ) := by
            rw [← this]; push_cast; ring
          rcases r with _ | r
          · simp
          · push_cast at this ⊢; simpa using this
        linarith

end Normed

end Trotter
