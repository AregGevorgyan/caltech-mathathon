import TrotterAnalytic.SplitFormula
import TrotterAnalytic.TheoremDprime

/-!
# Discharging the contraction hypotheses in a C*-algebra

All analytic theorems assume that generators satisfy `‖exp (s • a)‖ ≤ 1` for real `s`.  In a
(nontrivial) C*-algebra this holds for every skew-adjoint `a` (`a* = -a`, i.e. `a = -i·Hermitian`),
because `exp (s • a)` is unitary.  Products of such exponentials are unitary, so their powers have
norm `1` (the hypothesis `‖S^k‖ ≤ 1` of Theorems D and D′).  This file states the single-step
theorem for skew-adjoint stage generators with no analytic hypotheses left.
-/

open NormedSpace Finset

set_option linter.unusedSectionVars false

namespace Trotter

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [StarRing 𝔸]
  [CStarRing 𝔸] [StarModule ℝ 𝔸] [ContinuousStar 𝔸] [Nontrivial 𝔸]

theorem exp_smul_mem_unitary {a : 𝔸} (ha : a ∈ skewAdjoint 𝔸) (s : ℝ) :
    exp (s • a) ∈ unitary 𝔸 := by
  let +nondep : NormedAlgebra ℚ 𝔸 := .restrictScalars ℚ ℝ 𝔸
  exact exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem s ha)

/-- Skew-adjoint elements generate contraction (indeed unitary) groups. -/
theorem contraction_of_skewAdjoint {a : 𝔸} (ha : a ∈ skewAdjoint 𝔸) (s : ℝ) :
    ‖exp (s • a)‖ ≤ 1 :=
  (CStarRing.norm_of_mem_unitary (exp_smul_mem_unitary ha s)).le

theorem prodExp_mem_unitary (τ : ℝ) :
    ∀ L : List 𝔸, (∀ a ∈ L, a ∈ skewAdjoint 𝔸) → prodExp L τ ∈ unitary 𝔸
  | [], _ => by simp [prodExp, one_mem]
  | a :: L, h => by
    simp only [prodExp]
    exact mul_mem (exp_smul_mem_unitary (h a (by simp)) τ)
      (prodExp_mem_unitary τ L fun b hb => h b (by simp [hb]))

/-- Powers of a product of unitary exponentials have norm `≤ 1`. -/
theorem norm_pow_prodExp_le (τ : ℝ) (L : List 𝔸) (h : ∀ a ∈ L, a ∈ skewAdjoint 𝔸) (k : ℕ) :
    ‖prodExp L τ ^ k‖ ≤ 1 :=
  (CStarRing.norm_of_mem_unitary (pow_mem (prodExp_mem_unitary τ L h) k)).le

/-- **Single-step theorem for skew-adjoint stages** (any split), with no analytic hypotheses. -/
theorem norm_split_sub_exp_le_skewAdjoint (Lst Rst : List 𝔸)
    (hL : ∀ a ∈ Lst, a ∈ skewAdjoint 𝔸) (hR : ∀ a ∈ Rst, a ∈ skewAdjoint 𝔸)
    (H : 𝔸) (hH : H ∈ skewAdjoint 𝔸) (K : ℕ) (hK : 1 ≤ K) {t : ℝ} (ht : 0 ≤ t) :
    ‖prodExp Lst t * prodExp Rst t - exp (t • H)‖
      ≤ ∑ r ∈ range K, ‖chainC 0 Rst r - chainC H (negrev Lst) r‖ * (t ^ (r + 1) / (r + 1))
        + (chainBg 0 Rst K + chainBg H (negrev Lst) K) * (t ^ (K + 1) / (K + 1)) :=
  norm_split_sub_exp_le Lst Rst (fun a ha => contraction_of_skewAdjoint (hL a ha))
    (fun a ha => contraction_of_skewAdjoint (hR a ha)) H (contraction_of_skewAdjoint hH) K hK ht

section Matrices
open scoped Matrix.Norms.L2Operator

/-- **Quantum-circuit instance:** the single-step theorem for anti-Hermitian `(n+1)×(n+1)` complex
matrices with the operator (spectral) norm, i.e. `e^{tA_j} = e^{-it(iA_j)}` unitary gates. -/
theorem matrix_split_sub_exp_le (n : ℕ) (Lst Rst : List (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))
    (hL : ∀ a ∈ Lst, a ∈ skewAdjoint _) (hR : ∀ a ∈ Rst, a ∈ skewAdjoint _)
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hH : H ∈ skewAdjoint _) (K : ℕ) (hK : 1 ≤ K)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖prodExp Lst t * prodExp Rst t - exp (t • H)‖
      ≤ ∑ r ∈ range K, ‖chainC 0 Rst r - chainC H (negrev Lst) r‖ * (t ^ (r + 1) / (r + 1))
        + (chainBg 0 Rst K + chainBg H (negrev Lst) K) * (t ^ (K + 1) / (K + 1)) :=
  norm_split_sub_exp_le_skewAdjoint Lst Rst hL hR H hH K hK ht

end Matrices

end Trotter
