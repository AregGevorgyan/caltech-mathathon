import TrotterAnalytic.ConjTaylor

/-!
# Lemma 3: Taylor expansion of a chain of conjugations, remainder from the right

A *chain* with generators `a₁, …, aₙ` (each generating a contraction group; in the write-up
`aₛ = gₛ Yₛ` with `Yₛ ∈ {A, B, H}`) and terminal element `Z` is

  `V(τ) = a₁ + Ad_{a₁}(τ) (a₂ + Ad_{a₂}(τ) ( … (aₙ + Ad_{aₙ}(τ) Z)))`.

Both halves of the defect `T(τ)` (Lemma 2) are chains.  Its Taylor coefficients `cᵣ` satisfy
the recursion `c(a::L, r) = [r=0] a + ∑_{k≤r} ad_a^{r-k} c(L, k)/(r-k)!`, and for `K ≥ 1`,
`τ ≥ 0`

  `‖V(τ) - ∑_{r<K} τ^r cᵣ‖ ≤ τ^K ∑ₛ ∑_{j<K} ‖ad_{aₛ}^{K-j} c(tailₛ, j)‖/(K-j)!`,

where `tailₛ` is the chain after position `s`.  Every term is a nested commutator taken
**after** all cancellations inside the tail coefficient `c(tailₛ, j)`, and all conjugations
have dropped out of the norm: this is Lemma 3 of the write-up (with `k = K - j`).
-/

open NormedSpace Finset

set_option linter.unusedSectionVars false

namespace Trotter

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- Value of the chain. -/
noncomputable def chainV (Z : 𝔸) : List 𝔸 → ℝ → 𝔸
  | [], _ => Z
  | a :: L, τ => a + Ad a τ (chainV Z L τ)

/-- Taylor coefficients of the chain (exact recursion). -/
noncomputable def chainC (Z : 𝔸) : List 𝔸 → ℕ → 𝔸
  | [], r => if r = 0 then Z else 0
  | a :: L, r => (if r = 0 then a else 0) +
      ∑ k ∈ range (r + 1), (1 / ((r - k).factorial : ℝ)) • (ad a)^[r - k] (chainC Z L k)

/-- The Lemma 3 remainder constant. -/
noncomputable def chainB (Z : 𝔸) : List 𝔸 → ℕ → ℝ
  | [], _ => 0
  | a :: L, K => chainB Z L K +
      ∑ j ∈ range K, (1 / ((K - j).factorial : ℝ)) * ‖(ad a)^[K - j] (chainC Z L j)‖

theorem sum_ite_zero_smul (K : ℕ) (hK : 1 ≤ K) (τ : ℝ) (X : 𝔸) :
    ∑ r ∈ range K, τ ^ r • (if r = 0 then X else 0) = X := by
  rw [sum_eq_single 0]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (mem_range.mpr (by omega)) h

/-- **Lemma 3 (chain form).** -/
theorem norm_chain_sub_taylor_le (Z : 𝔸) :
    ∀ (L : List 𝔸), (∀ a ∈ L, ∀ s : ℝ, ‖exp (s • a)‖ ≤ 1) →
      ∀ (K : ℕ), 1 ≤ K → ∀ {τ : ℝ}, 0 ≤ τ →
        ‖chainV Z L τ - ∑ r ∈ range K, τ ^ r • chainC Z L r‖ ≤ τ ^ K * chainB Z L K
  | [], _, K, hK, τ, _ => by
    simp only [chainV, chainC, chainB, mul_zero]
    rw [sum_ite_zero_smul K hK τ Z, sub_self, norm_zero]
  | a :: L, hL, K, hK, τ, hτ => by
    have ha : ∀ s : ℝ, ‖exp (s • a)‖ ≤ 1 := hL a (by simp)
    have hL' : ∀ b ∈ L, ∀ s : ℝ, ‖exp (s • b)‖ ≤ 1 := fun b hb => hL b (by simp [hb])
    have ih := norm_chain_sub_taylor_le Z L hL' K hK hτ
    set c : ℕ → 𝔸 := chainC Z L with hc
    set P : 𝔸 := ∑ j ∈ range K, τ ^ j • c j with hP
    set E : 𝔸 := chainV Z L τ - P with hE
    set R : ℕ → 𝔸 := fun j => Ad a τ (c j) - taylorAd a (K - j) (c j) τ with hR
    -- Ad is linear
    have hAdlin : Ad a τ (E + P) = Ad a τ E + ∑ j ∈ range K, τ ^ j • Ad a τ (c j) := by
      simp only [hP, Ad, mul_add, add_mul, mul_sum, sum_mul, mul_smul_comm, smul_mul_assoc]
    -- double sum reindexing
    have hdiag : ∑ j ∈ range K, τ ^ j • taylorAd a (K - j) (c j) τ
        = ∑ m ∈ range K, τ ^ m •
            ∑ k ∈ range (m + 1), (1 / ((m - k).factorial : ℝ)) • (ad a)^[m - k] (c k) := by
      simp only [taylorAd, smul_sum]
      rw [← sum_range_diag_flip K (fun m k => τ ^ m • (τ ^ k / (k.factorial : ℝ)) • (ad a)^[k] (c m))]
      apply sum_congr rfl; intro m _
      apply sum_congr rfl; intro k hk
      have hkm : k ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hk)
      rw [smul_smul, smul_smul]
      congr 1
      rw [div_eq_mul_one_div (τ ^ (m - k)), ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hkm]
    have hexp : chainV Z (a :: L) τ - ∑ r ∈ range K, τ ^ r • chainC Z (a :: L) r
        = Ad a τ E + ∑ j ∈ range K, τ ^ j • R j := by
      have h1 : chainV Z L τ = E + P := by rw [hE]; abel
      simp only [chainV, chainC, smul_add, sum_add_distrib]
      rw [sum_ite_zero_smul K hK τ a, h1, hAdlin]
      rw [← hdiag]
      simp only [hR, smul_sub, sum_sub_distrib]
      abel
    rw [hexp]
    calc ‖Ad a τ E + ∑ j ∈ range K, τ ^ j • R j‖
        ≤ ‖Ad a τ E‖ + ∑ j ∈ range K, ‖τ ^ j • R j‖ :=
          (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
      _ ≤ τ ^ K * chainB Z L K +
            ∑ j ∈ range K, τ ^ K * ((1 / ((K - j).factorial : ℝ)) * ‖(ad a)^[K - j] (c j)‖) := by
          gcongr with j hj
          · exact (norm_Ad_le a ha τ E).trans ih
          · have hjK : j < K := mem_range.mp hj
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hτ j)]
            have := norm_Ad_sub_taylor_le a ha (K - j) (c j) hτ
            calc τ ^ j * ‖R j‖ ≤ τ ^ j * (τ ^ (K - j) / ((K - j).factorial : ℝ) *
                  ‖(ad a)^[K - j] (c j)‖) := by gcongr
              _ = τ ^ K * ((1 / ((K - j).factorial : ℝ)) * ‖(ad a)^[K - j] (c j)‖) := by
                  rw [show τ ^ K = τ ^ j * τ ^ (K - j) by rw [← pow_add]; congr 1; omega]
                  ring
      _ = τ ^ K * chainB Z (a :: L) K := by
          simp only [chainB, mul_add, mul_sum, hc]

end Trotter
