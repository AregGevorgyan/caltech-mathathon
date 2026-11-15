import TrotterAnalytic.ChainGrouped
import TrotterAnalytic.Midpoint

/-!
# General split point `S = L R` (Lemma 2 for any `m`) and the single-step theorem

Stages are split into a left list `Lst` (first `m` stages) and a right list `Rst`.  With
`negrev Lst = (Lst.map (-·)).reverse` (the left stages reversed, with negated generators):

* `prodExp (negrev Lst)` is the inverse of `prodExp Lst`;
* **key identity:** `chainV W (negrev Lst) τ = L⁻¹ (W - V_L) L` for every `W`, where `V_L = chainV 0 Lst τ`;
* **Lemma 2:** `S' - H S = L T R` with `T(τ) = chainV 0 Rst τ - chainV H (negrev Lst) τ`
  (right chain with terminal `0`, left chain reversed/negated with terminal `H`, exactly as in the
  write-up and in `trotter/splitbound.py`).

With Lemma 1 (split form) and Lemma 3′ for both chains this gives the single-step theorem for any
split, i.e. the analytic content of Theorems B (`m = 3`) and C (`m = 2`).
-/

open NormedSpace Finset intervalIntegral

set_option linter.unusedSectionVars false

namespace Trotter

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]

/-- Reversed list of negated generators. -/
def negrev (L : List 𝔸) : List 𝔸 := (L.map (fun a => -a)).reverse

theorem negrev_cons (a : 𝔸) (L : List 𝔸) : negrev (a :: L) = negrev L ++ [-a] := by
  simp [negrev]

theorem prodExp_append (τ : ℝ) : ∀ l₁ l₂ : List 𝔸, prodExp (l₁ ++ l₂) τ = prodExp l₁ τ * prodExp l₂ τ
  | [], l₂ => by simp [prodExp]
  | a :: l₁, l₂ => by simp [prodExp, prodExp_append τ l₁ l₂, mul_assoc]

theorem chainV_append (τ : ℝ) (W : 𝔸) : ∀ l₁ l₂ : List 𝔸,
    chainV W (l₁ ++ l₂) τ = chainV (chainV W l₂ τ) l₁ τ
  | [], l₂ => by simp [chainV]
  | a :: l₁, l₂ => by simp [chainV, chainV_append τ W l₁ l₂]

theorem exp_neg_mul_exp (a : 𝔸) (τ : ℝ) : exp (τ • (-a)) * exp (τ • a) = 1 := by
  have := exp_smul_mul_exp_smul_neg (-a) τ; rwa [neg_neg] at this

theorem prodExp_negrev_mul (τ : ℝ) : ∀ L : List 𝔸, prodExp (negrev L) τ * prodExp L τ = 1
  | [] => by simp [negrev, prodExp]
  | a :: L => by
    rw [negrev_cons, prodExp_append]
    simp only [prodExp, mul_one]
    calc prodExp (negrev L) τ * exp (τ • -a) * (exp (τ • a) * prodExp L τ)
        = prodExp (negrev L) τ * (exp (τ • -a) * exp (τ • a)) * prodExp L τ := by
          simp only [mul_assoc]
      _ = 1 := by rw [exp_neg_mul_exp, mul_one, prodExp_negrev_mul τ L]

theorem mul_prodExp_negrev (τ : ℝ) : ∀ L : List 𝔸, prodExp L τ * prodExp (negrev L) τ = 1
  | [] => by simp [negrev, prodExp]
  | a :: L => by
    rw [negrev_cons, prodExp_append]
    simp only [prodExp, mul_one]
    calc exp (τ • a) * prodExp L τ * (prodExp (negrev L) τ * exp (τ • -a))
        = exp (τ • a) * (prodExp L τ * prodExp (negrev L) τ) * exp (τ • -a) := by
          simp only [mul_assoc]
      _ = 1 := by rw [mul_prodExp_negrev τ L, mul_one, exp_smul_mul_exp_smul_neg]

theorem exp_neg_conj_self (a : 𝔸) (τ : ℝ) : exp (τ • (-a)) * a * exp (τ • a) = a := by
  rw [mul_assoc, ← exp_smul_comm a τ, ← mul_assoc, exp_neg_mul_exp, one_mul]

/-- **Key identity:** the reversed/negated left chain is the conjugated left defect. -/
theorem chainV_negrev (τ : ℝ) : ∀ (L : List 𝔸) (W : 𝔸),
    chainV W (negrev L) τ = prodExp (negrev L) τ * (W - chainV 0 L τ) * prodExp L τ
  | [], W => by simp [negrev, chainV, prodExp]
  | a :: L, W => by
    rw [negrev_cons, chainV_append]
    have hW : chainV W [-a] τ = -a + Ad (-a) τ W := by simp [chainV]
    rw [hW, chainV_negrev τ L, prodExp_append]
    simp only [prodExp, chainV, mul_one, Ad, neg_neg]
    -- L⁻¹ (W - (a + e^{τa} V e^{-τa})) L  with L = e^{τa} L', L⁻¹ = L'⁻¹ e^{-τa}
    have e1 : exp (τ • -a) * (W - (a + exp (τ • a) * chainV 0 L τ * exp (τ • -a))) * exp (τ • a)
        = (-a + exp (τ • -a) * W * exp (τ • a)) - chainV 0 L τ := by
      have h1 := exp_neg_conj_self a τ
      have h2 : exp (τ • -a) * (exp (τ • a) * chainV 0 L τ * exp (τ • -a)) * exp (τ • a)
          = chainV 0 L τ := by
        calc exp (τ • -a) * (exp (τ • a) * chainV 0 L τ * exp (τ • -a)) * exp (τ • a)
            = (exp (τ • -a) * exp (τ • a)) * chainV 0 L τ * (exp (τ • -a) * exp (τ • a)) := by
              simp only [mul_assoc]
          _ = chainV 0 L τ := by rw [exp_neg_mul_exp, one_mul, mul_one]
      calc exp (τ • -a) * (W - (a + exp (τ • a) * chainV 0 L τ * exp (τ • -a))) * exp (τ • a)
          = exp (τ • -a) * W * exp (τ • a) - exp (τ • -a) * a * exp (τ • a)
            - exp (τ • -a) * (exp (τ • a) * chainV 0 L τ * exp (τ • -a)) * exp (τ • a) := by
            noncomm_ring
        _ = _ := by rw [h1, h2]; abel
    calc prodExp (negrev L) τ * (-a + exp (τ • -a) * W * exp (τ • a) - chainV 0 L τ) * prodExp L τ
        = prodExp (negrev L) τ * (exp (τ • -a) * (W - (a + exp (τ • a) * chainV 0 L τ *
            exp (τ • -a))) * exp (τ • a)) * prodExp L τ := by rw [e1]
      _ = _ := by simp only [mul_assoc]

/-- The split defect `T(τ)`. -/
noncomputable def splitT (H : 𝔸) (Lst Rst : List 𝔸) (τ : ℝ) : 𝔸 :=
  chainV 0 Rst τ - chainV H (negrev Lst) τ

/-- **Lemma 2 (general split):** `S' = H S + L T R`. -/
theorem hasDerivAt_split (H : 𝔸) (Lst Rst : List 𝔸) (τ : ℝ) :
    HasDerivAt (fun τ => prodExp Lst τ * prodExp Rst τ)
      (H * (prodExp Lst τ * prodExp Rst τ) + prodExp Lst τ * splitT H Lst Rst τ * prodExp Rst τ) τ := by
  have h := (hasDerivAt_prodExp Lst τ).mul (hasDerivAt_prodExp Rst τ)
  refine h.congr_deriv ?_
  have hinv := mul_prodExp_negrev τ Lst
  have hinv' := prodExp_negrev_mul τ Lst
  simp only [splitT, chainV_negrev]
  set Lm := prodExp Lst τ
  set Li := prodExp (negrev Lst) τ
  set Rm := prodExp Rst τ
  set VL := chainV 0 Lst τ
  set VR := chainV 0 Rst τ
  -- V_L L R + L V_R R = H L R + L (V_R - L⁻¹(H - V_L)L) R
  have : Lm * (Li * (H - VL) * Lm) * Rm = (H - VL) * Lm * Rm := by
    calc Lm * (Li * (H - VL) * Lm) * Rm = (Lm * Li) * (H - VL) * Lm * Rm := by simp only [mul_assoc]
      _ = (H - VL) * Lm * Rm := by rw [hinv, one_mul]
  calc VL * Lm * Rm + Lm * (VR * Rm)
      = H * (Lm * Rm) + (Lm * VR * Rm - (H - VL) * Lm * Rm) := by noncomm_ring
    _ = H * (Lm * Rm) + Lm * (VR - Li * (H - VL) * Lm) * Rm := by rw [← this]; noncomm_ring

/-- **Single-step theorem, general split** (Lemmas 1, 2, 3′). -/
theorem norm_split_sub_exp_le (Lst Rst : List 𝔸)
    (hL : ∀ a ∈ Lst, ∀ s : ℝ, ‖exp (s • a)‖ ≤ 1) (hR : ∀ a ∈ Rst, ∀ s : ℝ, ‖exp (s • a)‖ ≤ 1)
    (H : 𝔸) (hH : ∀ s : ℝ, ‖exp (s • H)‖ ≤ 1) (K : ℕ) (hK : 1 ≤ K) {t : ℝ} (ht : 0 ≤ t) :
    ‖prodExp Lst t * prodExp Rst t - exp (t • H)‖
      ≤ ∑ r ∈ range K, ‖chainC 0 Rst r - chainC H (negrev Lst) r‖ * (t ^ (r + 1) / (r + 1))
        + (chainBg 0 Rst K + chainBg H (negrev Lst) K) * (t ^ (K + 1) / (K + 1)) := by
  have hLn : ∀ a ∈ negrev Lst, ∀ s : ℝ, ‖exp (s • a)‖ ≤ 1 := by
    intro a ha s
    simp only [negrev, List.mem_reverse, List.mem_map] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    exact contraction_neg b (hL b hb) s
  have hTc : Continuous (splitT H Lst Rst) :=
    (continuous_chainV 0 Rst).sub (continuous_chainV H (negrev Lst))
  have hLc : Continuous (prodExp Lst) :=
    continuous_iff_continuousAt.2 fun τ => (hasDerivAt_prodExp Lst τ).continuousAt
  have hRc : Continuous (prodExp Rst) :=
    continuous_iff_continuousAt.2 fun τ => (hasDerivAt_prodExp Rst τ).continuousAt
  have h1 := norm_sub_exp_le_integral_split H hH (fun τ => prodExp Lst τ * prodExp Rst τ)
    (prodExp Lst) (splitT H Lst Rst) (prodExp Rst) (hasDerivAt_split H Lst Rst)
    ((hLc.mul hTc).mul hRc) hTc (norm_prodExp_le Lst hL) (norm_prodExp_le Rst hR)
    (by simp [prodExp_zero]) ht
  refine h1.trans ((integral_le_of_poly_bound (splitT H Lst Rst) hTc ht (range (K + 1))
    (fun r => if r < K then ‖chainC 0 Rst r - chainC H (negrev Lst) r‖
      else chainBg 0 Rst K + chainBg H (negrev Lst) K) ?_).trans ?_)
  · intro τ hτ
    have hτ0 := hτ.1
    have hR' := norm_chain_sub_taylor_le_grouped (0 : 𝔸) Rst hR K hK hτ0
    have hL' := norm_chain_sub_taylor_le_grouped H (negrev Lst) hLn K hK hτ0
    calc ‖splitT H Lst Rst τ‖
        = ‖(chainV 0 Rst τ - ∑ r ∈ range K, τ ^ r • chainC 0 Rst r)
            - (chainV H (negrev Lst) τ - ∑ r ∈ range K, τ ^ r • chainC H (negrev Lst) r)
            + ∑ r ∈ range K, τ ^ r • (chainC 0 Rst r - chainC H (negrev Lst) r)‖ := by
          congr 1; simp only [splitT, smul_sub, sum_sub_distrib]; abel
      _ ≤ τ ^ K * chainBg 0 Rst K + τ ^ K * chainBg H (negrev Lst) K
            + ∑ r ∈ range K, τ ^ r * ‖chainC 0 Rst r - chainC H (negrev Lst) r‖ := by
          refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add hR' hL')) ?_)
          refine (norm_sum_le _ _).trans (le_of_eq ?_)
          apply sum_congr rfl; intro r _
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hτ0 r)]
      _ = _ := by
          rw [sum_range_succ, if_neg (lt_irrefl K)]
          rw [add_comm]; congr 1
          · apply sum_congr rfl; intro r hr; rw [if_pos (mem_range.mp hr)]; ring
          · ring
  · rw [sum_range_succ, if_neg (lt_irrefl K)]
    apply le_of_eq; congr 1
    apply sum_congr rfl; intro r hr; rw [if_pos (mem_range.mp hr)]

end Trotter
