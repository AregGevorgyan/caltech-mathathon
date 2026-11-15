import TrotterAnalytic.Duhamel
import TrotterAnalytic.Chain

/-!
# Single-step bound for an arbitrary product formula (Lemmas 1–3 assembled, split `m = 0`)

Stage generators `a₁, …, aₙ` (in the write-up `aⱼ = cⱼ Xⱼ`, `Xⱼ ∈ {A, B}`), each generating a
contraction group, with `∑ aⱼ = H`.  The product formula is `S(τ) = e^{τa₁} ⋯ e^{τaₙ}`.

* **Lemma 2 (`m = 0`).** `S'(τ) = V(τ) S(τ)`, where `V = a₁ + Ad_{a₁}(a₂ + Ad_{a₂}(…))` is the
  chain with terminal element `0`, so the defect is `S' - H S = (V(τ) - H) S(τ)`.
* With Lemma 1 (Duhamel) and Lemma 3 (chain Taylor remainder):

  `‖S(t) - e^{tH}‖ ≤ ∑_{r<K} ‖cᵣ - [r=0] H‖ t^{r+1}/(r+1) + B_K t^{K+1}/(K+1)`,

  where `cᵣ = chainC 0 L r` are the exact Taylor coefficients of `V` and `B_K = chainB 0 L K`
  the Lemma 3 remainder constant.  For a formula of order `p`, `c₀ = H` and `c₁ = … = c_{p-1} = 0`,
  so only `r ≥ p` contributes (`c₄ = 5E₅` for Suzuki's `S₄`).
-/

open NormedSpace Finset intervalIntegral

set_option linter.unusedSectionVars false

namespace Trotter

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]

/-- The product formula `e^{τa₁} ⋯ e^{τaₙ}`. -/
noncomputable def prodExp : List 𝔸 → ℝ → 𝔸
  | [], _ => 1
  | a :: L, τ => exp (τ • a) * prodExp L τ

theorem exp_smul_comm (a : 𝔸) (τ : ℝ) : exp (τ • a) * a = a * exp (τ • a) := by
  let +nondep : NormedAlgebra ℚ 𝔸 := .restrictScalars ℚ ℝ 𝔸
  exact ((Commute.refl a).smul_left τ).exp_left.eq

theorem Ad_mul_exp (a V : 𝔸) (τ : ℝ) : Ad a τ V * exp (τ • a) = exp (τ • a) * V := by
  have h : exp (τ • (-a)) * exp (τ • a) = 1 := by
    have := exp_smul_mul_exp_smul_neg (-a) τ; rwa [neg_neg] at this
  simp only [Ad, mul_assoc]
  rw [h, mul_one]

/-- **Lemma 2 (`m = 0`)**: `d/dτ prodExp L τ = chainV 0 L τ * prodExp L τ`. -/
theorem hasDerivAt_prodExp : ∀ (L : List 𝔸) (τ : ℝ),
    HasDerivAt (prodExp L) (chainV 0 L τ * prodExp L τ) τ
  | [], τ => by simpa [prodExp, chainV] using hasDerivAt_const τ (1 : 𝔸)
  | a :: L, τ => by
    have h1 := hasDerivAt_exp_smul_const a τ
    have h2 := hasDerivAt_prodExp L τ
    have key : HasDerivAt (fun x => exp (x • a) * prodExp L x)
        (exp (τ • a) * a * prodExp L τ + exp (τ • a) * (chainV 0 L τ * prodExp L τ)) τ :=
      h1.mul h2
    refine key.congr_deriv ?_
    simp only [chainV, prodExp]
    rw [add_mul, ← mul_assoc (Ad a τ (chainV 0 L τ)), Ad_mul_exp, ← mul_assoc a,
      ← exp_smul_comm]
    simp only [mul_assoc]

theorem continuous_chainV (Z : 𝔸) : ∀ L : List 𝔸, Continuous (chainV Z L)
  | [] => continuous_const
  | a :: L => by
    have hc := continuous_chainV Z L
    have : Continuous fun τ => Ad a τ (chainV Z L τ) := by
      simp only [Ad]
      have he : Continuous fun τ : ℝ => exp (τ • a) :=
        continuous_iff_continuousAt.2 fun τ => (hasDerivAt_exp_smul_const a τ).continuousAt
      have he' : Continuous fun τ : ℝ => exp (τ • (-a)) :=
        continuous_iff_continuousAt.2 fun τ => (hasDerivAt_exp_smul_const (-a) τ).continuousAt
      exact (he.mul hc).mul he'
    exact continuous_const.add this

theorem norm_prodExp_le : ∀ (L : List 𝔸), (∀ a ∈ L, ∀ s : ℝ, ‖exp (s • a)‖ ≤ 1) →
    ∀ τ, ‖prodExp L τ‖ ≤ 1
  | [], _, τ => by simp [prodExp]
  | a :: L, hL, τ => by
    simp only [prodExp]
    refine (norm_mul_le _ _).trans ?_
    have h1 := hL a (by simp) τ
    have h2 := norm_prodExp_le L (fun b hb => hL b (by simp [hb])) τ
    nlinarith [norm_nonneg (exp (τ • a)), norm_nonneg (prodExp L τ)]

theorem prodExp_zero : ∀ L : List 𝔸, prodExp L 0 = 1
  | [] => rfl
  | a :: L => by simp [prodExp, prodExp_zero L]

theorem chainV_zero_at_zero : ∀ L : List 𝔸, chainV 0 L 0 = L.sum
  | [] => by simp [chainV]
  | a :: L => by simp [chainV, Ad_zero, chainV_zero_at_zero L]

/-- **Single-step theorem for any product formula** (Lemmas 1, 2, 3 assembled). -/
theorem norm_prodExp_sub_exp_le (L : List 𝔸) (hL : ∀ a ∈ L, ∀ s : ℝ, ‖exp (s • a)‖ ≤ 1)
    (H : 𝔸) (hH : ∀ s : ℝ, ‖exp (s • H)‖ ≤ 1) (hsum : L.sum = H) (K : ℕ) (hK : 1 ≤ K)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖prodExp L t - exp (t • H)‖
      ≤ ∑ r ∈ range K, ‖chainC 0 L r - (if r = 0 then H else 0)‖ * (t ^ (r + 1) / (r + 1))
        + chainB 0 L K * (t ^ (K + 1) / (K + 1)) := by
  set D : ℝ → 𝔸 := fun τ => (chainV 0 L τ - H) * prodExp L τ
  have hS : ∀ τ, HasDerivAt (prodExp L) (H * prodExp L τ + D τ) τ := by
    intro τ
    convert hasDerivAt_prodExp L τ using 1
    simp only [D, sub_mul]; abel
  have hDc : Continuous D := by
    refine ((continuous_chainV 0 L).sub continuous_const).mul ?_
    exact continuous_iff_continuousAt.2 fun τ => (hasDerivAt_prodExp L τ).continuousAt
  have hS0 : prodExp L 0 = 1 := prodExp_zero L
  -- polynomial bound on the defect
  have hb : ∀ τ ∈ Set.Icc 0 t, ‖D τ‖ ≤
      ∑ r ∈ range (K + 1), (if r < K then ‖chainC 0 L r - (if r = 0 then H else 0)‖
        else chainB 0 L K) * τ ^ r := by
    intro τ hτ
    have hτ0 := hτ.1
    have htay := norm_chain_sub_taylor_le (0 : 𝔸) L hL K hK hτ0
    have hHsum : ∑ r ∈ range K, τ ^ r • (if r = 0 then H else 0) = H := sum_ite_zero_smul K hK τ H
    calc ‖D τ‖ ≤ ‖chainV 0 L τ - H‖ * ‖prodExp L τ‖ := norm_mul_le _ _
      _ ≤ ‖chainV 0 L τ - H‖ * 1 := by
          gcongr; exact norm_prodExp_le L hL τ
      _ = ‖(chainV 0 L τ - ∑ r ∈ range K, τ ^ r • chainC 0 L r)
            + ∑ r ∈ range K, τ ^ r • (chainC 0 L r - (if r = 0 then H else 0))‖ := by
          rw [mul_one]; congr 1
          simp only [smul_sub, sum_sub_distrib, hHsum]; abel
      _ ≤ τ ^ K * chainB 0 L K
            + ∑ r ∈ range K, τ ^ r * ‖chainC 0 L r - (if r = 0 then H else 0)‖ := by
          refine (norm_add_le _ _).trans (add_le_add htay ?_)
          refine (norm_sum_le _ _).trans (le_of_eq ?_)
          apply sum_congr rfl; intro r _
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hτ0 r)]
      _ = _ := by
          rw [sum_range_succ, if_neg (lt_irrefl K)]
          rw [add_comm]; congr 1
          · apply sum_congr rfl; intro r hr; rw [if_pos (mem_range.mp hr)]; ring
          · ring
  have := norm_sub_exp_le_poly H hH (prodExp L) D hS hDc hS0 ht (range (K + 1)) _ hb
  refine this.trans (le_of_eq ?_)
  rw [sum_range_succ, if_neg (lt_irrefl K)]
  congr 1
  apply sum_congr rfl; intro r hr; rw [if_pos (mem_range.mp hr)]

end Trotter
