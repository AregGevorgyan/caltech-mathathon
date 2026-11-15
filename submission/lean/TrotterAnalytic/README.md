# Mathlib formalization of the analytic lemmas (p109)

Lean 4 + Mathlib (`lean-toolchain`, `lake-manifest.json` pin the versions).
Build: `lake exe cache get && lake build`.

| file | content | write-up |
|---|---|---|
| `Telescope.lean` | `S^r − U^r = Σ U^(r−1−j)(S−U)S^j`; `‖S^r−U^r‖ ≤ r‖S−U‖`; second-order form with error `‖S−U‖² r(r−1)/2` | Theorem D, Step 1 |
| `Duhamel.lean` | variation of constants `‖S(t) − e^{tH}‖ ≤ ∫₀ᵗ ‖S′ − HS‖`, split form `L T R`, polynomial integration | Lemma 1, shape of (★) |
| `Midpoint.lean` | `‖Σ_{j<r} δ·Ad_{(j+½)δ}[H,Y]‖ ≤ 2‖Y‖ + rδ³‖ad_H³Y‖/24` (exact cell derivative + sharp midpoint error) | Theorem D, Step 3 |
| `TheoremD.lean` | **Theorem D** from `E₅ = [H,Y]+Z` and the single-step estimate `‖M − δ⁵Ad_{U(−δ/2)}E₅‖ ≤ ρ` | Theorem D |
| `Chain.lean` | Taylor expansion of a chain `a₁ + Ad_{a₁}(a₂ + Ad_{a₂}(… Z))` with remainder `τᴷ Σₛ Σ_{j<K} ‖ad_{aₛ}^{K−j} c(tailₛ, j)‖/(K−j)!` | Lemma 3 (chain form) |
| `ProductFormula.lean` | `d/dτ ∏ e^{τaⱼ} = V(τ)·∏ e^{τaⱼ}` (Lemma 2, m = 0) and the assembled single-step theorem `‖∏ e^{taⱼ} − e^{tH}‖ ≤ Σ_{r<K} ‖cᵣ − [r=0]H‖ t^{r+1}/(r+1) + B_K t^{K+1}/(K+1)` for **any** product formula (needs `NormOneClass`) | Lemmas 1–3 ⇒ (★) |
| `IntegralRemainder.lean` | integral form `Ad_τX − Σ_{i≤k} τⁱad^iX/i! = ∫₀^τ (τ−σ)^k/k!·Ad_σ(ad^{k+1}X)dσ` (telescoping primitive, no Fubini); Lemma 3′ for one item | Lemma 3′ |
| `ChainGrouped.lean` | **Lemma 3′ (chain form)** `‖V(τ) − Σ_{r<K} τʳc_r‖ ≤ τᴷ Σ_items ∫₀¹ ‖P_a(u)‖du`, `P_a(u) = Σ_{j<K} (1−u)^{K−j−1}/(K−j−1)!·ad_a^{K−j}c_j`; single-step theorem with these grouped constants | Lemma 3′, (★) |
| `SplitFormula.lean` | **Lemma 2 for any split** `S = L R`: `L⁻¹ = ∏` reversed negated stages; key identity `chainV_W(negrev L) = L⁻¹(W − V_L)L`; `S′ = HS + L·T·R` with `T = V_R − chain_H(negrev L)`; single-step theorem for any split with Lemma 3′ constants of both chains | Lemmas 1–3′ ⇒ Theorems A (m=0), B (m=3), C (m=2) |
| `Midpoint2.lean` | Euler–Maclaurin-corrected midpoint: cell error `(2h)⁵‖ad⁵Y‖/1920`; `‖Σ δ·Ad_{mⱼ}[H,Y]‖ ≤ 2‖Y‖ + δ²‖ad²Y‖/12 + rδ⁵(1/1920+1/576)‖ad⁵Y‖` | Theorem D′, item 3 |
| `TheoremDprime.lean` | **Theorem D′** from `E₅ = [H,Y]+Z`, `W₇ = [H,Y₇]+Z₇` and `‖M − δ⁵Ad E₅ − δ⁷Ad W₇‖ ≤ ρ₈` | Theorem D′ |
| `CStar.lean` | discharges all contraction hypotheses in a C*-algebra (skew-adjoint generators ⇒ unitary exponentials, `‖S^k‖ ≤ 1`); single-step theorem for skew-adjoint stages; **instance for anti-Hermitian complex matrices** with the operator norm | applicability |
| `SingleStepD.lean` | Step 2 of Theorem D: `‖M − δ⁵Ad_{U(−δ/2)}E₅‖ ≤ δ⁷B̂₆/7 + δ⁷‖ad_H²E₅‖/8 + B̂₄βδ⁵/5` from `Ŝ = e^{−τH}S`, Lemma 2 and Lemma 3′; **`theoremD_full`**: Theorem D with only the algebraic identities (`ĉ₀..₃ = 0`, `ĉ₄ = 5E₅`, `ĉ₅ = −3[H,E₅]`, `E₅ = [H,Y]+Z`) as hypotheses | Theorem D, end to end |
| `SingleStepDprime.lean` | single-step input `ρ₈` of Theorem D′ (Lemma 3′ at K = 7, exact `ĉ₆`, conjugation remainders K = 3, 1); **`theoremDprime_full`**: Theorem D′ with only algebraic hypotheses | Theorem D′, end to end |
| `ConjTaylor.lean` | `‖e^{τa}Ye^{−τa} − Σ_{k<K} τᵏ ad_aᵏY/k!‖ ≤ τᴷ‖ad_aᴷY‖/K!` | Lemma 3 (core) |

Setting: `𝔸` a real Banach algebra; generators satisfy `‖exp(s•H)‖ ≤ 1` for all real `s`
(true for anti-Hermitian `H` in a C*-algebra, where `exp(s•H)` is unitary).

`Axioms.lean` prints the axioms of the main theorems (`axioms.log`): only `propext`,
`Classical.choice`, `Quot.sound`; no `sorry`.

**What is and is not formal.** The analytic argument (Lemma 1, Lemma 2 for split m = 0,
Lemma 3 in chain form, Theorem D from its single-step input) is proved in Lean/Mathlib for an
abstract Banach algebra. The *values* of the coefficients cᵣ and of the remainder terms as
Lie polynomials in A, B are computed by exact arithmetic in Python (`trotter/`); the leading
coefficient c₄ = 5E₅ and the processing identity E₅ = [H,Y] + Z are additionally kernel-checked
in `../S4Leading.lean`. Not formalized: the joint-representation choice (it only changes how the
grouped polynomials are written), and the interval
bounds on ∫|c_b(u)|du.
