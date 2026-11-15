# How wrong is a Trotter step? A short explainer

*Pitched at a first course in quantum computing. The precise statements and proofs are in
[writeup.md](writeup.md).*

## 1. The problem

A quantum computer simulating a physical system has to apply the time-evolution operator
e^{−itH}. The Hamiltonian H is usually a sum of pieces that are easy on their own but
don't commute. A standard example is the transverse-field Ising chain:

 H = A + B,  A = Σ Z_i Z_{i+1} (couplings),  B = Σ X_i (field).

Gates for e^{−itA} and e^{−itB} are easy to build, but e^{−it(A+B)} ≠ e^{−itA}e^{−itB},
because AB ≠ BA. A **product formula** (Trotter–Suzuki formula) approximates the true
evolution by a sequence of the easy pieces. The fourth-order Suzuki formula S₄ uses 11 of
them, with carefully chosen and partly negative time fractions. To simulate for time T we
apply S₄(T/r) r times. The engineering question is how large r must be for a target
accuracy ε. Every extra step costs gates.

We need a **guaranteed** answer, not just a numerical estimate, because the hardware will
run circuits far too large to simulate classically. That requires a rigorous upper bound
on ‖S₄(t) − e^{−itH}‖.

## 2. What was known

For a 4th-order formula the error of one step scales like t⁵, multiplied by a constant
that depends on the commutators of A and B. Commutators are what measure how badly A and B
fail to commute. Childs, Su, Tran, Wiebe and Zhu (2021) proved a bound of the form

 error ≤ t⁵ × (0.0047‖[A,[A,[A,[B,A]]]]‖ + … + 0.0284‖[B,[B,[B,[B,A]]]]‖).

The bound is rigorous, but on the Ising chain it overestimates the real error by about
**60×**, at every step size. In the example in §5 that makes the guaranteed circuit
about 4× deeper than necessary (236 steps vs 56). Part of that gap also comes from adding
up step errors one by one: errors in different steps partly cancel in reality.

## 3. Idea 1: compute the leading error exactly

Pretend for a moment that all the exponentials can be merged into a single exponential
(the Baker–Campbell–Hausdorff formula). Then

 S₄(t) = exp( t(A+B) + t⁵E₅ + t⁷E₇ + … ),

and the t⁵ coefficient E₅ is a specific combination of commutators with five letters. We
computed it **exactly**. Its six coefficients are algebraic numbers involving the cube
root of 2, because the Suzuki time fractions involve 4^{1/3}. For example, the coefficient
of [B,[B,[A,[A,B]]]] is

 −551/900000 − (451/2700000)·2^{1/3} − (371/1350000)·2^{2/3} ≈ −0.00126.

Adding up their sizes gives 0.0038, compared with 0.0875 for the Childs constants. That
is 23× smaller. The computation was checked three ways: exact rational arithmetic in
Python, a proof checked by the Lean theorem prover, and comparison against a numerically
computed matrix logarithm.

For small t the error equals t⁵‖E₅‖ up to corrections of size t⁶. So this is the **best
possible** t⁵ constant: no valid bound can have a smaller one.

## 4. Idea 2: control everything else rigorously

"Up to corrections of size t⁶" isn't a guarantee by itself, because we need to know how
big those corrections can be. We write the error exactly as an integral (the
"variation of constants" formula from ODE theory). Inside the integral, each Taylor
expansion of an exponential gets an exact integral remainder. Every leftover exponential
then sits on the outside, where it is a unitary rotation and doesn't change any norm.

The trick that makes the constants small is to **collect terms before taking norms**.
Many pieces of the expansion partly cancel. Earlier bounds applied the triangle
inequality ‖x + y‖ ≤ ‖x‖ + ‖y‖ to each piece separately, which throws those cancellations
away. We first add up, exactly, every group of terms that share the same outer rotation
and the same integral weight. Only then do we take a norm. The result:

 error ≤ t⁵ Σ|c_i|‖C_i‖ + t⁶ Σ d_b‖P_b‖,  valid for **every** t ≥ 0,

where all constants are written down exactly (`results/constants.md`). A second round of
grouping goes further. Terms from different orders of the Taylor expansion also share an
outer rotation, so they too can be added before taking a norm. That halves the remainder
again. The final universal bounds, in the same commutators Childs et al. use, are:

- a single t⁵ term with constants summing to **0.0137**, against Childs' 0.0875. Each
  constant is smaller than Childs' constant for the same commutator.
- t⁵·(exact 0.0030) + t⁶·(exact 0.0005) + t⁷·0.0007, which is the best option at
  realistic step sizes.

**Can one do better?** Not at leading order. Any bound of this form (constants times the same
commutator norms, times t⁵) must have constants summing to at least 0.0029981499. That is
proved by six small explicit matrix pairs and a linear-programming argument, checked in exact
rational arithmetic. Our exact leading term gives 0.0029981584, so it is optimal to within
3 parts in a million. Childs' 0.0875 is 29× above what is possible.

## 5. What it buys on a real model

Ising chain with 8 spins (J = h = 1), simulating to time T = 8 with total error 10⁻³:

| method | Trotter steps r |
|---|---|
| Childs et al. bound | 236 |
| our bound, constants only (Theorem C) | 101 |
| our bound, evaluated on this H | 86 |
| what is actually needed (brute-force simulation) | 56 |

At small step sizes our operator-specific bound sits within 1–7% of the true error. The Childs bound is
about 60× above it.

![](../results/tfim_n8.png)

## 6. Idea 3: errors from different steps partly cancel

Adding up r one-step error bounds assumes the worst: that every step's error points the
same way. Part of the leading error has the special form [H, Y]. Between steps, the
evolution rotates that part around, so over many steps it averages out: a sum of such
terms telescopes to something that doesn't grow with r at all. Only the remainder Z keeps
accumulating. For S₄ we found the best Y exactly, and Z turns out to be a single number
times three commutators, 3.4× smaller than the full leading error.

This matters most for long simulations. Repeating the same trick one order higher
removes most of what is left. For the Ising chain run to T = 128 at accuracy 10⁻³, our
guarantee needs 1815 steps and the truth is 1776, 2% apart. The Childs et al. bound asks
for 7543.

![](../results/long_time_n8.png)

## 7. Take-aways

- Error bounds for product formulas can be made close to tight by (i) computing the
  leading error term exactly and (ii) never applying the triangle inequality before the
  algebra has had a chance to cancel.
- Error that has the form [H, Y] cancels across steps. Accounting for this rigorously
  makes the guarantee nearly tight for long simulations.
- Rigorous no longer has to mean pessimistic: in the example, the guaranteed step count
  is within 2–11% of the truly necessary one.
- The leading constant cannot be improved: it is optimal among all bounds of this form.
- The whole analytic argument is machine-checked. The Lean theorem prover with the Mathlib
  library verifies every inequality step. That leaves only exact algebraic identities between
  commutators, which are computed in exact arithmetic and the key ones are checked by Lean's kernel.
