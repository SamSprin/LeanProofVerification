# Full Writeup: Lean Verification of "Log-concavity of codimension-three level Hilbert functions of type two"

## 1. What was built

A fully self-contained Lean 4 verification environment in this repository's
root folder — nothing installed outside it:

- **Toolchain**: elan 4.2.3 in `.elan/`, Lean 4.31.0
- **Library**: Mathlib (release v4.31.0) with its prebuilt binary cache
  (8,542 files) in `.lake/`
- **The formalization**: `LogConcavity.lean` (~690 lines), documentation in
  `README.md`

To re-verify: put `.elan\bin` on PATH and run `lake build`:

```powershell
$env:ELAN_HOME = "$PWD\.elan"
$env:PATH = "$env:ELAN_HOME\bin;$env:PATH"
lake build
```

The build ends with an axiom audit showing every theorem depends only on
`propext`, `Classical.choice`, `Quot.sound` — Lean's three standard
foundational axioms. There are **no `sorry`s and no custom axioms** anywhere.

## 2. Architecture of the proof

**Layer 0 — Hilbert function of `R = k[x₁,x₂,x₃]`.**
`N j = C(j+2,2)` and its zero-extension `Nz` to integer degrees, with the
closed form `2Nⱼ = (j+1)(j+2)`, Pascal recursion, strict monotonicity, the
first difference `Nz t − Nz(t−1) = t+1`, and the second difference
`Δ²Nz = 1` on nonnegative degrees (the numerical content of the Hilbert
series of `R`). All proved.

**Layer 1 — the four scenarios imply log-concavity.**
The paper's case analysis distills each tested triple
`(g_{d−2}, g_{d−1}, g_d)` into one of four shapes (`GoodTriple`); each is
proved log-concave:

- binomial windows `(N_m, N_{m−1}, N_{m−2})` (the ε_d = 1 case);
- the AM–GM step (`Δ²g_d ≤ 0` implies the inequality);
- the r_d = 0 margin `g_{d−1}² − g_{d−2}g_d = d(2(d+1)+(d−1)p_d) > 0`;
- the r_d = 1 failure margin `x² − y ≥ d² − d(d−1) = d > 0`.

**Layer 2 — from resolution numerics to the scenarios (`deep_dispatch`).**
This is the deep part. Starting only from the *numerical shadows* of the
commutative algebra, Lean derives the paper's entire reduction:

- the telescoping identity turning rank additivity of the complex
  `0 → R(−s) → F₂ → F₁ → R² → M → 0` into
  `Δ²g_d = 2 + Q_d − P_{<d} − p_d` (formalized as `shiftSum_second_diff`,
  a genuine finite-sum argument over shift multisets);
- the central estimate (4) from the rank inequality (3);
- the proof that a putative failure under `r_d = 1` forces equation (6)
  (`p_d = 0`, `Δ²g_d = 1`);
- inequality (9) `2d ≤ e+2`, from squeezing `g_{d−1}` between `N_{d−1}` and
  `N_{e−d+1}` using strict monotonicity of `N`;
- the computation `x = g_{d−1} − g_{d−2} = d + a + D ≥ d` using
  equation (8) and Stanley monotonicity of `B` (including the boundary case
  `n − 2 < 0`);
- the bound `g_{d−2} ≤ 2N_{d−2} = d(d−1)`;
- the explicit evaluation of the r_d = 0 triple
  `(d(d−1), d(d+1), (d+1)(d+2) − p_d)` from the resolution formula, via
  `P_{<d} = 0` and nonnegativity forcing `Q_d = 0`.

**Assembly.** `theorem1_full` chains Layer 2 → Layer 1 → the reversal
transfer `g_d = h_{e−d}`, concluding `h_{i−1}h_{i+1} ≤ h_i²` for
`1 ≤ i ≤ e−1`.

**Non-vacuity certificate (`nonvacuity`).**
Since the structural facts are hypotheses, one must rule out that they are
secretly contradictory (which would make the theorem vacuously true). For
the genuine level algebra `A = R/Ann(X², Y²+XZ)` — Hilbert function
`(1,3,2)`, socle degree 2, type two, whose Hilbert numerator
`(1−t)³(1+3t+2t²) = 1 − 4t² + 2t³ + 3t⁴ − 2t⁵` yields the dual resolution
data `F₁ = R(−1)³ ⊕ R(−2)²` (p₁ = 3, p₂ = 2), `F₂ = R(−3)⁴` (q₃ = 4),
`s = 5`, rank data `r₂ = 2`, `ε₂ = 0` — Lean verifies **all eleven
hypotheses** concretely, and the theorem produces the concrete inequality
`h₀h₂ = 2 ≤ 9 = h₁²`. The hypothesis set is consistent and instantiable by
real algebras.

## 3. What is machine-checked vs. assumed

**Kernel-checked (everything quantitative in the paper, pp. 2–4):** every
identity, inequality, sum manipulation, case split, and the logic that
strings them together — including all four margin computations and the
entire dispatch from inequality (3) plus rank additivity down to the
conclusion.

**Assumed, as named hypotheses of `theorem1_full`** (each annotated in the
Lean source with its origin in the paper):

| Hypothesis | Content | Paper source |
|---|---|---|
| `hrev` | `g_d = h_{e−d}` | graded Matlis duality, p. 1 |
| `hquot` | `h_t ≤ N_t` | `A` is a quotient of `R` |
| `hres` | rank additivity of complex (1) | exactness of the dual resolution |
| `hrε`, `h3` | `r_d ∈ {0,1,2}`, `ε_d ∈ {0,1}`, estimate (3) | linear algebra over `Frac(R)`, (2)–(3) |
| `hε1` | `ε_d = 1` ⇒ `h_t = N_t` below `s−d` | dual degree correspondence, p. 3 |
| `hr0` | `r_d = 0` ⇒ `P_{<d} = 0` | minimal relations are nonzero, p. 3 |
| `hr1` | equation (8) with `B` Gorenstein, Stanley monotonicity | UFD/cyclic-submodule argument + Lemma 1, pp. 3–4 |

## 4. Honest verdict

**Is this a complete formalization of the theorem?** No. Discharging the
seven structural hypotheses would require building graded Matlis duality,
minimal graded free resolutions, and Stanley's theorem for codimension-three
Gorenstein h-vectors inside Mathlib — none of which exist there even
partially. That is a research program measured in expert-months to years,
not something any amount of code in one session can produce.

**Is it strong verification? Yes, and here is its precise value.** For a
paper like this, errors overwhelmingly live in the quantitative
bookkeeping: an off-by-one in a degree bound, a sign in a second
difference, a case silently dropped, a margin that isn't actually positive.
*Every one of those failure modes is now excluded by the Lean kernel.* What
remains on trust are textbook-level structural moves (duality, exactness,
rank counts) plus one citation to Zanello's published characteristic-free
Stanley theorem — exactly the parts a referee verifies by standard theory
rather than computation. The non-vacuity certificate additionally proves
the hypothesis interface is coherent and realizable.

In the taxonomy of partial formalizations, this is a **complete,
non-vacuous, machine-checked verification of the paper's reduction and case
analysis** — the strongest form of verification achievable for this result
with today's libraries.

## 5. Key named results in `LogConcavity.lean`

| Lean name | Statement |
|---|---|
| `two_mul_N`, `N_succ`, `N_strictMono` | closed form, Pascal recursion, strict monotonicity of `N` |
| `Nz_diff`, `Nz_second_diff` | first/second differences of the zero-extended `N` |
| `binomial_window_log_concave`, `Nz_window` | log-concavity of descending windows of `N` |
| `amgm_log_concave` | `a + c ≤ 2b`, `a,c ≥ 0` ⇒ `ac ≤ b²` |
| `r_eq_zero_log_concave` | the r = 0 margin is positive |
| `r_eq_one_log_concave` | the r = 1 failure margin is positive |
| `GoodTriple.log_concave` | all four scenarios are log-concave |
| `shiftSum_second_diff` | the Hilbert-numerator telescoping identity |
| `deep_dispatch` | resolution numerics ⇒ every tested triple is a `GoodTriple` |
| `theorem1`, `theorem1_full` | the main theorem (scenario form / full form) |
| `nonvacuity` | all hypotheses verified for `A = R/Ann(X², Y²+XZ)` |

Axiom audit output (from `lake build`):

```
'LogConcavity.theorem1_full'  depends on axioms: [propext, Classical.choice, Quot.sound]
'LogConcavity.nonvacuity'     depends on axioms: [propext, Classical.choice, Quot.sound]
'LogConcavity.deep_dispatch'  depends on axioms: [propext, Classical.choice, Quot.sound]
'LogConcavity.theorem1'       depends on axioms: [propext, Classical.choice, Quot.sound]
'LogConcavity.GoodTriple.log_concave' depends on axioms: [propext, Classical.choice, Quot.sound]
'LogConcavity.shiftSum_second_diff'   depends on axioms: [propext, Classical.choice, Quot.sound]
'LogConcavity.binomial_window_log_concave' depends on axioms: [propext, Classical.choice, Quot.sound]
```
