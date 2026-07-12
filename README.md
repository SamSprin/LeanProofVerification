# Lean verification: Log-concavity of codimension-three level Hilbert functions of type two

A Lean 4 + Mathlib formalization of the proof of:

> **Theorem 1.** Let `A = R/I` (`R = k[x₁,x₂,x₃]`, `k` any field) be a standard
> graded Artinian level algebra of embedding dimension three, socle degree `e`,
> and type two. Then its Hilbert function is log-concave:
> `hᵢ² ≥ h_{i-1} h_{i+1}` for `1 ≤ i ≤ e−1`.

All Lean code is in [`LogConcavity.lean`](LogConcavity.lean). The build is
fully self-contained in this folder: toolchain in `.elan/`, dependencies in
`.lake/`.

## Verification status

`lake build` succeeds with **zero `sorry`**, and `#print axioms` reports only
Lean's standard foundational axioms (`propext`, `Classical.choice`,
`Quot.sound`) for every theorem — no hidden axioms.

## What is machine-checked

The development derives Theorem 1 from the *primitive numerical shadows* of
the paper's commutative algebra. Everything the paper does on pp. 2–4 —
every identity, inequality, sum manipulation, and case split — is formally
verified:

| Paper step | Lean theorem |
|---|---|
| `2Nⱼ = (j+1)(j+2)`, Pascal recursion, strict monotonicity | `two_mul_N`, `N_succ`, `N_strictMono` |
| First/second differences of `N` extended by zero | `Nz_diff`, `Nz_second_diff` |
| ε=1 case: windows `(N_m, N_{m−1}, N_{m−2})` are log-concave | `binomial_window_log_concave`, `Nz_window` |
| Hilbert-numerator computation `Δ²g_d = 2 + Q_d − P_{<d} − p_d` (from rank additivity of complex (1)) | `shiftSum_second_diff` + inside `deep_dispatch` |
| Central estimate (4) from (3), and (5) ⇒ (6) (`p_d = 0`, `Δ²g_d = 1`) | inside `deep_dispatch` |
| AM–GM step: `Δ² ≤ 0 ⇒ ac ≤ b²` | `amgm_log_concave` |
| r=0 case: evaluation `g = (d(d−1), d(d+1), (d+1)(d+2)−p_d)` and margin `> 0` | `deep_dispatch`, `r_eq_zero_log_concave` |
| Inequality (9): `2d ≤ e+2` from `N_{d−1} ≤ g_{d−1} ≤ N_{e−d+1}` | inside `deep_dispatch` |
| `x = g_{d−1} − g_{d−2} = d + a + D ≥ d`, `g_{d−2} ≤ d(d−1)` (via (8), Stanley) | inside `deep_dispatch` |
| r=1 failure margin `x² − y ≥ d > 0` | `r_eq_one_log_concave` |
| Full scenario case analysis | `GoodTriple.log_concave`, `deep_dispatch` |
| Reversal transfer `g → h` | `theorem1`, `theorem1_full` |

## What is assumed (the trust base), and exactly why

Mathlib currently has **no graded Matlis duality, no minimal graded free
resolutions, and no Stanley theorem** for codimension-3 Gorenstein h-vectors;
formalizing them is a multi-month research project. The corresponding
*structural* facts enter as the named hypotheses of `theorem1_full`, each
annotated with its source in the paper:

- `hrev` — `g_d = h_{e−d}` (graded Matlis duality, p. 1);
- `hquot` — `h_t ≤ N_t` (`A` is a quotient of `R`);
- `hres` — rank additivity of the exact complex (1);
- `hrε`, `h3` — the rank data `r_d ∈ {0,1,2}`, `ε_d ∈ {0,1}` and estimate (3);
- `hε1` — `ε_d = 1` ⇒ `h_t = N_t` below degree `s−d` (dual degree correspondence);
- `hr0` — `r_d = 0` ⇒ no relations of shift `< d` (`P_{<d} = 0`);
- `hr1` — in the putative-failure case, equation (8) with the Gorenstein
  Hilbert function `B` and Stanley's monotonicity (Lemma 1) — packaging the
  UFD/cyclic-submodule argument of pp. 3–4.

The formal result: **given these structural inputs, log-concavity follows,
with the entire quantitative argument of the paper kernel-checked.**

## Non-vacuity certificate

Assumed hypotheses could in principle be mutually contradictory, making the
theorem vacuous. The `Nonvacuity` section rules this out: for the genuine
level algebra `A = R/Ann(X², Y²+XZ)` — Hilbert function `(1,3,2)`, socle
degree 2, type two, dual resolution `F₁ = R(−1)³⊕R(−2)²`, `F₂ = R(−3)⁴`,
`s = 5`, rank data `r₂ = 2, ε₂ = 0` — **every hypothesis of `theorem1_full`
is machine-verified** (`nonvacuity`), and the theorem delivers the concrete
inequality `h₀h₂ = 2 ≤ 9 = h₁²`.

## Reproducing

```powershell
$env:ELAN_HOME = "$PWD\.elan"
$env:PATH = "$env:ELAN_HOME\bin;$env:PATH"
lake build   # expect: Build completed successfully + axiom audit lines
```

Setup: elan 4.2.3 (local), Lean `v4.31.0`, Mathlib `v4.31.0` with prebuilt
cache (`lake exe cache get`).
