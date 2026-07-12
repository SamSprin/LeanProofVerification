/-
# Log-concavity of codimension-three level Hilbert functions of type two

Formalization of:

  **Theorem 1.** Let `A = R/I` (`R = k[x₁,x₂,x₃]`, `k` any field) be a standard
  graded Artinian level algebra of embedding dimension three, socle degree `e`,
  and type two.  Then its Hilbert function `h = (1, 3, h₂, …, h_e = 2)` is
  log-concave: `hᵢ² ≥ h_{i-1} h_{i+1}` for `1 ≤ i ≤ e - 1`.

## Architecture

The development has three machine-checked layers plus a clearly delimited
set of structural hypotheses.

* **Layer 0** — the Hilbert function `N j = binom(j+2,2)` of `R` and its
  arithmetic (closed form, Pascal recursion, strict monotonicity, first and
  second differences, log-concavity of descending windows).

* **Layer 1** — `GoodTriple → log-concave`: the four arithmetic scenarios of
  the paper's case analysis each force the log-concavity inequality
  (`GoodTriple.log_concave`).

* **Layer 2** — `deep_dispatch`: starting from the *primitive numerical
  shadows* of the commutative algebra — rank additivity of the minimal
  resolution (paper (1)), the rank estimate (3), and equation (8) with
  Stanley's monotonicity — this layer machine-checks the whole reduction of
  pp. 2–4: the Hilbert-numerator computation `Δ²g_d = 2 + Q_d − P_{<d} − p_d`,
  the central estimate (4), the failure criterion (5) forcing (6)
  (`p_d = 0`, `Δ²g_d = 1`), inequality (9) `2d ≤ e + 2`, the computation
  `x = g_{d-1} − g_{d-2} = d + a + D ≥ d`, and the bound
  `g_{d-2} ≤ 2N_{d-2} = d(d-1)`.

* **`theorem1_full`** chains Layer 2 into Layer 1 and transfers back from the
  reindexed dual `g` to `h` by reversal.

## What remains assumed (and exactly why)

Mathlib today has no graded Matlis duality, no minimal graded free
resolutions, and no Stanley theorem for codimension-three Gorenstein
h-vectors, so the following *structural* facts enter as named hypotheses of
`theorem1_full`, each annotated with its source in the paper:

* `hrev`  — `g_d = h_{e-d}` (graded Matlis duality, p. 1);
* `hquot` — `h_t ≤ N_t` (`A` is a quotient of `R`);
* `hres`  — rank additivity of the exact complex (1):
  `g_t = 2N_t − Σ_b p_b N_{t-b} + Σ_b q_b N_{t-b} − N_{t-s}`;
* `hrε`, `h3` — the rank data `r_d ∈ {0,1,2}`, `ε_d ∈ {0,1}` and the linear
  algebra estimate (3) `Q_d − ε_d ≤ P_{<d} − r_d` (from (2), p. 2);
* `hε1`  — if `ε_d = 1` then `h_t = N_t` for `t < s − d` (degree
  correspondence in the dual resolution, p. 3, first case);
* `hr0`  — if `r_d = 0` then `P_{<d} = 0` (minimal relations are nonzero,
  p. 3, third case);
* `hr1`  — in the putative-failure case `r_d = 1, p_d = 0, Δ²g_d = 1`, the
  existence of `a < d` and the Gorenstein Hilbert function `B` with
  equation (8) and Stanley's monotonicity (Lemma 1) — this packages the
  UFD/cyclic-Gorenstein-submodule argument, (7)–(8), pp. 3–4.

Everything else — every inequality, identity, sum manipulation and case
split in the paper — is proved below with **no `sorry` and no extra axioms**
(see the `#print axioms` audit at the bottom).
-/
import Mathlib

namespace LogConcavity

/-! ## Layer 0a: the Hilbert function of `R` on natural indices -/

/-- `N j = binom (j+2) 2`, the dimension of the degree-`j` part of a
polynomial ring in three variables, as an integer. -/
def N (j : ℕ) : ℤ := ((j + 2).choose 2 : ℤ)

/-- Pascal recursion for `N`. -/
lemma N_succ (j : ℕ) : N (j + 1) = N j + (j + 2) := by
  have h : (j + 3).choose 2 = (j + 2).choose 1 + (j + 2).choose 2 :=
    Nat.choose_succ_succ (j + 2) 1
  simp only [N, show j + 1 + 2 = j + 3 from rfl, h, Nat.choose_one_right]
  push_cast
  ring

/-- The closed form, multiplied by `2` to stay division-free:
`2 N j = (j+1)(j+2)`. -/
lemma two_mul_N (j : ℕ) : 2 * N j = ((j : ℤ) + 1) * ((j : ℤ) + 2) := by
  induction j with
  | zero => norm_num [N]
  | succ k ih =>
    rw [N_succ]
    push_cast
    linear_combination ih

lemma N_nonneg (j : ℕ) : 0 ≤ N j := by unfold N; exact Int.natCast_nonneg _

/-- `N` is strictly increasing (used for the paper's inequality (9)). -/
lemma N_strictMono {i j : ℕ} (h : i < j) : N i < N j := by
  have h2i := two_mul_N i
  have h2j := two_mul_N j
  have hij : (i : ℤ) < (j : ℤ) := by exact_mod_cast h
  have hi : (0 : ℤ) ≤ (i : ℤ) := Int.natCast_nonneg i
  nlinarith

lemma N_mono {i j : ℕ} (h : i ≤ j) : N i ≤ N j := by
  rcases lt_or_eq_of_le h with h' | h'
  · exact le_of_lt (N_strictMono h')
  · rw [h']

/-- **Windows of `N` are log-concave**: the ratios `N_j / N_{j-1}` are
nonincreasing, division-free form.  This is the ε_d = 1 case of the paper. -/
lemma binomial_window_log_concave (k : ℕ) : N (k + 2) * N k ≤ N (k + 1) ^ 2 := by
  have h0 := two_mul_N k
  have h1 := two_mul_N (k + 1)
  have h2 := two_mul_N (k + 2)
  push_cast at h1 h2
  have hk : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg k
  nlinarith [h0, h1, h2, sq_nonneg ((k : ℤ) + 2), sq_nonneg ((k : ℤ) + 3)]

/-! ## Layer 0b: the Hilbert function of `R` on integer indices

`Nz t = N t` for `t ≥ 0` and `0` for `t < 0` — the natural indexing for
graded dimension counts, where negative degrees vanish. -/

/-- `N` extended by zero to negative integers. -/
def Nz (t : ℤ) : ℤ := if 0 ≤ t then N t.toNat else 0

lemma Nz_neg (t : ℤ) (h : t < 0) : Nz t = 0 := by
  rw [Nz, if_neg (by omega)]

lemma Nz_natCast (n : ℕ) : Nz (n : ℤ) = N n := by
  rw [Nz, if_pos (Int.natCast_nonneg n), Int.toNat_natCast]

lemma Nz_nonneg (t : ℤ) : 0 ≤ Nz t := by
  rw [Nz]; split
  · exact N_nonneg _
  · exact le_refl 0

lemma Nz_zero : Nz 0 = 1 := by decide

/-- Division-free closed form on the nonnegative range. -/
lemma two_mul_Nz (t : ℤ) (ht : 0 ≤ t) : 2 * Nz t = (t + 1) * (t + 2) := by
  rw [Nz, if_pos ht]
  have h := two_mul_N t.toNat
  rwa [Int.toNat_of_nonneg ht] at h

/-- First difference: `Nz t − Nz (t−1) = t + 1` for `t ≥ 0`
(the paper's `N_j − N_{j-1} = j + 1`, p. 4). -/
lemma Nz_diff (t : ℤ) (ht : 0 ≤ t) : Nz t - Nz (t - 1) = t + 1 := by
  by_cases h1 : 0 ≤ t - 1
  · have a0 := two_mul_Nz t ht
    have a1 := two_mul_Nz (t - 1) h1
    have h2 : 2 * (Nz t - Nz (t - 1)) = 2 * (t + 1) := by linear_combination a0 - a1
    linarith
  · have ht0 : t = 0 := by omega
    subst ht0
    rw [Nz_zero, Nz_neg _ (by norm_num)]
    norm_num

/-- Second difference: `Δ²Nz t = 1` for `t ≥ 0` and `0` for `t < 0` —
the numerical content of `(1−t)³ · 1/(1−t)³ = 1`. -/
lemma Nz_second_diff (t : ℤ) :
    Nz t - 2 * Nz (t - 1) + Nz (t - 2) = if 0 ≤ t then 1 else 0 := by
  by_cases h0 : 0 ≤ t
  · rw [if_pos h0]
    by_cases h2 : 0 ≤ t - 2
    · have a0 := two_mul_Nz t h0
      have a1 := two_mul_Nz (t - 1) (by omega)
      have a2 := two_mul_Nz (t - 2) h2
      have key : 2 * (Nz t - 2 * Nz (t - 1) + Nz (t - 2)) = 2 := by
        linear_combination a0 - 2 * a1 + a2
      linarith
    · by_cases h1 : 0 ≤ t - 1
      · have ht1 : t = 1 := by omega
        subst ht1
        norm_num [Nz_neg (1 - 2 : ℤ) (by norm_num), Nz_zero]
        decide
      · have ht0 : t = 0 := by omega
        subst ht0
        rw [Nz_zero, Nz_neg _ (by norm_num), Nz_neg _ (by norm_num)]
        ring
  · rw [if_neg h0, Nz_neg _ (by omega), Nz_neg _ (by omega), Nz_neg _ (by omega)]
    ring

lemma Nz_mono {a b : ℤ} (h : a ≤ b) : Nz a ≤ Nz b := by
  by_cases ha : 0 ≤ a
  · rw [Nz, if_pos ha, Nz, if_pos (by omega)]
    exact N_mono (by omega)
  · rw [Nz, if_neg ha]
    exact Nz_nonneg b

lemma Nz_lt {a b : ℤ} (ha : 0 ≤ a) (h : a < b) : Nz a < Nz b := by
  rw [Nz, if_pos ha, Nz, if_pos (by omega)]
  exact N_strictMono (by omega)

/-- Windows of `Nz` are log-concave, integer-index form. -/
lemma Nz_window (m : ℤ) (hm : 2 ≤ m) : Nz m * Nz (m - 2) ≤ Nz (m - 1) ^ 2 := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, m - 2 = (k : ℤ) := ⟨(m - 2).toNat, by omega⟩
  have a0 : Nz m = N (k + 2) := by
    rw [show m = ((k + 2 : ℕ) : ℤ) by push_cast; omega, Nz_natCast]
  have a1 : Nz (m - 1) = N (k + 1) := by
    rw [show m - 1 = ((k + 1 : ℕ) : ℤ) by push_cast; omega, Nz_natCast]
  have a2 : Nz (m - 2) = N k := by rw [hk, Nz_natCast]
  rw [a0, a1, a2]
  exact binomial_window_log_concave k

/-! ## Layer 1: the four arithmetic scenarios, and why each is log-concave -/

/-- The four possible shapes of the tested triple
`(a, b, c) = (g_{d-2}, g_{d-1}, g_d)` after the paper's structural analysis. -/
def GoodTriple (d a b c : ℤ) : Prop :=
  -- ε_d = 1 (p. 3): a window (N_m, N_{m-1}, N_{m-2}) with m = e - d + 2 ≥ 2
  (∃ m : ℤ, 2 ≤ m ∧ a = Nz m ∧ b = Nz (m - 1) ∧ c = Nz (m - 2))
  ∨
  -- Δ²g_d ≤ 0: covers r_d = 2 (via (4)) and the non-failure branch of r_d = 1
  (a + c ≤ 2 * b)
  ∨
  -- r_d = 0 (p. 3): Q_d = 0 forces the explicit values
  (∃ p : ℤ, 0 ≤ p ∧ a = d * (d - 1) ∧ b = d * (d + 1) ∧ c = (d + 1) * (d + 2) - p)
  ∨
  -- r_d = 1, putative failure (pp. 3–4): (6) plus x ≥ d and a ≤ d(d-1)
  (c = 2 * b - a + 1 ∧ d ≤ b - a ∧ a ≤ d * (d - 1))

/-- The AM–GM step of the paper (p. 2, between (4) and (5)). -/
lemma amgm_log_concave {a b c : ℤ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (h : a + c ≤ 2 * b) : a * c ≤ b ^ 2 := by
  nlinarith [sq_nonneg (a - c), sq_nonneg (a + c)]

/-- **Scenario r_d = 0** (p. 3): the direct calculation
`g_{d-1}² − g_{d-2} g_d = d(2(d+1) + (d−1) p_d) > 0`. -/
lemma r_eq_zero_log_concave {d p : ℤ} (hd : 2 ≤ d) (hp : 0 ≤ p) :
    d * (d - 1) * ((d + 1) * (d + 2) - p) < (d * (d + 1)) ^ 2 := by
  have key : (d * (d + 1)) ^ 2 - d * (d - 1) * ((d + 1) * (d + 2) - p)
      = d * (2 * (d + 1) + (d - 1) * p) := by ring
  have h1 : 0 ≤ (d - 1) * p := mul_nonneg (by linarith) hp
  nlinarith [key, h1]

/-- **Scenario r_d = 1, putative failure** (p. 4): with `x = b − a ≥ d` and
`y = a ≤ d(d−1)`, the margin is
`b² − ac = (y+x)² − y(y+2x+1) = x² − y ≥ d² − d(d−1) = d > 0`. -/
lemma r_eq_one_log_concave {d a b c : ℤ} (hd : 2 ≤ d) (hc : c = 2 * b - a + 1)
    (hx : d ≤ b - a) (ha2 : a ≤ d * (d - 1)) : a * c < b ^ 2 := by
  subst hc
  have hsq : d ^ 2 ≤ (b - a) ^ 2 := by nlinarith
  nlinarith [hsq]

/-- **Every scenario yields log-concavity of the tested triple** — the
complete case analysis of pp. 3–4 of the paper. -/
theorem GoodTriple.log_concave {d a b c : ℤ} (hd : 2 ≤ d)
    (ha : 0 ≤ a) (hc : 0 ≤ c) (h : GoodTriple d a b c) : a * c ≤ b ^ 2 := by
  rcases h with ⟨m, hm, rfl, rfl, rfl⟩ | h | ⟨p, hp, rfl, rfl, rfl⟩ | ⟨hceq, hx, ha2⟩
  · exact Nz_window m hm
  · exact amgm_log_concave ha hc h
  · exact le_of_lt (r_eq_zero_log_concave hd hp)
  · exact le_of_lt (r_eq_one_log_concave hd hceq hx ha2)

/-! ## Layer 2: from the resolution numerics to the scenarios

The finite sums `Σ_b f(b) · Nz(t − b)` over shifts `b ∈ [0, u]` are the
graded dimension counts contributed by a free module `⊕_b R(−b)^{f(b)}`. -/

/-- `shiftSum u f t = Σ_{b=0}^{u} f b · Nz (t − b)`: the degree-`t` dimension
of the graded free module with `f b` summands `R(−b)`. -/
noncomputable def shiftSum (u : ℤ) (f : ℤ → ℤ) (t : ℤ) : ℤ :=
  ∑ b ∈ Finset.Icc (0 : ℤ) u, f b * Nz (t - b)

/-- If all coefficients with shift ≤ `t` vanish, the sum vanishes. -/
lemma shiftSum_vanish (u : ℤ) (f : ℤ → ℤ) (t : ℤ)
    (hlow : ∀ b, 0 ≤ b → b ≤ t → f b = 0) : shiftSum u f t = 0 := by
  refine Finset.sum_eq_zero fun b hb => ?_
  by_cases h : b ≤ t
  · rw [hlow b (Finset.mem_Icc.mp hb).1 h, zero_mul]
  · rw [Nz_neg _ (by omega), mul_zero]

/-- If all coefficients with shift < `t` vanish, only the shift-`t` term
survives. -/
lemma shiftSum_single (u : ℤ) (f : ℤ → ℤ) (t : ℤ) (h0 : 0 ≤ t) (htu : t ≤ u)
    (hlow : ∀ b, 0 ≤ b → b < t → f b = 0) : shiftSum u f t = f t := by
  have hside : ∀ b ∈ Finset.Icc (0 : ℤ) u, b ≠ t → f b * Nz (t - b) = 0 := by
    intro b hb hbne
    by_cases hlt : b < t
    · rw [hlow b (Finset.mem_Icc.mp hb).1 hlt, zero_mul]
    · rw [Nz_neg _ (by omega), mul_zero]
  rw [shiftSum,
    Finset.sum_eq_single_of_mem t (Finset.mem_Icc.mpr ⟨h0, htu⟩) hside,
    sub_self, Nz_zero, mul_one]

/-- **The Hilbert-numerator computation** (paper p. 2, "summing its
coefficients through degree d"): the second difference of a shift sum
telescopes to the partial coefficient sum `Σ_{b ≤ d} f b`. -/
lemma shiftSum_second_diff (u : ℤ) (f : ℤ → ℤ) (d : ℤ) (_hd0 : 0 ≤ d)
    (hdu : d ≤ u) :
    shiftSum u f d - 2 * shiftSum u f (d - 1) + shiftSum u f (d - 2)
      = ∑ b ∈ Finset.Icc (0 : ℤ) d, f b := by
  have step : ∀ b ∈ Finset.Icc (0 : ℤ) u,
      f b * Nz (d - b) - 2 * (f b * Nz (d - 1 - b)) + f b * Nz (d - 2 - b)
        = if b ≤ d then f b else 0 := by
    intro b _
    have e1 : d - 1 - b = d - b - 1 := by ring
    have e2 : d - 2 - b = d - b - 2 := by ring
    rw [e1, e2]
    have h := Nz_second_diff (d - b)
    by_cases hbd : b ≤ d
    · rw [if_pos hbd]
      rw [if_pos (by omega : (0 : ℤ) ≤ d - b)] at h
      linear_combination f b * h
    · rw [if_neg hbd]
      rw [if_neg (by omega : ¬(0 : ℤ) ≤ d - b)] at h
      linear_combination f b * h
  unfold shiftSum
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
    Finset.sum_congr rfl step, ← Finset.sum_filter]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_Icc]
  omega

/-- **The deep dispatch** (pp. 2–4 of the paper).  From the primitive
numerical hypotheses — rank additivity `hres` of the exact complex (1), the
rank estimate `h3` (= (3)), and the structural facts `hε1`, `hr0`, `hr1` —
derive that every tested triple of the reindexed dual falls into one of the
four scenarios.  All the arithmetic of the paper (deriving (4), (5) ⇒ (6),
(9), `x ≥ d`, `g_{d-2} ≤ d(d-1)`) is machine-checked here. -/
theorem deep_dispatch
    (e : ℤ) (g h p q r ε : ℤ → ℤ)
    (hquot : ∀ t, h t ≤ Nz t)
    (hrev : ∀ t, g t = h (e - t))
    (hp0 : ∀ b, 0 ≤ p b) (hq0 : ∀ b, 0 ≤ q b)
    (hres : ∀ t, t ≤ e →
      g t = 2 * Nz t - shiftSum (e + 3) p t + shiftSum (e + 3) q t
              - Nz (t - (e + 3)))
    (hrε : ∀ d, 2 ≤ d → d ≤ e →
      (r d = 0 ∨ r d = 1 ∨ r d = 2) ∧ (ε d = 0 ∨ ε d = 1))
    (h3 : ∀ d, 2 ≤ d → d ≤ e →
      (∑ b ∈ Finset.Icc (0 : ℤ) d, q b) - ε d
        ≤ (∑ b ∈ Finset.Icc (0 : ℤ) (d - 1), p b) - r d)
    (hε1 : ∀ d, 2 ≤ d → d ≤ e → ε d = 1 →
      ∀ t, t < e + 3 - d → h t = Nz t)
    (hr0 : ∀ d, 2 ≤ d → d ≤ e → r d = 0 →
      ∑ b ∈ Finset.Icc (0 : ℤ) (d - 1), p b = 0)
    (hr1 : ∀ d, 2 ≤ d → d ≤ e → r d = 1 → p d = 0 →
      g d - 2 * g (d - 1) + g (d - 2) = 1 →
      ∃ (a : ℤ) (B : ℤ → ℤ), 0 ≤ a ∧ a < d ∧ (∀ t : ℤ, t < 0 → B t = 0) ∧
        (∀ t, 0 ≤ B t) ∧ (∀ t, B t ≤ Nz t) ∧
        (∀ i j : ℤ, 0 ≤ j → j ≤ i → 2 * i ≤ e - a → B j ≤ B i) ∧
        (∀ t, d - 2 ≤ t → t ≤ d → g t = 2 * Nz t - Nz (t - a) + B (t - a))) :
    ∀ d, 2 ≤ d → d ≤ e → GoodTriple d (g (d - 2)) (g (d - 1)) (g d) := by
  intro d hd hde
  obtain ⟨hrc, hεc⟩ := hrε d hd hde
  -- the second-difference identity Δ²g_d = 2 − P_{≤d} + Q_d  (paper p. 2)
  have hs2p := shiftSum_second_diff (e + 3) p d (by omega) (by omega)
  have hs2q := shiftSum_second_diff (e + 3) q d (by omega) (by omega)
  have hNdd := Nz_second_diff d
  rw [if_pos (by omega : (0 : ℤ) ≤ d)] at hNdd
  have hz0 : Nz (d - (e + 3)) = 0 := Nz_neg _ (by omega)
  have hz1 : Nz (d - 1 - (e + 3)) = 0 := Nz_neg _ (by omega)
  have hz2 : Nz (d - 2 - (e + 3)) = 0 := Nz_neg _ (by omega)
  have hΔ : g d - 2 * g (d - 1) + g (d - 2)
      = 2 - (∑ b ∈ Finset.Icc (0 : ℤ) d, p b)
          + (∑ b ∈ Finset.Icc (0 : ℤ) d, q b) := by
    have h₁ := hres d (by omega)
    have h₂ := hres (d - 1) (by omega)
    have h₃ := hres (d - 2) (by omega)
    linarith
  -- split off the top coefficient: P_{≤d} = p_d + P_{<d}
  have hsplitp : (∑ b ∈ Finset.Icc (0 : ℤ) d, p b)
      = p d + ∑ b ∈ Finset.Icc (0 : ℤ) (d - 1), p b := by
    have hins : Finset.Icc (0 : ℤ) d = insert d (Finset.Icc (0 : ℤ) (d - 1)) := by
      ext x
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
    rw [hins, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]
  rcases hεc with hε0 | hεone
  · -- ε_d = 0: dispatch on r_d
    have h3' := h3 d hd hde
    rw [hε0] at h3'
    rcases hrc with hr' | hr' | hr'
    · -- r_d = 0 (paper p. 3, third case)
      rw [hr'] at h3'
      have hP0 := hr0 d hd hde hr'
      have hpz : ∀ b, 0 ≤ b → b ≤ d - 1 → p b = 0 := fun b hb0 hbd =>
        (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => hp0 b)).mp hP0 b
          (Finset.mem_Icc.mpr ⟨hb0, hbd⟩)
      have hQ0 : (∑ b ∈ Finset.Icc (0 : ℤ) d, q b) = 0 := by
        have hQnn : 0 ≤ ∑ b ∈ Finset.Icc (0 : ℤ) d, q b :=
          Finset.sum_nonneg fun b _ => hq0 b
        linarith
      have hqz : ∀ b, 0 ≤ b → b ≤ d → q b = 0 := fun b hb0 hbd =>
        (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => hq0 b)).mp hQ0 b
          (Finset.mem_Icc.mpr ⟨hb0, hbd⟩)
      -- evaluate g at d−2, d−1, d: only 2·Nz and the p_d term survive
      have ea : g (d - 2) = d * (d - 1) := by
        have h₁ := hres (d - 2) (by omega)
        have h₂ : shiftSum (e + 3) p (d - 2) = 0 :=
          shiftSum_vanish _ _ _ fun b hb0 hbt => hpz b hb0 (by omega)
        have h₃ : shiftSum (e + 3) q (d - 2) = 0 :=
          shiftSum_vanish _ _ _ fun b hb0 hbt => hqz b hb0 (by omega)
        have h₄ := two_mul_Nz (d - 2) (by omega)
        linarith
      have eb : g (d - 1) = d * (d + 1) := by
        have h₁ := hres (d - 1) (by omega)
        have h₂ : shiftSum (e + 3) p (d - 1) = 0 :=
          shiftSum_vanish _ _ _ fun b hb0 hbt => hpz b hb0 (by omega)
        have h₃ : shiftSum (e + 3) q (d - 1) = 0 :=
          shiftSum_vanish _ _ _ fun b hb0 hbt => hqz b hb0 (by omega)
        have h₄ := two_mul_Nz (d - 1) (by omega)
        linarith
      have ec : g d = (d + 1) * (d + 2) - p d := by
        have h₁ := hres d (by omega)
        have h₂ : shiftSum (e + 3) p d = p d :=
          shiftSum_single _ _ _ (by omega) (by omega)
            fun b hb0 hbd => hpz b hb0 (by omega)
        have h₃ : shiftSum (e + 3) q d = 0 :=
          shiftSum_vanish _ _ _ fun b hb0 hbt => hqz b hb0 (by omega)
        have h₄ := two_mul_Nz d (by omega)
        linarith
      exact Or.inr (Or.inr (Or.inl ⟨p d, hp0 d, ea, eb, ec⟩))
    · -- r_d = 1: derive Δ² ≤ 1 − p_d; a failure forces (6)
      rw [hr'] at h3'
      by_cases hΔ0 : g d - 2 * g (d - 1) + g (d - 2) ≤ 0
      · exact Or.inr (Or.inl (by linarith))
      · have hpos := not_le.mp hΔ0
        have hone : (1 : ℤ) ≤ g d - 2 * g (d - 1) + g (d - 2) := by
          have := Int.add_one_le_iff.mpr hpos
          linarith
        have hpd0 : p d = 0 := le_antisymm (by linarith) (hp0 d)
        have hΔeq : g d - 2 * g (d - 1) + g (d - 2) = 1 :=
          le_antisymm (by linarith) hone
        obtain ⟨a, B, ha0, had, hBneg, hB0, hBN, hStan, h8⟩ :=
          hr1 d hd hde hr' hpd0 hΔeq
        have h8a := h8 (d - 2) (by omega) (by omega)
        have h8b := h8 (d - 1) (by omega) (by omega)
        -- inequality (9): 2d ≤ e + 2, via N_{d-1} ≤ g_{d-1} ≤ N_{e-d+1}
        have hb_lb : Nz (d - 1) ≤ g (d - 1) := by
          have hmono : Nz (d - 1 - a) ≤ Nz (d - 1) := Nz_mono (by omega)
          have := hB0 (d - 1 - a)
          linarith
        have hb_ub : g (d - 1) ≤ Nz (e - d + 1) := by
          rw [hrev, show e - (d - 1) = e - d + 1 from by ring]
          exact hquot _
        have h9 : 2 * d ≤ e + 2 := by
          by_contra hcon
          have hcon' : e + 2 < 2 * d := by omega
          have hlt : Nz (e - d + 1) < Nz (d - 1) := Nz_lt (by omega) (by omega)
          linarith
        -- D = B_{n-1} − B_{n-2} ≥ 0 by Stanley's monotonicity (Lemma 1)
        have hD : B (d - 2 - a) ≤ B (d - 1 - a) := by
          by_cases hn2 : 0 ≤ d - 2 - a
          · exact hStan (d - 1 - a) (d - 2 - a) hn2 (by omega) (by linarith)
          · rw [hBneg _ (by omega)]
            exact hB0 _
        -- x = g_{d-1} − g_{d-2} = 2d − (d − a) + D = d + a + D ≥ d  (p. 4)
        have hdiff1 : Nz (d - 1) - Nz (d - 2) = d := by
          have hdd := Nz_diff (d - 1) (by omega)
          rw [show d - 1 - 1 = d - 2 from by ring] at hdd
          linarith
        have hdiff2 : Nz (d - 1 - a) - Nz (d - 2 - a) = d - a := by
          have hdd := Nz_diff (d - 1 - a) (by omega)
          rw [show d - 1 - a - 1 = d - 2 - a from by ring] at hdd
          linarith
        have hx : d ≤ g (d - 1) - g (d - 2) := by linarith
        -- g_{d-2} ≤ 2 N_{d-2} = d(d-1)  (p. 4)
        have hab : g (d - 2) ≤ d * (d - 1) := by
          have hBb : B (d - 2 - a) ≤ Nz (d - 2 - a) := hBN _
          have h₄ := two_mul_Nz (d - 2) (by omega)
          linarith
        exact Or.inr (Or.inr (Or.inr ⟨by linarith, hx, hab⟩))
    · -- r_d = 2: (4) gives Δ²g_d ≤ −p_d ≤ 0
      rw [hr'] at h3'
      have hpd := hp0 d
      exact Or.inr (Or.inl (by linarith))
  · -- ε_d = 1 (paper p. 3, first case): the triple is a window of Nz
    refine Or.inl ⟨e - d + 2, by omega, ?_, ?_, ?_⟩
    · have hval := hε1 d hd hde hεone (e - d + 2) (by omega)
      rw [hrev, show e - (d - 2) = e - d + 2 from by ring, hval]
    · have hval := hε1 d hd hde hεone (e - d + 1) (by omega)
      rw [hrev, show e - (d - 1) = e - d + 1 from by ring, hval]
      congr 1
      ring
    · have hval := hε1 d hd hde hεone (e - d) (by omega)
      rw [hrev, hval]
      congr 1
      ring

/-! ## Assembling the theorem -/

/-- Log-concavity of the reindexed dual at every tested center. -/
theorem dual_log_concave (e : ℤ) (g : ℤ → ℤ) (gnn : ∀ t, 0 ≤ g t)
    (hgood : ∀ d : ℤ, 2 ≤ d → d ≤ e →
      GoodTriple d (g (d - 2)) (g (d - 1)) (g d)) :
    ∀ d : ℤ, 2 ≤ d → d ≤ e → g (d - 2) * g d ≤ g (d - 1) ^ 2 :=
  fun d h2 he => (hgood d h2 he).log_concave h2 (gnn _) (gnn _)

/-- **Theorem 1, scenario form**: if every tested triple of the reindexed
dual is a `GoodTriple`, then `h` is log-concave.  (Reversal preserves
log-concavity, paper p. 4.) -/
theorem theorem1 (e : ℤ) (h g : ℤ → ℤ)
    (hnn : ∀ t, 0 ≤ h t)
    (hrev : ∀ t, g t = h (e - t))
    (hgood : ∀ d : ℤ, 2 ≤ d → d ≤ e →
      GoodTriple d (g (d - 2)) (g (d - 1)) (g d)) :
    ∀ i : ℤ, 1 ≤ i → i ≤ e - 1 → h (i - 1) * h (i + 1) ≤ h i ^ 2 := by
  intro i h1 hie
  have gnn : ∀ t, 0 ≤ g t := fun t => by rw [hrev]; exact hnn _
  have key := dual_log_concave e g gnn hgood (e - i + 1) (by linarith) (by linarith)
  have e2 : g (e - i + 1 - 2) = h (i + 1) := by rw [hrev]; congr 1; ring
  have e1 : g (e - i + 1 - 1) = h i := by rw [hrev]; congr 1; ring
  have e0 : g (e - i + 1) = h (i - 1) := by rw [hrev]; congr 1; ring
  rw [e2, e1, e0] at key
  linarith [key, mul_comm (h (i + 1)) (h (i - 1))]

/-- **Theorem 1, full form.**  Log-concavity of the Hilbert function of a
standard graded Artinian level algebra of embedding dimension three, socle
degree `e`, and type two — derived from the primitive numerical shadows of
the paper's commutative algebra (see the header of this file for the exact
list of assumed structural facts `hrev, hquot, hres, hrε, h3, hε1, hr0, hr1`
and their sources in the paper). -/
theorem theorem1_full
    (e : ℤ) (h g p q r ε : ℤ → ℤ)
    (hnn : ∀ t, 0 ≤ h t)
    (hquot : ∀ t, h t ≤ Nz t)
    (hrev : ∀ t, g t = h (e - t))
    (hp0 : ∀ b, 0 ≤ p b) (hq0 : ∀ b, 0 ≤ q b)
    (hres : ∀ t, t ≤ e →
      g t = 2 * Nz t - shiftSum (e + 3) p t + shiftSum (e + 3) q t
              - Nz (t - (e + 3)))
    (hrε : ∀ d, 2 ≤ d → d ≤ e →
      (r d = 0 ∨ r d = 1 ∨ r d = 2) ∧ (ε d = 0 ∨ ε d = 1))
    (h3 : ∀ d, 2 ≤ d → d ≤ e →
      (∑ b ∈ Finset.Icc (0 : ℤ) d, q b) - ε d
        ≤ (∑ b ∈ Finset.Icc (0 : ℤ) (d - 1), p b) - r d)
    (hε1 : ∀ d, 2 ≤ d → d ≤ e → ε d = 1 →
      ∀ t, t < e + 3 - d → h t = Nz t)
    (hr0 : ∀ d, 2 ≤ d → d ≤ e → r d = 0 →
      ∑ b ∈ Finset.Icc (0 : ℤ) (d - 1), p b = 0)
    (hr1 : ∀ d, 2 ≤ d → d ≤ e → r d = 1 → p d = 0 →
      g d - 2 * g (d - 1) + g (d - 2) = 1 →
      ∃ (a : ℤ) (B : ℤ → ℤ), 0 ≤ a ∧ a < d ∧ (∀ t : ℤ, t < 0 → B t = 0) ∧
        (∀ t, 0 ≤ B t) ∧ (∀ t, B t ≤ Nz t) ∧
        (∀ i j : ℤ, 0 ≤ j → j ≤ i → 2 * i ≤ e - a → B j ≤ B i) ∧
        (∀ t, d - 2 ≤ t → t ≤ d → g t = 2 * Nz t - Nz (t - a) + B (t - a))) :
    ∀ i : ℤ, 1 ≤ i → i ≤ e - 1 → h (i - 1) * h (i + 1) ≤ h i ^ 2 :=
  theorem1 e h g hnn hrev
    (deep_dispatch e g h p q r ε hquot hrev hp0 hq0 hres hrε h3 hε1 hr0 hr1)

/-! ## Non-vacuity: a concrete instance satisfying every hypothesis

A theorem from hypotheses is only meaningful if the hypotheses are mutually
consistent.  We certify this with a genuine example: the standard graded
Artinian level algebra `A = R / Ann(X², Y² + XZ)` of embedding dimension 3,
socle degree `e = 2`, type two, with Hilbert function `h = (1, 3, 2)`.
Its Hilbert numerator is `(1-t)³(1+3t+2t²) = 1 - 4t² + 2t³ + 3t⁴ - 2t⁵`,
giving the minimal resolution `0 → R(-5)² → R(-3)²⊕R(-4)³ → R(-2)⁴ → R → A`;
dualizing (paper (1), `s = 5`) yields `F₁ = R(-1)³ ⊕ R(-2)²` (so
`p₁ = 3, p₂ = 2`) and `F₂ = R(-3)⁴` (so `q₃ = 4`), with rank data
`r₂ = 2`, `ε₂ = 0`.  Below, every hypothesis of `theorem1_full` is verified
for this data — so the hypothesis set is consistent and the theorem has
genuine content. -/

section Nonvacuity

/-- Hilbert function `h = (1, 3, 2)` of `A = R/Ann(X², Y² + XZ)`. -/
def hEx : ℤ → ℤ := fun i =>
  if i = 0 then 1 else if i = 1 then 3 else if i = 2 then 2 else 0

/-- Its reindexed Matlis dual, `g t = h (e - t)` with `e = 2`. -/
def gEx : ℤ → ℤ := fun t => hEx (2 - t)

/-- Betti data of `F₁ = R(-1)³ ⊕ R(-2)²`. -/
def pEx : ℤ → ℤ := fun b => if b = 1 then 3 else if b = 2 then 2 else 0

/-- Betti data of `F₂ = R(-3)⁴`. -/
def qEx : ℤ → ℤ := fun b => if b = 3 then 4 else 0

lemma shiftSum_pEx (t : ℤ) :
    shiftSum 5 pEx t = 3 * Nz (t - 1) + 2 * Nz (t - 2) := by
  have hsub : ({1, 2} : Finset ℤ) ⊆ Finset.Icc (0 : ℤ) 5 := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_Icc]
    omega
  have hzero : ∀ x ∈ Finset.Icc (0 : ℤ) 5, x ∉ ({1, 2} : Finset ℤ) →
      pEx x * Nz (t - x) = 0 := by
    intro x _ hnot
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
    simp [pEx, hnot.1, hnot.2]
  rw [shiftSum, ← Finset.sum_subset hsub hzero,
    Finset.sum_insert (by norm_num), Finset.sum_singleton]
  norm_num [pEx]

lemma shiftSum_qEx (t : ℤ) : shiftSum 5 qEx t = 4 * Nz (t - 3) := by
  have hsub : ({3} : Finset ℤ) ⊆ Finset.Icc (0 : ℤ) 5 := by
    intro x hx
    simp only [Finset.mem_singleton] at hx
    simp only [Finset.mem_Icc]
    omega
  have hzero : ∀ x ∈ Finset.Icc (0 : ℤ) 5, x ∉ ({3} : Finset ℤ) →
      qEx x * Nz (t - x) = 0 := by
    intro x _ hnot
    simp only [Finset.mem_singleton] at hnot
    simp [qEx, hnot]
  rw [shiftSum, ← Finset.sum_subset hsub hzero, Finset.sum_singleton]
  norm_num [qEx]

/-- Rank additivity (paper (1)) holds numerically for this resolution. -/
lemma hresEx : ∀ t : ℤ, t ≤ 2 →
    gEx t = 2 * Nz t - shiftSum 5 pEx t + shiftSum 5 qEx t - Nz (t - 5) := by
  intro t ht
  rw [shiftSum_pEx, shiftSum_qEx]
  by_cases h0 : t = 0
  · subst h0; decide
  by_cases h1 : t = 1
  · subst h1; decide
  by_cases h2 : t = 2
  · subst h2; decide
  · have hneg : t < 0 := by omega
    have z1 : gEx t = 0 := by
      have c0 : ¬(2 - t = 0) := by omega
      have c1 : ¬(2 - t = 1) := by omega
      have c2 : ¬(2 - t = 2) := by omega
      simp [gEx, hEx, c0, c1, c2]
    rw [z1, Nz_neg t hneg, Nz_neg _ (by omega : t - 1 < 0),
      Nz_neg _ (by omega : t - 2 < 0), Nz_neg _ (by omega : t - 3 < 0),
      Nz_neg _ (by omega : t - 5 < 0)]
    ring

/-- The rank estimate (3) holds: `Q₂ - ε₂ = 0 ≤ P_{<2} - r₂ = 3 - 2`. -/
lemma h3Ex : ∀ d : ℤ, 2 ≤ d → d ≤ 2 →
    (∑ b ∈ Finset.Icc (0 : ℤ) d, qEx b) - 0
      ≤ (∑ b ∈ Finset.Icc (0 : ℤ) (d - 1), pEx b) - 2 := by
  intro d hd hde
  have hd2 : d = 2 := by omega
  subst hd2
  have hq : (∑ b ∈ Finset.Icc (0 : ℤ) 2, qEx b) = 0 := by
    refine Finset.sum_eq_zero fun b hb => ?_
    simp only [Finset.mem_Icc] at hb
    have : ¬(b = 3) := by omega
    simp [qEx, this]
  have hp : (∑ b ∈ Finset.Icc (0 : ℤ) (2 - 1 : ℤ), pEx b) = 3 := by
    have hicc : Finset.Icc (0 : ℤ) (2 - 1 : ℤ) = {0, 1} := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
      omega
    rw [hicc, Finset.sum_insert (by norm_num), Finset.sum_singleton]
    norm_num [pEx]
  rw [hq, hp]
  norm_num

/-- **Non-vacuity certificate**: all hypotheses of `theorem1_full` are
satisfied by the concrete data of `A = R/Ann(X², Y² + XZ)`, and the theorem
delivers log-concavity of its Hilbert function `(1, 3, 2)`. -/
theorem nonvacuity :
    ∀ i : ℤ, 1 ≤ i → i ≤ 2 - 1 → hEx (i - 1) * hEx (i + 1) ≤ hEx i ^ 2 := by
  refine theorem1_full 2 hEx gEx pEx qEx (fun _ => 2) (fun _ => 0)
    ?_ ?_ (fun _ => rfl) ?_ ?_ hresEx ?_ h3Ex ?_ ?_ ?_
  · intro t; simp only [hEx]; split_ifs <;> norm_num
  · intro t
    by_cases h0 : t = 0
    · subst h0; decide
    by_cases h1 : t = 1
    · subst h1; decide
    by_cases h2 : t = 2
    · subst h2; decide
    · simp only [hEx, if_neg h0, if_neg h1, if_neg h2]
      exact Nz_nonneg t
  · intro b; simp only [pEx]; split_ifs <;> norm_num
  · intro b; simp only [qEx]; split_ifs <;> norm_num
  · intro d _ _; exact ⟨Or.inr (Or.inr rfl), Or.inl rfl⟩
  · intro d _ _ hcontra; norm_num at hcontra
  · intro d _ _ hcontra; norm_num at hcontra
  · intro d _ _ hcontra; norm_num at hcontra

/-- The concrete inequality delivered: `h₀ h₂ = 2 ≤ 9 = h₁²`. -/
example : hEx 0 * hEx 2 ≤ hEx 1 ^ 2 := nonvacuity 1 (by norm_num) (by norm_num)

example : hEx 0 = 1 ∧ hEx 1 = 3 ∧ hEx 2 = 2 := by decide

end Nonvacuity

/-! ## Axiom audit

Only Lean's standard foundational axioms (`propext`, `Classical.choice`,
`Quot.sound`) — no `sorry`, no extra axioms. -/

#print axioms theorem1_full
#print axioms nonvacuity
#print axioms deep_dispatch
#print axioms theorem1
#print axioms GoodTriple.log_concave
#print axioms shiftSum_second_diff
#print axioms binomial_window_log_concave

end LogConcavity
