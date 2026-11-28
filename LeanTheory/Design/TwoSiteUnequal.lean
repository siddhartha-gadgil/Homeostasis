/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Design.TwoSiteMonostable

/-!
# Two-site phosphorylation with unequal enzyme totals (notes N-010, Q-2)

At the witness rates `twoK`, a positive steady state is determined by `(S₀, F, r)` with
`r = E/F`: `S₁ = rS₀`, `S₂ = r²S₀`, `E = rF` (`TwoTotals.reduced`). The totals become

* `rF(1 + S₀(2 + r)) = E_tot`, `F(1 + S₀r(2r + 1)) = F_tot`,
* `S₀(1 + r + r²) + 3S₀rF(1 + r) = S_tot`.

Eliminating `S₀` and `F` (`two_reduced_Q`): `S₀ r G(r) = F_tot r − E_tot` with
`G(r) = (2E_tot − F_tot) r + (E_tot − 2F_tot)`, and `r` is a root of the quartic `twoQ`, which is
linear in `S_tot`: `Q = A(r) + S_tot B(r)`, `B = −2r(r − 1)G(r)`.

**Monostability when one enzyme total is at least twice the other.** If `F_tot ≥ 2E_tot`, then
`G < 0`, so feasibility forces `r < E_tot/F_tot`. On that interval two roots `r ≠ s` would give
`(r − s) H(r, s) = Q(r)B(s) − Q(s)B(r) = 0`, but `H > 0` there: after the substitution
`F_tot = E_tot(2 + m)`, `r = u/((1 + u)(2 + m))` the numerator of `H` is a polynomial in
`(u, v, E_tot, m)` with **175 positive coefficients** (`twoH_pos`, sympy oracle). Existence comes
from the intermediate value theorem: `Q(0) = 2E_tot > 0` and
`Q(E_tot/F_tot) = −4E_tot S_tot (E_tot − F_tot)²(E_tot + F_tot)/F_tot³ < 0`. The network is
symmetric under `S₀ ↔ S₂`, `E ↔ F` at the witness rates (`twoSwap`), which covers `E_tot ≥ 2F_tot`.

`two_totals_existsUnique`: **for all `S_tot > 0`, every class with `F_tot ≥ 2E_tot` or
`E_tot ≥ 2F_tot` has exactly one positive steady state.**

For `E_tot < F_tot < 2E_tot` the class is multistationary for large `S_tot`, so the ratio 2 is sharp
(`Design/TwoSiteRatio`, `two_monostable_iff`). The unique state is locally exponentially stable in
its class (`Design/TwoSiteStability`, `two_totals_classStable`).

Label: exact, idealized; witness rates `twoK`; all classes with `max/min ≥ 2` enzyme ratio.
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN.Design

open Matrix ReactionNetwork Set

/-- The quartic in `r = E/F` whose roots are the steady states (cleared of denominators). -/
def twoQ (Et Ft St r : ℝ) : ℝ :=
  2 * Ft * r ^ 4 + (6 * Et * Ft - 4 * Et * St - 2 * Et - 3 * Ft ^ 2 + 2 * Ft * St) * r ^ 3
    - 2 * (3 * Et ^ 2 - 3 * Et * Ft - Et * St + 3 * Ft ^ 2 - Ft * St) * r ^ 2
    + (-3 * Et ^ 2 + 6 * Et * Ft + 2 * Et * St - 4 * Ft * St - 2 * Ft) * r + 2 * Et

/-- The `S_tot`-coefficient of `twoQ`. -/
def twoBq (Et Ft r : ℝ) : ℝ := -2 * r * (r - 1) * ((2 * Et - Ft) * r + (Et - 2 * Ft))

/-- The certificate polynomial `H(r, s)` with `(r − s) H = Q(r)B(s) − Q(s)B(r)`. -/
def twoH (Et Ft r s : ℝ) : ℝ :=
  -24 * Et ^ 3 * r ^ 2 * s ^ 2 - 12 * Et ^ 3 * r ^ 2 * s - 12 * Et ^ 3 * r * s ^ 2 - 6 * Et ^ 3 *
    r * s + 48 * Et ^ 2 * Ft * r ^ 2 * s ^ 2 + 42 * Et ^ 2 * Ft * r ^ 2 * s + 42 * Et ^ 2 * Ft * r
    * s ^ 2 + 30 * Et ^ 2 * Ft * r * s - 4 * Et ^ 2 * r ^ 2 * s ^ 2 - 4 * Et ^ 2 * r ^ 2 * s + 8 *
    Et ^ 2 * r ^ 2 - 4 * Et ^ 2 * r * s ^ 2 + 8 * Et ^ 2 * r * s - 4 * Et ^ 2 * r + 8 * Et ^ 2 * s
    ^ 2 - 4 * Et ^ 2 * s - 4 * Et ^ 2 - 30 * Et * Ft ^ 2 * r ^ 2 * s ^ 2 - 42 * Et * Ft ^ 2 * r ^
    2 * s - 42 * Et * Ft ^ 2 * r * s ^ 2 - 48 * Et * Ft ^ 2 * r * s - 8 * Et * Ft * r ^ 3 * s ^ 3
    + 4 * Et * Ft * r ^ 3 * s ^ 2 + 4 * Et * Ft * r ^ 3 * s + 4 * Et * Ft * r ^ 2 * s ^ 3 - 4 * Et
    * Ft * r ^ 2 + 4 * Et * Ft * r * s ^ 3 - 4 * Et * Ft * r - 4 * Et * Ft * s ^ 2 - 4 * Et * Ft *
    s + 8 * Et * Ft + 6 * Ft ^ 3 * r ^ 2 * s ^ 2 + 12 * Ft ^ 3 * r ^ 2 * s + 12 * Ft ^ 3 * r * s ^
    2 + 24 * Ft ^ 3 * r * s + 4 * Ft ^ 2 * r ^ 3 * s ^ 3 + 4 * Ft ^ 2 * r ^ 3 * s ^ 2 - 8 * Ft ^ 2
    * r ^ 3 * s + 4 * Ft ^ 2 * r ^ 2 * s ^ 3 - 8 * Ft ^ 2 * r ^ 2 * s ^ 2 + 4 * Ft ^ 2 * r ^ 2 * s
    - 8 * Ft ^ 2 * r * s ^ 3 + 4 * Ft ^ 2 * r * s ^ 2 + 4 * Ft ^ 2 * r * s

/-- The elimination cofactor `W`. -/
def twoWc (Et Ft St a r : ℝ) : ℝ :=
  -6 * Et * Ft * r ^ 4 - 9 * Et * Ft * r ^ 3 - 3 * Et * Ft * r ^ 2 + 4 * Et * St * r ^ 4 + 4 * Et
    * St * r ^ 3 + Et * St * r ^ 2 - 4 * Et * a * r ^ 6 - 8 * Et * a * r ^ 5 - 9 * Et * a * r ^ 4
    - 5 * Et * a * r ^ 3 - Et * a * r ^ 2 + 3 * Ft ^ 2 * r ^ 4 + 9 * Ft ^ 2 * r ^ 3 + 6 * Ft ^ 2 *
    r ^ 2 - 2 * Ft * St * r ^ 4 - 5 * Ft * St * r ^ 3 - 2 * Ft * St * r ^ 2 + 2 * Ft * a * r ^ 6 +
    7 * Ft * a * r ^ 5 + 9 * Ft * a * r ^ 4 + 7 * Ft * a * r ^ 3 + 2 * Ft * a * r ^ 2 - 2 * Ft * r
    ^ 5 - 2 * Ft * r ^ 4 + 2 * Ft * r ^ 2 + 2 * Ft * r

/-- Part 0 of the numerator of `twoH` after substitution (positive coefficients). -/
def twoHnum_0 (Et m u v : ℝ) : ℝ :=
  24 * u ^ 3 * v ^ 3 * Et ^ 3 * m ^ 6 + 264 * u ^ 3 * v ^ 3 * Et ^ 3 * m ^ 5 + 1152 * u ^ 3 * v ^
    3 * Et ^ 3 * m ^ 4 + 2544 * u ^ 3 * v ^ 3 * Et ^ 3 * m ^ 3 + 3000 * u ^ 3 * v ^ 3 * Et ^ 3 * m
    ^ 2 + 1800 * u ^ 3 * v ^ 3 * Et ^ 3 * m + 432 * u ^ 3 * v ^ 3 * Et ^ 3 + 8 * u ^ 3 * v ^ 3 *
    Et ^ 2 * m ^ 6 + 88 * u ^ 3 * v ^ 3 * Et ^ 2 * m ^ 5 + 392 * u ^ 3 * v ^ 3 * Et ^ 2 * m ^ 4 +
    896 * u ^ 3 * v ^ 3 * Et ^ 2 * m ^ 3 + 1096 * u ^ 3 * v ^ 3 * Et ^ 2 * m ^ 2 + 680 * u ^ 3 * v
    ^ 3 * Et ^ 2 * m + 168 * u ^ 3 * v ^ 3 * Et ^ 2 + 48 * u ^ 3 * v ^ 2 * Et ^ 3 * m ^ 6 + 516 *
    u ^ 3 * v ^ 2 * Et ^ 3 * m ^ 5 + 2220 * u ^ 3 * v ^ 2 * Et ^ 3 * m ^ 4 + 4884 * u ^ 3 * v ^ 2
    * Et ^ 3 * m ^ 3 + 5796 * u ^ 3 * v ^ 2 * Et ^ 3 * m ^ 2 + 3528 * u ^ 3 * v ^ 2 * Et ^ 3 * m +
    864 * u ^ 3 * v ^ 2 * Et ^ 3 + 24 * u ^ 3 * v ^ 2 * Et ^ 2 * m ^ 6 + 264 * u ^ 3 * v ^ 2 * Et
    ^ 2 * m ^ 5 + 1176 * u ^ 3 * v ^ 2 * Et ^ 2 * m ^ 4 + 2712 * u ^ 3 * v ^ 2 * Et ^ 2 * m ^ 3 +
    3408 * u ^ 3 * v ^ 2 * Et ^ 2 * m ^ 2 + 2208 * u ^ 3 * v ^ 2 * Et ^ 2 * m + 576 * u ^ 3 * v ^
    2 * Et ^ 2 + 24 * u ^ 3 * v * Et ^ 3 * m ^ 6 + 252 * u ^ 3 * v * Et ^ 3 * m ^ 5

/-- Part 1 of the numerator of `twoH` after substitution (positive coefficients). -/
def twoHnum_1 (Et m u v : ℝ) : ℝ :=
  1068 * u ^ 3 * v * Et ^ 3 * m ^ 4 + 2340 * u ^ 3 * v * Et ^ 3 * m ^ 3 + 2796 * u ^ 3 * v * Et ^
    3 * m ^ 2 + 1728 * u ^ 3 * v * Et ^ 3 * m + 432 * u ^ 3 * v * Et ^ 3 + 24 * u ^ 3 * v * Et ^ 2
    * m ^ 6 + 264 * u ^ 3 * v * Et ^ 2 * m ^ 5 + 1176 * u ^ 3 * v * Et ^ 2 * m ^ 4 + 2712 * u ^ 3
    * v * Et ^ 2 * m ^ 3 + 3408 * u ^ 3 * v * Et ^ 2 * m ^ 2 + 2208 * u ^ 3 * v * Et ^ 2 * m + 576
    * u ^ 3 * v * Et ^ 2 + 8 * u ^ 3 * Et ^ 2 * m ^ 6 + 88 * u ^ 3 * Et ^ 2 * m ^ 5 + 392 * u ^ 3
    * Et ^ 2 * m ^ 4 + 904 * u ^ 3 * Et ^ 2 * m ^ 3 + 1136 * u ^ 3 * Et ^ 2 * m ^ 2 + 736 * u ^ 3
    * Et ^ 2 * m + 192 * u ^ 3 * Et ^ 2 + 48 * u ^ 2 * v ^ 3 * Et ^ 3 * m ^ 6 + 516 * u ^ 2 * v ^
    3 * Et ^ 3 * m ^ 5 + 2220 * u ^ 2 * v ^ 3 * Et ^ 3 * m ^ 4 + 4884 * u ^ 2 * v ^ 3 * Et ^ 3 * m
    ^ 3 + 5796 * u ^ 2 * v ^ 3 * Et ^ 3 * m ^ 2 + 3528 * u ^ 2 * v ^ 3 * Et ^ 3 * m + 864 * u ^ 2
    * v ^ 3 * Et ^ 3 + 24 * u ^ 2 * v ^ 3 * Et ^ 2 * m ^ 6 + 264 * u ^ 2 * v ^ 3 * Et ^ 2 * m ^ 5
    + 1176 * u ^ 2 * v ^ 3 * Et ^ 2 * m ^ 4 + 2712 * u ^ 2 * v ^ 3 * Et ^ 2 * m ^ 3

/-- Part 2 of the numerator of `twoH` after substitution (positive coefficients). -/
def twoHnum_2 (Et m u v : ℝ) : ℝ :=
  3408 * u ^ 2 * v ^ 3 * Et ^ 2 * m ^ 2 + 2208 * u ^ 2 * v ^ 3 * Et ^ 2 * m + 576 * u ^ 2 * v ^ 3
    * Et ^ 2 + 96 * u ^ 2 * v ^ 2 * Et ^ 3 * m ^ 6 + 1008 * u ^ 2 * v ^ 2 * Et ^ 3 * m ^ 5 + 4278
    * u ^ 2 * v ^ 2 * Et ^ 3 * m ^ 4 + 9378 * u ^ 2 * v ^ 2 * Et ^ 3 * m ^ 3 + 11196 * u ^ 2 * v ^
    2 * Et ^ 3 * m ^ 2 + 6912 * u ^ 2 * v ^ 2 * Et ^ 3 * m + 1728 * u ^ 2 * v ^ 2 * Et ^ 3 + 72 *
    u ^ 2 * v ^ 2 * Et ^ 2 * m ^ 6 + 796 * u ^ 2 * v ^ 2 * Et ^ 2 * m ^ 5 + 3584 * u ^ 2 * v ^ 2 *
    Et ^ 2 * m ^ 4 + 8424 * u ^ 2 * v ^ 2 * Et ^ 2 * m ^ 3 + 10912 * u ^ 2 * v ^ 2 * Et ^ 2 * m ^
    2 + 7388 * u ^ 2 * v ^ 2 * Et ^ 2 * m + 2040 * u ^ 2 * v ^ 2 * Et ^ 2 + 48 * u ^ 2 * v * Et ^
    3 * m ^ 6 + 492 * u ^ 2 * v * Et ^ 3 * m ^ 5 + 2058 * u ^ 2 * v * Et ^ 3 * m ^ 4 + 4494 * u ^
    2 * v * Et ^ 3 * m ^ 3 + 5400 * u ^ 2 * v * Et ^ 3 * m ^ 2 + 3384 * u ^ 2 * v * Et ^ 3 * m +
    864 * u ^ 2 * v * Et ^ 3 + 72 * u ^ 2 * v * Et ^ 2 * m ^ 6 + 800 * u ^ 2 * v * Et ^ 2 * m ^ 5
    + 3636 * u ^ 2 * v * Et ^ 2 * m ^ 4 + 8648 * u ^ 2 * v * Et ^ 2 * m ^ 3 + 11340 * u ^ 2 * v *
    Et ^ 2 * m ^ 2 + 7760 * u ^ 2 * v * Et ^ 2 * m

/-- Part 3 of the numerator of `twoH` after substitution (positive coefficients). -/
def twoHnum_3 (Et m u v : ℝ) : ℝ :=
  2160 * u ^ 2 * v * Et ^ 2 + 24 * u ^ 2 * Et ^ 2 * m ^ 6 + 268 * u ^ 2 * Et ^ 2 * m ^ 5 + 1228 *
    u ^ 2 * Et ^ 2 * m ^ 4 + 2952 * u ^ 2 * Et ^ 2 * m ^ 3 + 3920 * u ^ 2 * Et ^ 2 * m ^ 2 + 2720
    * u ^ 2 * Et ^ 2 * m + 768 * u ^ 2 * Et ^ 2 + 24 * u * v ^ 3 * Et ^ 3 * m ^ 6 + 252 * u * v ^
    3 * Et ^ 3 * m ^ 5 + 1068 * u * v ^ 3 * Et ^ 3 * m ^ 4 + 2340 * u * v ^ 3 * Et ^ 3 * m ^ 3 +
    2796 * u * v ^ 3 * Et ^ 3 * m ^ 2 + 1728 * u * v ^ 3 * Et ^ 3 * m + 432 * u * v ^ 3 * Et ^ 3 +
    24 * u * v ^ 3 * Et ^ 2 * m ^ 6 + 264 * u * v ^ 3 * Et ^ 2 * m ^ 5 + 1176 * u * v ^ 3 * Et ^ 2
    * m ^ 4 + 2712 * u * v ^ 3 * Et ^ 2 * m ^ 3 + 3408 * u * v ^ 3 * Et ^ 2 * m ^ 2 + 2208 * u * v
    ^ 3 * Et ^ 2 * m + 576 * u * v ^ 3 * Et ^ 2 + 48 * u * v ^ 2 * Et ^ 3 * m ^ 6 + 492 * u * v ^
    2 * Et ^ 3 * m ^ 5 + 2058 * u * v ^ 2 * Et ^ 3 * m ^ 4 + 4494 * u * v ^ 2 * Et ^ 3 * m ^ 3 +
    5400 * u * v ^ 2 * Et ^ 3 * m ^ 2 + 3384 * u * v ^ 2 * Et ^ 3 * m + 864 * u * v ^ 2 * Et ^ 3 +
    72 * u * v ^ 2 * Et ^ 2 * m ^ 6

/-- Part 4 of the numerator of `twoH` after substitution (positive coefficients). -/
def twoHnum_4 (Et m u v : ℝ) : ℝ :=
  800 * u * v ^ 2 * Et ^ 2 * m ^ 5 + 3636 * u * v ^ 2 * Et ^ 2 * m ^ 4 + 8648 * u * v ^ 2 * Et ^ 2
    * m ^ 3 + 11340 * u * v ^ 2 * Et ^ 2 * m ^ 2 + 7760 * u * v ^ 2 * Et ^ 2 * m + 2160 * u * v ^
    2 * Et ^ 2 + 24 * u * v * Et ^ 3 * m ^ 6 + 240 * u * v * Et ^ 3 * m ^ 5 + 990 * u * v * Et ^ 3
    * m ^ 4 + 2154 * u * v * Et ^ 3 * m ^ 3 + 2604 * u * v * Et ^ 3 * m ^ 2 + 1656 * u * v * Et ^
    3 * m + 432 * u * v * Et ^ 3 + 72 * u * v * Et ^ 2 * m ^ 6 + 808 * u * v * Et ^ 2 * m ^ 5 +
    3736 * u * v * Et ^ 2 * m ^ 4 + 9096 * u * v * Et ^ 2 * m ^ 3 + 12272 * u * v * Et ^ 2 * m ^ 2
    + 8672 * u * v * Et ^ 2 * m + 2496 * u * v * Et ^ 2 + 24 * u * Et ^ 2 * m ^ 6 + 272 * u * Et ^
    2 * m ^ 5 + 1276 * u * Et ^ 2 * m ^ 4 + 3168 * u * Et ^ 2 * m ^ 3 + 4384 * u * Et ^ 2 * m ^ 2
    + 3200 * u * Et ^ 2 * m + 960 * u * Et ^ 2 + 8 * v ^ 3 * Et ^ 2 * m ^ 6 + 88 * v ^ 3 * Et ^ 2
    * m ^ 5 + 392 * v ^ 3 * Et ^ 2 * m ^ 4

/-- Part 5 of the numerator of `twoH` after substitution (positive coefficients). -/
def twoHnum_5 (Et m _u v : ℝ) : ℝ :=
  904 * v ^ 3 * Et ^ 2 * m ^ 3 + 1136 * v ^ 3 * Et ^ 2 * m ^ 2 + 736 * v ^ 3 * Et ^ 2 * m + 192 *
    v ^ 3 * Et ^ 2 + 24 * v ^ 2 * Et ^ 2 * m ^ 6 + 268 * v ^ 2 * Et ^ 2 * m ^ 5 + 1228 * v ^ 2 *
    Et ^ 2 * m ^ 4 + 2952 * v ^ 2 * Et ^ 2 * m ^ 3 + 3920 * v ^ 2 * Et ^ 2 * m ^ 2 + 2720 * v ^ 2
    * Et ^ 2 * m + 768 * v ^ 2 * Et ^ 2 + 24 * v * Et ^ 2 * m ^ 6 + 272 * v * Et ^ 2 * m ^ 5 +
    1276 * v * Et ^ 2 * m ^ 4 + 3168 * v * Et ^ 2 * m ^ 3 + 4384 * v * Et ^ 2 * m ^ 2 + 3200 * v *
    Et ^ 2 * m + 960 * v * Et ^ 2 + 8 * Et ^ 2 * m ^ 6 + 92 * Et ^ 2 * m ^ 5 + 440 * Et ^ 2 * m ^
    4 + 1120 * Et ^ 2 * m ^ 3 + 1600 * Et ^ 2 * m ^ 2 + 1216 * Et ^ 2 * m + 384 * Et ^ 2

/-- The numerator of `twoH` after the substitution `F_tot = E_tot (2 + m)`,
`r = u/((1 + u)(2 + m))`, `s = v/((1 + v)(2 + m))`: 175 terms, all positive. -/
def twoHnum (Et m u v : ℝ) : ℝ :=
  twoHnum_0 Et m u v + twoHnum_1 Et m u v + twoHnum_2 Et m u v + twoHnum_3 Et m u v
    + twoHnum_4 Et m u v + twoHnum_5 Et m u v

/-- The cross identity behind uniqueness. -/
theorem twoH_cross (Et Ft St r s : ℝ) :
    (r - s) * twoH Et Ft r s =
      twoQ Et Ft St r * twoBq Et Ft s - twoQ Et Ft St s * twoBq Et Ft r := by
  unfold twoH twoQ twoBq
  ring

set_option maxHeartbeats 8000000 in
-- clearing denominators in a degree-8 polynomial identity
/-- `twoH` after the substitution, with denominators cleared. -/
theorem twoH_subst (Et m u v : ℝ) (hm : 0 ≤ m) (hu : 0 < u) (hv : 0 < v) :
    twoH Et (Et * (2 + m)) (u / ((1 + u) * (2 + m))) (v / ((1 + v) * (2 + m))) *
      ((2 + m) ^ 5 * (1 + u) ^ 3 * (1 + v) ^ 3) = twoHnum Et m u v := by
  have h1 : (2 + m) ≠ 0 := by positivity
  have h2 : (1 + u) ≠ 0 := by positivity
  have h3 : (1 + v) ≠ 0 := by positivity
  unfold twoH twoHnum twoHnum_0 twoHnum_1 twoHnum_2 twoHnum_3 twoHnum_4 twoHnum_5
  field_simp
  ring

/-- **The certificate is positive** on the feasible region `F_tot ≥ 2E_tot`, `0 < r, s`,
`F_tot r, F_tot s < E_tot`. -/
theorem twoH_pos {Et Ft r s : ℝ} (hE : 0 < Et) (hF : 2 * Et ≤ Ft) (hr : 0 < r)
    (hrE : Ft * r < Et) (hs : 0 < s) (hsE : Ft * s < Et) : 0 < twoH Et Ft r s := by
  obtain ⟨m, hm, rfl⟩ : ∃ m, 0 ≤ m ∧ Ft = Et * (2 + m) :=
    ⟨Ft / Et - 2, by rw [sub_nonneg, le_div_iff₀ hE]; linarith, by field_simp; ring⟩
  have h2m : 0 < 2 + m := by linarith
  have hr1 : 0 < 1 - (2 + m) * r := by nlinarith
  have hs1 : 0 < 1 - (2 + m) * s := by nlinarith
  obtain ⟨Dr, hDr, hDrdef⟩ : ∃ D, 0 < D ∧ D = 1 - (2 + m) * r := ⟨_, hr1, rfl⟩
  obtain ⟨u, hu, rfl⟩ : ∃ u, 0 < u ∧ r = u / ((1 + u) * (2 + m)) :=
    ⟨(2 + m) * r / Dr, by positivity, by
      rw [eq_div_iff (by positivity)]; field_simp; rw [hDrdef]; ring⟩
  obtain ⟨Ds, hDs, hDsdef⟩ : ∃ D, 0 < D ∧ D = 1 - (2 + m) * s := ⟨_, hs1, rfl⟩
  obtain ⟨v, hv, rfl⟩ : ∃ v, 0 < v ∧ s = v / ((1 + v) * (2 + m)) :=
    ⟨(2 + m) * s / Ds, by positivity, by
      rw [eq_div_iff (by positivity)]; field_simp; rw [hDsdef]; ring⟩
  have key := twoH_subst Et m u v hm hu hv
  have hnum : 0 < twoHnum Et m u v := by
    unfold twoHnum twoHnum_0 twoHnum_1 twoHnum_2 twoHnum_3 twoHnum_4 twoHnum_5
    positivity
  have hden : 0 < (2 + m) ^ 5 * (1 + u) ^ 3 * (1 + v) ^ 3 := by positivity
  by_contra h
  push Not at h
  nlinarith

/-- **At most one feasible root** when `F_tot ≥ 2E_tot`. -/
theorem twoQ_root_unique {Et Ft St r s : ℝ} (hE : 0 < Et) (hF : 2 * Et ≤ Ft) (hr : 0 < r)
    (hrE : Ft * r < Et) (hs : 0 < s) (hsE : Ft * s < Et) (hQr : twoQ Et Ft St r = 0)
    (hQs : twoQ Et Ft St s = 0) : r = s := by
  have h := twoH_cross Et Ft St r s
  rw [hQr, hQs, zero_mul, zero_mul, sub_zero] at h
  rcases mul_eq_zero.mp h with h | h
  · linarith
  · exact absurd h (twoH_pos hE hF hr hrE hs hsE).ne'

/-- **Elimination**: the reduced steady-state equations give the feasibility relation
`S₀ r G(r) = F_tot r − E_tot` and `F_tot r (r + 1) Q(r) = 0`. -/
theorem two_reduced_Q {Et Ft St a F r : ℝ} (eE : r * F * (1 + a * (2 + r)) = Et)
    (eF : F * (1 + a * r * (2 * r + 1)) = Ft)
    (eS : a * (1 + r + r ^ 2) + 3 * a * r * F * (1 + r) = St) :
    a * r * ((2 * Et - Ft) * r + (Et - 2 * Ft)) = Ft * r - Et ∧
      Ft * r * (r + 1) * twoQ Et Ft St r = 0 := by
  constructor
  · linear_combination (-(1 + a * r * (2 * r + 1))) * eE + (r * (1 + a * (2 + r))) * eF
  · linear_combination (norm := skip)
      (r * ((2 * Et - Ft) * r + (Et - 2 * Ft))) ^ 2 * (1 + a * r * (2 * r + 1)) * eS
      + (twoWc Et Ft St a r * r * (1 + a * (2 + r))
        - 3 * a * r * (1 + r) * (r * ((2 * Et - Ft) * r + (Et - 2 * Ft))) ^ 2) * eF
      - (twoWc Et Ft St a r * (1 + a * r * (2 * r + 1))) * eE
    unfold twoQ twoWc
    ring

/-! ### Steady states with prescribed totals -/

/-- `y` is a positive steady state at the witness rates with totals `E_tot`, `F_tot`, `S_tot`. -/
def TwoTotals (Et Ft St : ℝ) (y : Fin 9 → ℝ) : Prop :=
  twoNet.IsPosSteadyState twoK y ∧ y 3 + y 5 + y 6 = Et ∧ y 4 + y 7 + y 8 = Ft ∧
    y 0 + y 1 + y 2 + y 5 + y 6 + y 7 + y 8 = St

/-- The slice of `Design/TwoSiteMonostable` is the case `E_tot = F_tot`. -/
theorem twoTotals_eq_slice (c σ : ℝ) : TwoTotals c c σ = TwoSlice c σ := rfl

/-- **Reduction** of a steady state with given totals to `(S₀, F, r)`. -/
theorem TwoTotals.reduced {Et Ft St : ℝ} {y : Fin 9 → ℝ} (hy : TwoTotals Et Ft St y) :
    ∃ r, 0 < r ∧ y 3 = r * y 4 ∧ y 1 = r * y 0 ∧ y 2 = r ^ 2 * y 0 ∧
      r * y 4 * (1 + y 0 * (2 + r)) = Et ∧ y 4 * (1 + y 0 * r * (2 * r + 1)) = Ft ∧
      y 0 * (1 + r + r ^ 2) + 3 * y 0 * r * y 4 * (1 + r) = St := by
  obtain ⟨⟨hpos, hss⟩, cE, cF, cS⟩ := hy
  obtain ⟨e5, e6, e7, e8, g0, g2⟩ := two_steady_eqs hss
  have p4 := hpos 4
  refine ⟨y 3 / y 4, div_pos (hpos 3) p4, ?_⟩
  set r := y 3 / y 4
  have hr3 : y 3 = r * y 4 := (div_mul_cancel₀ (y 3) p4.ne').symm
  have hy1 : y 1 = r * y 0 := by
    have : (y 1 - r * y 0) * y 4 = 0 := by linear_combination -g0 + y 0 * hr3
    linarith [(mul_eq_zero.mp this).resolve_right p4.ne']
  have hy2 : y 2 = r ^ 2 * y 0 := by
    have : (y 2 - r * y 1) * y 4 = 0 := by linear_combination -g2 + y 1 * hr3
    have h := (mul_eq_zero.mp this).resolve_right p4.ne'
    rw [hy1] at h
    linear_combination h
  refine ⟨hr3, hy1, hy2, ?_, ?_, ?_⟩
  · linear_combination cE - e5 - e6 - (1 + 2 * y 0 + y 1) * hr3 - r * y 4 * hy1
  · linear_combination cF - e7 - e8 - 2 * y 4 * hy2 - y 4 * hy1
  · linear_combination cS - e5 - e6 - e7 - e8 - (2 * y 0 + y 1) * hr3
      - (1 + r * y 4 + y 4) * hy1 - (1 + 2 * y 4) * hy2

/-- **Uniqueness when `F_tot ≥ 2E_tot`.** -/
theorem two_totals_unique {Et Ft St : ℝ} (hE : 0 < Et) (hF : 2 * Et ≤ Ft) {y y' : Fin 9 → ℝ}
    (hy : TwoTotals Et Ft St y) (hy' : TwoTotals Et Ft St y') : y = y' := by
  obtain ⟨r, hr, hr3, hy1, hy2, eE, eF, eS⟩ := hy.reduced
  obtain ⟨r', hr', hr3', hy1', hy2', eE', eF', eS'⟩ := hy'.reduced
  have hFt : 0 < Ft := by linarith
  have a0 := hy.1.1 0
  have a0' := hy'.1.1 0
  obtain ⟨L, hQ⟩ := two_reduced_Q eE eF eS
  obtain ⟨L', hQ'⟩ := two_reduced_Q eE' eF' eS'
  have hG : ∀ t, 0 < t → (2 * Et - Ft) * t + (Et - 2 * Ft) < 0 := fun t ht => by nlinarith
  have feas : ∀ a t, 0 < a → 0 < t → a * t * ((2 * Et - Ft) * t + (Et - 2 * Ft)) = Ft * t - Et →
      Ft * t < Et := fun a t ha ht h => by
    have := mul_neg_of_pos_of_neg (mul_pos ha ht) (hG t ht)
    linarith
  have hQr : twoQ Et Ft St r = 0 := by
    rcases mul_eq_zero.mp hQ with h | h
    · exact absurd h (by positivity)
    · exact h
  have hQr' : twoQ Et Ft St r' = 0 := by
    rcases mul_eq_zero.mp hQ' with h | h
    · exact absurd h (by positivity)
    · exact h
  have hrr := twoQ_root_unique hE hF hr (feas _ _ a0 hr L) hr' (feas _ _ a0' hr' L') hQr hQr'
  subst hrr
  have ha : y 0 = y' 0 := by
    have : (y 0 - y' 0) * (r * ((2 * Et - Ft) * r + (Et - 2 * Ft))) = 0 := by
      linear_combination L - L'
    have hne : r * ((2 * Et - Ft) * r + (Et - 2 * Ft)) ≠ 0 :=
      (mul_neg_of_pos_of_neg hr (hG r hr)).ne
    linarith [(mul_eq_zero.mp this).resolve_right hne]
  have hF4 : y 4 = y' 4 := by
    rw [ha] at eF
    have : (y 4 - y' 4) * (1 + y' 0 * r * (2 * r + 1)) = 0 := by linear_combination eF - eF'
    have hne : (1 + y' 0 * r * (2 * r + 1)) ≠ 0 := by positivity
    linarith [(mul_eq_zero.mp this).resolve_right hne]
  exact two_eq_of hy.1.2 hy'.1.2 ha (by rw [hy1, hy1', ha]) (by rw [hy2, hy2', ha]) (by
    rw [hr3, hr3', hF4]) hF4

/-- The value of the quartic at `r = E_tot/F_tot`. -/
theorem twoQ_at_ratio {Et Ft St : ℝ} (hF : 0 < Ft) :
    twoQ Et Ft St (Et / Ft) * Ft ^ 3 = -4 * Et * St * (Et - Ft) ^ 2 * (Et + Ft) := by
  unfold twoQ
  field_simp
  ring

/-- **Existence when `F_tot ≥ 2E_tot`** (intermediate value theorem on the quartic). -/
theorem two_totals_exists {Et Ft St : ℝ} (hE : 0 < Et) (hF : 2 * Et ≤ Ft) (hS : 0 < St) :
    ∃ y, TwoTotals Et Ft St y := by
  have hFt : 0 < Ft := by linarith
  have hρ : 0 < Et / Ft := by positivity
  have hcont : ContinuousOn (fun r => twoQ Et Ft St r) (Icc 0 (Et / Ft)) := by
    unfold twoQ; fun_prop
  have h0 : twoQ Et Ft St 0 = 2 * Et := by unfold twoQ; ring
  have h1 : twoQ Et Ft St (Et / Ft) < 0 := by
    have key := twoQ_at_ratio (Et := Et) (St := St) hFt
    have hne : 0 < (Et - Ft) ^ 2 := by
      have : Et - Ft ≠ 0 := by intro h; linarith
      positivity
    have hneg : -4 * Et * St * (Et - Ft) ^ 2 * (Et + Ft) < 0 := by
      have : 0 < 4 * Et * St * (Et - Ft) ^ 2 * (Et + Ft) := by positivity
      linarith
    by_contra h
    push Not at h
    have : 0 ≤ twoQ Et Ft St (Et / Ft) * Ft ^ 3 := by positivity
    linarith
  obtain ⟨r, ⟨hr0, hr1⟩, hQ⟩ :=
    intermediate_value_Icc' hρ.le hcont ⟨h1.le, by
      change (0 : ℝ) ≤ twoQ Et Ft St 0
      rw [h0]; linarith⟩
  change twoQ Et Ft St r = 0 at hQ
  have hr : 0 < r := lt_of_le_of_ne hr0 (by rintro rfl; rw [h0] at hQ; linarith)
  have hrE : Ft * r < Et := by
    have : r < Et / Ft := lt_of_le_of_ne hr1 (by rintro rfl; linarith)
    rwa [lt_div_iff₀ hFt, mul_comm] at this
  set G := (2 * Et - Ft) * r + (Et - 2 * Ft) with hGdef
  have hG : G < 0 := by nlinarith
  have hrG : r * G < 0 := mul_neg_of_pos_of_neg hr hG
  set a := (Ft * r - Et) / (r * G) with hadef
  have ha : 0 < a := div_pos_of_neg_of_neg (by linarith) hrG
  have L : a * r * G = Ft * r - Et := by
    rw [hadef, mul_assoc, div_mul_cancel₀ _ hrG.ne]
  set Y := 1 + a * r * (2 * r + 1) with hYdef
  have hY : 0 < Y := by positivity
  set F := Ft / Y with hFdef
  have hFpos : 0 < F := by positivity
  have eF : F * Y = Ft := div_mul_cancel₀ Ft hY.ne'
  have eE : r * F * (1 + a * (2 + r)) = Et := by
    have : (r * F * (1 + a * (2 + r)) - Et) * Y = 0 := by
      linear_combination (r * (1 + a * (2 + r))) * eF - L
    linarith [(mul_eq_zero.mp this).resolve_right hY.ne']
  have hT : (r * G) ^ 2 * (St * Y - a * (1 + r + r ^ 2) * Y - 3 * a * r * (1 + r) * Ft) = 0 := by
    linear_combination (norm := skip) (-(Ft * r * (r + 1))) * hQ + twoWc Et Ft St a r * L
    unfold twoQ twoWc
    ring
  have hT0 : St * Y - a * (1 + r + r ^ 2) * Y - 3 * a * r * (1 + r) * Ft = 0 :=
    (mul_eq_zero.mp hT).resolve_left (pow_ne_zero 2 hrG.ne)
  have eS : a * (1 + r + r ^ 2) + 3 * a * r * F * (1 + r) = St := by
    have : (a * (1 + r + r ^ 2) + 3 * a * r * F * (1 + r) - St) * Y = 0 := by
      linear_combination -hT0 + 3 * a * r * (1 + r) * eF
    linarith [(mul_eq_zero.mp this).resolve_right hY.ne']
  refine ⟨![a, r * a, r ^ 2 * a, r * F, F, 2 * a * (r * F), r * a * (r * F),
    2 * (r ^ 2 * a) * F, r * a * F], ⟨⟨fun i => ?_, ?_⟩, ?_, ?_, ?_⟩⟩
  · fin_cases i
    exacts [ha, mul_pos hr ha, mul_pos (pow_pos hr 2) ha, mul_pos hr hFpos, hFpos,
      mul_pos (mul_pos two_pos ha) (mul_pos hr hFpos), mul_pos (mul_pos hr ha) (mul_pos hr hFpos),
      mul_pos (mul_pos two_pos (mul_pos (pow_pos hr 2) ha)) hFpos, mul_pos (mul_pos hr ha) hFpos]
  · refine two_steady_of rfl rfl rfl rfl ?_ ?_
    · change a * (r * F) = r * a * F; ring
    · change r * a * (r * F) = r ^ 2 * a * F; ring
  · change r * F + 2 * a * (r * F) + r * a * (r * F) = Et
    linear_combination eE
  · change F + 2 * (r ^ 2 * a) * F + r * a * F = Ft
    linear_combination eF
  · change a + r * a + r ^ 2 * a + 2 * a * (r * F) + r * a * (r * F) + 2 * (r ^ 2 * a) * F
      + r * a * F = St
    linear_combination eS

/-! ### The kinase–phosphatase symmetry -/

/-- The symmetry `S₀ ↔ S₂`, `E ↔ F`, `S₀E ↔ S₂F`, `S₁E ↔ S₁F` of the witness-rate system. -/
def twoSwap (y : Fin 9 → ℝ) : Fin 9 → ℝ := ![y 2, y 1, y 0, y 4, y 3, y 7, y 8, y 5, y 6]

/-- `twoSwap` is an involution. -/
theorem twoSwap_twoSwap (y : Fin 9 → ℝ) : twoSwap (twoSwap y) = y := by
  funext i
  fin_cases i <;> rfl

/-- `twoSwap` maps steady states with totals `(E_tot, F_tot, S_tot)` to `(F_tot, E_tot, S_tot)`. -/
theorem TwoTotals.swap {Et Ft St : ℝ} {y : Fin 9 → ℝ} (hy : TwoTotals Et Ft St y) :
    TwoTotals Ft Et St (twoSwap y) := by
  obtain ⟨⟨hpos, hss⟩, cE, cF, cS⟩ := hy
  obtain ⟨e5, e6, e7, e8, g0, g2⟩ := two_steady_eqs hss
  refine ⟨⟨fun i => ?_, two_steady_of e7 e8 e5 e6 ?_ ?_⟩, cF, cE, ?_⟩
  · fin_cases i
    exacts [hpos 2, hpos 1, hpos 0, hpos 4, hpos 3, hpos 7, hpos 8, hpos 5, hpos 6]
  · change y 2 * y 4 = y 1 * y 3; exact g2.symm
  · change y 1 * y 4 = y 0 * y 3; exact g0.symm
  · change y 2 + y 1 + y 0 + y 7 + y 8 + y 5 + y 6 = St
    linarith

/-- **Monostability for unequal enzyme totals**: at the witness rates, if one enzyme total is at
least twice the other, the class has exactly one positive steady state, for every `S_tot > 0`. -/
theorem two_totals_existsUnique {Et Ft St : ℝ} (hE : 0 < Et) (hF : 0 < Ft) (hS : 0 < St)
    (h : 2 * Et ≤ Ft ∨ 2 * Ft ≤ Et) : ∃! y, TwoTotals Et Ft St y := by
  rcases h with h | h
  · obtain ⟨y, hy⟩ := two_totals_exists hE h hS
    exact ⟨y, hy, fun y' hy' => two_totals_unique hE h hy' hy⟩
  · obtain ⟨y, hy⟩ := two_totals_exists hF h hS
    refine ⟨twoSwap y, hy.swap, fun y' hy' => ?_⟩
    rw [← twoSwap_twoSwap y', two_totals_unique hF h hy'.swap hy]

end LeanTheory.CRN.Design
