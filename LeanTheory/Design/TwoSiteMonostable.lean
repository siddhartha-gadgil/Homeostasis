/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Design.TwoSiteBistability

/-!
# A certified monostable region for two-site phosphorylation (notes N-010, Q-2)

At the witness rates `twoK` we classify the steady states in every compatibility class with
equal enzyme totals `E_tot = F_tot = c` and substrate total `S_tot = σ` (`TwoSlice c σ`; by
`TwoSlice.of_sub_mem` this is a union of compatibility classes). With the complexes eliminated,
`F · (E_tot − F_tot)` factors as `(E − F)(F − S₀E)` (`two_slice_cases`):

* the **symmetric branch** `E = F`, `S₀ = S₁ = S₂ = s` gives `e(1 + 3s) = c`,
  `9s² + (3 + 6c − 3σ)s − σ = 0`: exactly one state for every `c, σ > 0` (`twoSym`);
* the **asymmetric branch** `F = S₀E` gives `S₁ = 1`, `S₀S₂ = 1`, `S₀ + S₂ = σ − 1 − 3c/2`, which
  has positive solutions only when `σ ≥ 3 + 3c/2` (`twoBr`).

Results:

* **Monostable region** `σ ≤ 3 + 3c/2`: exactly one positive steady state
  (`two_slice_existsUnique`);
  for `σ < 3 + 3c/2` it is **locally exponentially stable within its class**
  (`two_slice_classStable`): along the symmetric branch the Hurwitz determinants of the restricted
  Jacobian are polynomials with positive coefficients and `a₆ = 432e²(1 − s)(2e + 3s + 1)`, positive
  exactly when `s < 1`, i.e. `σ < 3 + 3c/2` (`two_slice_threshold`).
* **Multistationary region** `σ > 3 + 3c/2`: exactly three positive steady states
  (`two_slice_three`), the symmetric one linearly unstable (`two_slice_sym_unstable`).

The threshold `σ = 3 + 3c/2` is a pitchfork: the symmetric state crosses `s = 1` and the two
asymmetric states are born from it. The witness class of `Design/TwoSitePhosphorylation`
(`c = 3`, `σ = 8 > 7.5`) lies on the multistationary side.

The two asymmetric states are stable for all `(c, σ)` beyond the threshold:
`Design/TwoSiteOuterStability` (`two_slice_bistable`). Not formalized: classes with
`E_tot ≠ F_tot`, other rate constants.

Label: exact, idealized; witness rates `twoK`, all classes with `E_tot = F_tot`.
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN.Design

open Matrix ReactionNetwork Set

/-! ### Stability along the symmetric branch -/

/-- Coefficient `a1` of the characteristic polynomial of `twoRM s e`. -/
def twoMA1 (s e : ℝ) : ℝ :=
  14 * s + 14 * e + 10

/-- Coefficient `a2` of the characteristic polynomial of `twoRM s e`. -/
def twoMA2 (s e : ℝ) : ℝ :=
  49 * s ^ 2 + 146 * s * e + 106 * s + 64 * e ^ 2 + 126 * e + 37

/-- Coefficient `a3` of the characteristic polynomial of `twoRM s e`. -/
def twoMA3 (s e : ℝ) : ℝ :=
  336 * s ^ 2 * e + 252 * s ^ 2 + 432 * s * e ^ 2 + 980 * s * e + 264 * s + 96 * e ^ 3 + 512 * e ^
  2 + 412 * e + 60

/-- Coefficient `a4` of the characteristic polynomial of `twoRM s e`. -/
def twoMA4 (s e : ℝ) : ℝ :=
  432 * s ^ 2 * e ^ 2 + 1536 * s ^ 2 * e + 324 * s ^ 2 + 288 * s * e ^ 3 + 2304 * s * e ^ 2 + 2112
  * s * e + 216 * s + 672 * e ^ 3 + 1408 * e ^ 2 + 576 * e + 36

/-- Coefficient `a5` of the characteristic polynomial of `twoRM s e`. -/
def twoMA5 (s e : ℝ) : ℝ :=
  864 * s ^ 2 * e ^ 2 + 1728 * s ^ 2 * e + 576 * s * e ^ 3 + 3408 * s * e ^ 2 + 1440 * s * e +
  1440 * e ^ 3 + 1488 * e ^ 2 + 288 * e

/-- Constant coefficient `a₆ = 432 e² (1 − s)(2e + 3s + 1)`. -/
def twoMA6 (s e : ℝ) : ℝ :=
  432 * e ^ 2 * (1 - s) * (2 * e + 3 * s + 1)

/-- The Hurwitz determinant `Δ₂` of `twoRM s e`: all coefficients positive. -/
def twoMΔ₂ (s e : ℝ) : ℝ :=
  686 * s ^ 3 + 2394 * s ^ 2 * e + 1722 * s ^ 2 + 2508 * s * e ^ 2 + 3728 * s * e + 1314 * s + 800
  * e ^ 3 + 1892 * e ^ 2 + 1366 * e + 310

/-- The Hurwitz determinant `Δ₃` of `twoRM s e`: all coefficients positive. -/
def twoMΔ₃ (s e : ℝ) : ℝ :=
  230496 * s ^ 5 * e + 172872 * s ^ 5 + 1016064 * s ^ 4 * e ^ 2 + 1553104 * s ^ 4 * e + 551544 * s
  ^ 4 + 1716960 * s ^ 3 * e ^ 3 + 4163320 * s ^ 3 * e ^ 2 + 3036320 * s ^ 3 * e + 693840 * s ^ 3 +
  1384512 * s ^ 2 * e ^ 4 + 4779312 * s ^ 2 * e ^ 3 + 5481720 * s ^ 2 * e ^ 2 + 2577600 * s ^ 2 *
  e + 428400 * s ^ 2 + 529920 * s * e ^ 5 + 2455744 * s * e ^ 4 + 3969312 * s * e ^ 3 + 2922216 *
  s * e ^ 2 + 1000832 * s * e + 129000 * s + 76800 * e ^ 6 + 459520 * e ^ 5 + 985472 * e ^ 4 +
  1017552 * e ^ 3 + 544808 * e ^ 2 + 144880 * e + 15000

/-- The Hurwitz determinant `Δ₄` of `twoRM s e`: all coefficients positive. -/
def twoMΔ₄ (s e : ℝ) : ℝ :=
  99574272 * s ^ 7 * e ^ 3 + 399680064 * s ^ 7 * e ^ 2 + 282127104 * s ^ 7 * e + 56010528 * s ^ 7
  + 505322496 * s ^ 6 * e ^ 4 + 2605216320 * s ^ 6 * e ^ 3 + 3199637280 * s ^ 6 * e ^ 2 +
  1445407488 * s ^ 6 * e + 216040608 * s ^ 6 + 1034353152 * s ^ 5 * e ^ 5 + 6812870400 * s ^ 5 * e
  ^ 4 + 12110342496 * s ^ 5 * e ^ 3 + 8996466528 * s ^ 5 * e ^ 2 + 2959117056 * s ^ 5 * e +
  350161056 * s ^ 5 + 1092593664 * s ^ 4 * e ^ 6 + 9261156096 * s ^ 4 * e ^ 5 + 22078752384 * s ^
  4 * e ^ 4 + 23507808736 * s ^ 4 * e ^ 3 + 12471867648 * s ^ 4 * e ^ 2 + 3190973184 * s ^ 4 * e +
  308526624 * s ^ 4 + 627664896 * s ^ 3 * e ^ 7 + 7042940928 * s ^ 3 * e ^ 6 + 21714987648 * s ^ 3
  * e ^ 5 + 30892151296 * s ^ 3 * e ^ 4 + 23302294208 * s ^ 3 * e ^ 3 + 9533805312 * s ^ 3 * e ^ 2
  + 1974438144 * s ^ 3 * e + 159308640 * s ^ 3 + 185794560 * s ^ 2 * e ^ 8 + 2973413376 * s ^ 2 *
  e ^ 7 + 11688059904 * s ^ 2 * e ^ 6 + 21358564224 * s ^ 2 * e ^ 5 + 21422125824 * s ^ 2 * e ^ 4
  + 12404494080 * s ^ 2 * e ^ 3 + 4092355872 * s ^ 2 * e ^ 2 + 704436480 * s ^ 2 * e + 48146400 *
  s ^ 2 + 22118400 * s * e ^ 9 + 635904000 * s * e ^ 8 + 3201060864 * s * e ^ 7 + 7350848512 * s *
  e ^ 6 + 9419936640 * s * e ^ 5 + 7228825344 * s * e ^ 4 + 3368218592 * s * e ^ 3 + 922923360 * s
  * e ^ 2 + 134611200 * s * e + 7884000 * s + 51609600 * e ^ 9 + 343203840 * e ^ 8 + 980998144 * e
  ^ 7 + 1566697472 * e ^ 6 + 1530424704 * e ^ 5 + 943379072 * e ^ 4 + 365037280 * e ^ 3 + 84907200
  * e ^ 2 + 10656000 * e + 540000

set_option maxHeartbeats 2000000 in
-- elaborating a 92-term polynomial with large coefficients
/-- The Hurwitz determinant `Δ₅` of `twoRM s e`: all coefficients positive. -/
def twoMΔ₅ (s e : ℝ) : ℝ :=
  86032171008 * s ^ 9 * e ^ 5 + 617758783488 * s ^ 9 * e ^ 4 + 1084961267712 * s ^ 9 * e ^ 3 +
  592367344128 * s ^ 9 * e ^ 2 + 96786192384 * s ^ 9 * e + 493953417216 * s ^ 8 * e ^ 6 +
  4332082341888 * s ^ 8 * e ^ 5 + 10354686547968 * s ^ 8 * e ^ 4 + 9308684560896 * s ^ 8 * e ^ 3 +
  3483108034560 * s ^ 8 * e ^ 2 + 453973330944 * s ^ 8 * e + 1184746881024 * s ^ 7 * e ^ 7 +
  12766016212992 * s ^ 7 * e ^ 6 + 39538330675200 * s ^ 7 * e ^ 5 + 50212551868416 * s ^ 7 * e ^ 4
  + 30313436073984 * s ^ 7 * e ^ 3 + 8648557940736 * s ^ 7 * e ^ 2 + 932307812352 * s ^ 7 * e +
  1539788341248 * s ^ 6 * e ^ 8 + 20653982982144 * s ^ 6 * e ^ 7 + 80893405956096 * s ^ 6 * e ^ 6
  + 135370762702848 * s ^ 6 * e ^ 5 + 115116189737472 * s ^ 6 * e ^ 4 + 52241413653504 * s ^ 6 * e
  ^ 3 + 12027391100928 * s ^ 6 * e ^ 2 + 1099585622016 * s ^ 6 * e + 1171636420608 * s ^ 5 * e ^ 9
  + 20063740870656 * s ^ 5 * e ^ 8 + 98543566725120 * s ^ 5 * e ^ 7 + 209389924288512 * s ^ 5 * e
  ^ 6 + 234210394272768 * s ^ 5 * e ^ 5 + 148837393640448 * s ^ 5 * e ^ 4 + 53985567025152 * s ^ 5
  * e ^ 3 + 10388808741888 * s ^ 5 * e ^ 2 + 820410052608 * s ^ 5 * e + 522061479936 * s ^ 4 * e ^
  10 + 11974634569728 * s ^ 4 * e ^ 9 + 74232236187648 * s ^ 4 * e ^ 8 + 196433030983680 * s ^ 4 *
  e ^ 7 + 277914102816768 * s ^ 4 * e ^ 6 + 231373237355520 * s ^ 4 * e ^ 5 + 116937073460736 * s
  ^ 4 * e ^ 4 + 35225473978368 * s ^ 4 * e ^ 3 + 5803578906624 * s ^ 4 * e ^ 2 + 401457088512 * s
  ^ 4 * e + 126127964160 * s ^ 3 * e ^ 11 + 4281205653504 * s ^ 3 * e ^ 10 + 34422183788544 * s ^
  3 * e ^ 9 + 112717767720960 * s ^ 3 * e ^ 8 + 197165203660800 * s ^ 3 * e ^ 7 + 206761792290816
  * s ^ 3 * e ^ 6 + 136421634011136 * s ^ 3 * e ^ 5 + 57052514396160 * s ^ 3 * e ^ 4 +
  14651361312768 * s ^ 3 * e ^ 3 + 2102959521792 * s ^ 3 * e ^ 2 + 128835256320 * s ^ 3 * e +
  12740198400 * s ^ 2 * e ^ 12 + 835969351680 * s ^ 2 * e ^ 11 + 9356376932352 * s ^ 2 * e ^ 10 +
  38195426230272 * s ^ 2 * e ^ 9 + 81669253595136 * s ^ 2 * e ^ 8 + 105326326849536 * s ^ 2 * e ^
  7 + 87255812302848 * s ^ 2 * e ^ 6 + 47516051748864 * s ^ 2 * e ^ 5 + 16898183474688 * s ^ 2 * e
  ^ 4 + 3770201189376 * s ^ 2 * e ^ 3 + 477716797440 * s ^ 2 * e ^ 2 + 26152243200 * s ^ 2 * e +
  67947724800 * s * e ^ 12 + 1315283927040 * s * e ^ 11 + 6892078104576 * s * e ^ 10 +
  18002266718208 * s * e ^ 9 + 28172288458752 * s * e ^ 8 + 28602653736960 * s * e ^ 7 +
  19515222829056 * s * e ^ 6 + 9022068618240 * s * e ^ 5 + 2783195771904 * s * e ^ 4 +
  547267553280 * s * e ^ 3 + 61852377600 * s * e ^ 2 + 3048192000 * s * e + 67947724800 * e ^ 12 +
  495735275520 * e ^ 11 + 1603724378112 * e ^ 10 + 3032764907520 * e ^ 9 + 3720372117504 * e ^ 8 +
  3104731533312 * e ^ 7 + 1796412125184 * e ^ 6 + 719841266688 * e ^ 5 + 195558658560 * e ^ 4 +
  34270041600 * e ^ 3 + 3483648000 * e ^ 2 + 155520000 * e

set_option maxHeartbeats 8000000 in
-- Laplace expansion of a symbolic `6 × 6` determinant
/-- The characteristic polynomial of `twoRM s e`, over `ℂ`. -/
theorem twoRM_charpolyC (s e : ℝ) (lam : ℂ) :
    (lam • (1 : Matrix (Fin 6) (Fin 6) ℂ) - toComplex (twoRM s e)).det =
      lam ^ 6 + (twoMA1 s e : ℂ) * lam ^ 5 + (twoMA2 s e : ℂ) * lam ^ 4
        + (twoMA3 s e : ℂ) * lam ^ 3 + (twoMA4 s e : ℂ) * lam ^ 2 + (twoMA5 s e : ℂ) * lam
        + (twoMA6 s e : ℂ) := by
  simp [det_succ_row_zero, Fin.sum_univ_succ, twoRM, twoMA1, twoMA2, twoMA3, twoMA4, twoMA5,
    twoMA6, toComplex_apply, Matrix.one_apply, Fin.succAbove]
  ring

/-- **The symmetric branch is stable for `s < 1`**: the restricted Jacobian `twoRM s e` is Hurwitz
(degree-6 Routh–Hurwitz; `Δ₂, …, Δ₅` have positive coefficients, `a₆ > 0` iff `s < 1`). -/
theorem twoRM_isHurwitz {s e : ℝ} (hs : 0 < s) (hs1 : s < 1) (he : 0 < e) :
    IsHurwitz (twoRM s e) := by
  refine isHurwitz_of_charpoly6 (twoRM_charpolyC s e) ?_ ?_ ?_ ?_ ?_ ?_
  · unfold twoMA1; positivity
  · unfold twoMA6
    exact mul_pos (mul_pos (by positivity) (by linarith)) (by positivity)
  · rw [show hurwitz6Δ₂ (twoMA1 s e) (twoMA2 s e) (twoMA3 s e) = twoMΔ₂ s e by
      unfold hurwitz6Δ₂ twoMA1 twoMA2 twoMA3 twoMΔ₂; ring]
    unfold twoMΔ₂; positivity
  · rw [show hurwitz6Δ₃ (twoMA1 s e) (twoMA2 s e) (twoMA3 s e) (twoMA4 s e) (twoMA5 s e)
        = twoMΔ₃ s e by
      unfold hurwitz6Δ₃ twoMA1 twoMA2 twoMA3 twoMA4 twoMA5 twoMΔ₃; ring]
    unfold twoMΔ₃; positivity
  · rw [show hurwitz6Δ₄ (twoMA1 s e) (twoMA2 s e) (twoMA3 s e) (twoMA4 s e) (twoMA5 s e)
        (twoMA6 s e) = twoMΔ₄ s e by
      unfold hurwitz6Δ₄ twoMA1 twoMA2 twoMA3 twoMA4 twoMA5 twoMA6 twoMΔ₄; ring]
    unfold twoMΔ₄; positivity
  · rw [show hurwitz6Δ₅ (twoMA1 s e) (twoMA2 s e) (twoMA3 s e) (twoMA4 s e) (twoMA5 s e)
        (twoMA6 s e) = twoMΔ₅ s e by
      unfold hurwitz6Δ₅ twoMA1 twoMA2 twoMA3 twoMA4 twoMA5 twoMA6 twoMΔ₅; ring]
    unfold twoMΔ₅; positivity

/-! ### Steady states at the witness rates -/

/-- The steady-state equations at the witness rates, with the complexes eliminated. -/
theorem two_steady_eqs {y : Fin 9 → ℝ} (hy : twoNet.massActionField twoK y = 0) :
    y 5 = 2 * y 0 * y 3 ∧ y 6 = y 1 * y 3 ∧ y 7 = 2 * y 2 * y 4 ∧ y 8 = y 1 * y 4 ∧
      y 0 * y 3 = y 1 * y 4 ∧ y 1 * y 3 = y 2 * y 4 := by
  rw [two_field] at hy
  have f0 := congrFun hy 0
  have f2 := congrFun hy 2
  have f5 := congrFun hy 5
  have f6 := congrFun hy 6
  have f7 := congrFun hy 7
  have f8 := congrFun hy 8
  norm_num [twoK] at f0 f2 f5 f6 f7 f8
  have e5 : y 5 = 2 * y 0 * y 3 := by linarith
  have e6 : y 6 = y 1 * y 3 := by linarith
  have e7 : y 7 = 2 * y 2 * y 4 := by linarith
  have e8 : y 8 = y 1 * y 4 := by linarith
  exact ⟨e5, e6, e7, e8, by linarith, by linarith⟩

/-- Conversely, these equations give a steady state. -/
theorem two_steady_of {y : Fin 9 → ℝ} (e5 : y 5 = 2 * y 0 * y 3) (e6 : y 6 = y 1 * y 3)
    (e7 : y 7 = 2 * y 2 * y 4) (e8 : y 8 = y 1 * y 4) (g0 : y 0 * y 3 = y 1 * y 4)
    (g2 : y 1 * y 3 = y 2 * y 4) : twoNet.massActionField twoK y = 0 := by
  rw [two_field]
  funext i
  fin_cases i <;> norm_num [twoK] <;> linarith

/-- A steady state at the witness rates is determined by `(S₀, S₁, S₂, E, F)`. -/
theorem two_eq_of {y y' : Fin 9 → ℝ} (hy : twoNet.massActionField twoK y = 0)
    (hy' : twoNet.massActionField twoK y' = 0) (h0 : y 0 = y' 0) (h1 : y 1 = y' 1)
    (h2 : y 2 = y' 2) (h3 : y 3 = y' 3) (h4 : y 4 = y' 4) : y = y' := by
  obtain ⟨e5, e6, e7, e8, -, -⟩ := two_steady_eqs hy
  obtain ⟨e5', e6', e7', e8', -, -⟩ := two_steady_eqs hy'
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · change y 5 = y' 5; rw [e5, e5', h0, h3]
  · change y 6 = y' 6; rw [e6, e6', h1, h3]
  · change y 7 = y' 7; rw [e7, e7', h2, h4]
  · change y 8 = y' 8; rw [e8, e8', h1, h4]

/-! ### The slice `E_tot = F_tot = c`, `S_tot = σ` -/

/-- `y` is a positive steady state at the witness rates with totals `E_tot = F_tot = c`,
`S_tot = σ`. -/
def TwoSlice (c σ : ℝ) (y : Fin 9 → ℝ) : Prop :=
  twoNet.IsPosSteadyState twoK y ∧ y 3 + y 5 + y 6 = c ∧ y 4 + y 7 + y 8 = c ∧
    y 0 + y 1 + y 2 + y 5 + y 6 + y 7 + y 8 = σ

/-- Two states of the slice lie in the same compatibility class. -/
theorem TwoSlice.sub_mem {c σ : ℝ} {y y' : Fin 9 → ℝ} (hy : TwoSlice c σ y)
    (hy' : TwoSlice c σ y') : y - y' ∈ twoNet.stoichSubspace := by
  obtain ⟨-, a1, a2, a3⟩ := hy
  obtain ⟨-, b1, b2, b3⟩ := hy'
  refine two_mem_of_cons ?_ ?_ ?_ <;> simp only [Pi.sub_apply] <;> linarith

/-- The slice is a union of compatibility classes: a positive steady state in the class of a
slice state is in the slice. -/
theorem TwoSlice.of_sub_mem {c σ : ℝ} {y y' : Fin 9 → ℝ} (hy : TwoSlice c σ y)
    (hy' : twoNet.IsPosSteadyState twoK y') (hm : y' - y ∈ twoNet.stoichSubspace) :
    TwoSlice c σ y' := by
  obtain ⟨-, a1, a2, a3⟩ := hy
  obtain ⟨c1, c2, c3⟩ := two_cons_of_mem hm
  simp only [Pi.sub_apply] at c1 c2 c3
  exact ⟨hy', by linarith, by linarith, by linarith⟩

/-- The witness class (`twoX`) is the slice `c = 3`, `σ = 8`. -/
theorem twoX_slice : TwoSlice 3 8 twoX :=
  ⟨twoX_steady, by norm_num [twoX], by norm_num [twoX], by norm_num [twoX]⟩

/-- **The two branches** (pure algebra): the symmetric branch, or the asymmetric branch
`F = S₀E`, `S₁ = 1`, `S₀S₂ = 1`. -/
theorem two_slice_cases {c σ y0 y1 y2 y3 y4 y5 y6 y7 y8 : ℝ} (p3 : 0 < y3) (p4 : 0 < y4)
    (e5 : y5 = 2 * y0 * y3) (e6 : y6 = y1 * y3) (e7 : y7 = 2 * y2 * y4)
    (e8 : y8 = y1 * y4) (g0 : y0 * y3 = y1 * y4) (g2 : y1 * y3 = y2 * y4)
    (cE : y3 + y5 + y6 = c) (cF : y4 + y7 + y8 = c)
    (cS : y0 + y1 + y2 + y5 + y6 + y7 + y8 = σ) :
    (y3 = y4 ∧ y1 = y0 ∧ y2 = y0 ∧ y3 * (1 + 3 * y0) = c ∧ 3 * y0 + 6 * y0 * y3 = σ) ∨
      (y4 = y0 * y3 ∧ y1 = 1 ∧ y0 * y2 = 1 ∧ y3 * (2 + 2 * y0) = c ∧
        y0 + y2 + 1 + 3 * c / 2 = σ) := by
  have h1 : y3 - y4 + y0 * y3 - y1 * y3 = 0 := by
    linear_combination cE - cF - e5 - e6 + e7 + e8 - 2 * g2 - g0
  have h2 : (y3 - y4) * (y4 - y0 * y3) = 0 := by linear_combination y4 * h1 - y3 * g0
  rcases mul_eq_zero.mp h2 with hA | hB
  · left
    have hA : y3 = y4 := sub_eq_zero.mp hA
    have hy1 : y1 = y0 := by
      have : (y1 - y0) * y3 = 0 := by linear_combination -g0 + y1 * hA
      linarith [(mul_eq_zero.mp this).resolve_right p3.ne']
    have hy2 : y2 = y0 := by
      have : (y2 - y1) * y3 = 0 := by linear_combination -g2 + y2 * hA
      linarith [(mul_eq_zero.mp this).resolve_right p3.ne']
    exact ⟨hA, hy1, hy2, by linear_combination cE - e5 - e6 - y3 * hy1,
      by linear_combination cS - e5 - e6 - e7 - e8 - (1 + y3 + y4) * hy1 - (1 + 2 * y4) * hy2
        + 3 * y0 * hA⟩
  · right
    have hB : y4 = y0 * y3 := sub_eq_zero.mp hB
    have hy1 : y1 = 1 := by
      have : (y1 - 1) * y4 = 0 := by linear_combination -g0 - hB
      linarith [(mul_eq_zero.mp this).resolve_right p4.ne']
    have hy2' : y2 * y4 = y3 := by linear_combination -g2 + y3 * hy1
    have hp : y0 * y2 = 1 := by
      have : y3 * (y0 * y2 - 1) = 0 := by linear_combination hy2' - y2 * hB
      linarith [(mul_eq_zero.mp this).resolve_left p3.ne']
    have hE : y3 * (2 + 2 * y0) = c := by linear_combination cE - e5 - e6 - y3 * hy1
    exact ⟨hB, hy1, hp, hE, by
      linear_combination cS - e5 - e6 - e7 - e8 - (1 + y3 + y4) * hy1 - 2 * hy2' - hB
        - (3 / 2) * hE⟩

/-- The two branches for a state of the slice. -/
theorem TwoSlice.cases {c σ : ℝ} {y : Fin 9 → ℝ} (hy : TwoSlice c σ y) :
    (y 3 = y 4 ∧ y 1 = y 0 ∧ y 2 = y 0 ∧ y 3 * (1 + 3 * y 0) = c ∧
        3 * y 0 + 6 * y 0 * y 3 = σ) ∨
      (y 4 = y 0 * y 3 ∧ y 1 = 1 ∧ y 0 * y 2 = 1 ∧ y 3 * (2 + 2 * y 0) = c ∧
        y 0 + y 2 + 1 + 3 * c / 2 = σ) := by
  obtain ⟨⟨hpos, hss⟩, cE, cF, cS⟩ := hy
  obtain ⟨e5, e6, e7, e8, g0, g2⟩ := two_steady_eqs hss
  exact two_slice_cases (hpos 3) (hpos 4) e5 e6 e7 e8 g0 g2 cE cF cS

/-- On the symmetric branch the sign of `σ − (3 + 3c/2)` is the sign of `s − 1`. -/
theorem two_slice_threshold {c σ s e : ℝ} (hE : e * (1 + 3 * s) = c)
    (hS : 3 * s + 6 * s * e = σ) : σ - (3 + 3 * c / 2) = (s - 1) * (3 + 3 * e / 2) := by
  linear_combination -hS + (3 / 2) * hE

/-- The symmetric branch has at most one point in each slice. -/
theorem two_sym_unique {c σ s e s' e' : ℝ} (hσ : 0 < σ) (hs : 0 < s) (hs' : 0 < s')
    (hE : e * (1 + 3 * s) = c) (hS : 3 * s + 6 * s * e = σ) (hE' : e' * (1 + 3 * s') = c)
    (hS' : 3 * s' + 6 * s' * e' = σ) : s = s' ∧ e = e' := by
  have q : 9 * s ^ 2 + (3 + 6 * c - 3 * σ) * s - σ = 0 := by
    linear_combination (1 + 3 * s) * hS - 6 * s * hE
  have q' : 9 * s' ^ 2 + (3 + 6 * c - 3 * σ) * s' - σ = 0 := by
    linear_combination (1 + 3 * s') * hS' - 6 * s' * hE'
  have hss : s = s' := by
    have h : (s - s') * (9 * (s + s') + 3 + 6 * c - 3 * σ) = 0 := by linear_combination q - q'
    rcases mul_eq_zero.mp h with h | h
    · linarith
    · have : 9 * s * s' + σ = 0 := by linear_combination -q + s * h
      have := mul_pos hs hs'
      linarith
  subst hss
  refine ⟨rfl, ?_⟩
  have : (e - e') * (1 + 3 * s) = 0 := by linear_combination hE - hE'
  linarith [(mul_eq_zero.mp this).resolve_right (by linarith)]

/-! ### The monostable region -/

/-- For `σ ≤ 3 + 3c/2` every state of the slice is on the symmetric branch. -/
theorem TwoSlice.symmetric {c σ : ℝ} {y : Fin 9 → ℝ} (hσ : σ ≤ 3 + 3 * c / 2)
    (hy : TwoSlice c σ y) :
    y 3 = y 4 ∧ y 1 = y 0 ∧ y 2 = y 0 ∧ y 3 * (1 + 3 * y 0) = c ∧
      3 * y 0 + 6 * y 0 * y 3 = σ := by
  have p0 := hy.1.1 0
  have p2 := hy.1.1 2
  rcases hy.cases with h | ⟨hB, hy1, hp, hE, hS⟩
  · exact h
  · have hsq : (y 0 - y 2) ^ 2 ≤ 0 := by nlinarith
    have h02 : y 0 = y 2 := by nlinarith [sq_nonneg (y 0 - y 2)]
    have h0 : y 0 = 1 := by
      rw [← h02] at hp
      nlinarith
    refine ⟨by rw [hB, h0, one_mul], by rw [hy1, h0], by rw [← h02], ?_, ?_⟩
    · rw [h0] at hE ⊢; linarith
    · rw [h0] at hE hS ⊢; linarith

/-- **Monostability**: for `σ ≤ 3 + 3c/2` the slice contains at most one positive steady state. -/
theorem two_slice_monostable {c σ : ℝ} {y y' : Fin 9 → ℝ} (hσ : σ ≤ 3 + 3 * c / 2)
    (hy : TwoSlice c σ y) (hy' : TwoSlice c σ y') : y = y' := by
  obtain ⟨a3, a1, a2, aE, aS⟩ := hy.symmetric hσ
  obtain ⟨b3, b1, b2, bE, bS⟩ := hy'.symmetric hσ
  have p0 := hy.1.1 0
  have p3 := hy.1.1 3
  have hσ0 : 0 < σ := by rw [← aS]; positivity
  obtain ⟨hs, he⟩ := two_sym_unique hσ0 p0 (hy'.1.1 0) aE aS bE bS
  exact two_eq_of hy.1.2 hy'.1.2 hs (by rw [a1, b1, hs]) (by rw [a2, b2, hs]) he
    (by rw [← a3, ← b3, he])

/-- The positive root `s` of `9s² + (3 + 6c − 3σ)s − σ`. -/
def twoSymS (c σ : ℝ) : ℝ :=
  (-(3 + 6 * c - 3 * σ) + √((3 + 6 * c - 3 * σ) ^ 2 + 36 * σ)) / 18

/-- `twoSymS c σ` is positive. -/
theorem twoSymS_pos {c σ : ℝ} (hσ : 0 < σ) : 0 < twoSymS c σ := by
  have hD : 0 ≤ (3 + 6 * c - 3 * σ) ^ 2 + 36 * σ := by positivity
  have hR := Real.sq_sqrt hD
  have hR0 := Real.sqrt_nonneg ((3 + 6 * c - 3 * σ) ^ 2 + 36 * σ)
  have : 3 + 6 * c - 3 * σ < √((3 + 6 * c - 3 * σ) ^ 2 + 36 * σ) := by
    by_contra h
    push Not at h
    nlinarith
  unfold twoSymS
  linarith

/-- `twoSymS c σ` solves the quadratic. -/
theorem twoSymS_quad {c σ : ℝ} (hσ : 0 ≤ σ) :
    9 * twoSymS c σ ^ 2 + (3 + 6 * c - 3 * σ) * twoSymS c σ - σ = 0 := by
  have hR := Real.sq_sqrt (show 0 ≤ (3 + 6 * c - 3 * σ) ^ 2 + 36 * σ by positivity)
  unfold twoSymS
  linear_combination hR / 36

/-- The symmetric steady state of the slice. -/
def twoSym (c σ : ℝ) : Fin 9 → ℝ := twoXm (twoSymS c σ) (c / (1 + 3 * twoSymS c σ))

/-- A point of the symmetric family with the right totals is in the slice. -/
theorem twoXm_slice {c σ s e : ℝ} (hs : 0 < s) (he : 0 < e) (hE : e * (1 + 3 * s) = c)
    (hS : 3 * s + 6 * s * e = σ) : TwoSlice c σ (twoXm s e) := by
  refine ⟨twoXm_steady hs he, ?_, ?_, ?_⟩
  · change e + 2 * s * e + s * e = c
    linear_combination hE
  · change e + 2 * s * e + s * e = c
    linear_combination hE
  · change s + s + s + 2 * s * e + s * e + 2 * s * e + s * e = σ
    linear_combination hS

/-- The defining relations of the symmetric state: `e(1 + 3s) = c`, `3s + 6se = σ`. -/
theorem twoSym_spec {c σ : ℝ} (hσ : 0 < σ) :
    0 < twoSymS c σ ∧ c / (1 + 3 * twoSymS c σ) * (1 + 3 * twoSymS c σ) = c ∧
      3 * twoSymS c σ + 6 * twoSymS c σ * (c / (1 + 3 * twoSymS c σ)) = σ := by
  have hs := twoSymS_pos (c := c) hσ
  have hq := twoSymS_quad (c := c) hσ.le
  set s := twoSymS c σ
  have h1 : (0 : ℝ) < 1 + 3 * s := by linarith
  have hE : c / (1 + 3 * s) * (1 + 3 * s) = c := div_mul_cancel₀ c h1.ne'
  refine ⟨hs, hE, ?_⟩
  have key : (3 * s + 6 * s * (c / (1 + 3 * s)) - σ) * (1 + 3 * s) = 0 := by
    linear_combination hq + 6 * s * hE
  linarith [(mul_eq_zero.mp key).resolve_right h1.ne']

/-- **Existence**: for `c, σ > 0` the symmetric state lies in the slice. -/
theorem twoSym_slice {c σ : ℝ} (hc : 0 < c) (hσ : 0 < σ) : TwoSlice c σ (twoSym c σ) := by
  obtain ⟨hs, hE, hS⟩ := twoSym_spec (c := c) hσ
  exact twoXm_slice hs (by positivity) hE hS

/-- **Exactly one positive steady state in the monostable region.** -/
theorem two_slice_existsUnique {c σ : ℝ} (hc : 0 < c) (hσ : 0 < σ)
    (hσc : σ ≤ 3 + 3 * c / 2) : ∃! y, TwoSlice c σ y :=
  ⟨twoSym c σ, twoSym_slice hc hσ, fun _ hy => two_slice_monostable hσc hy (twoSym_slice hc hσ)⟩

/-- The restricted Jacobian at a symmetric state is `twoRM`. -/
theorem twoR_of_symmetric {y : Fin 9 → ℝ} (a3 : y 3 = y 4) (a1 : y 1 = y 0) (a2 : y 2 = y 0) :
    twoR y = twoRM (y 0) (y 3) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [twoR, twoRM, a1, a2, ← a3] <;> ring

/-- **Stability in the monostable region**: for `σ < 3 + 3c/2` the steady state is linearly stable
within its class (the restricted Jacobian is Hurwitz). -/
theorem two_slice_isHurwitz {c σ : ℝ} {y : Fin 9 → ℝ} (hσ : σ < 3 + 3 * c / 2)
    (hy : TwoSlice c σ y) : IsHurwitz (twoC * twoNet.massActionJacobian twoK y * twoB) := by
  obtain ⟨a3, a1, a2, aE, aS⟩ := hy.symmetric hσ.le
  have p0 := hy.1.1 0
  have p3 := hy.1.1 3
  have hth := two_slice_threshold aE aS
  have hs1 : y 0 < 1 := by
    by_contra h
    push Not at h
    nlinarith
  rw [two_restrict, twoR_of_symmetric a3 a1 a2]
  exact twoRM_isHurwitz p0 hs1 p3

/-- **Local exponential stability within the class** in the monostable region. -/
theorem two_slice_classStable {c σ : ℝ} {y : Fin 9 → ℝ} (hσ : σ < 3 + 3 * c / 2)
    (hy : TwoSlice c σ y) :
    ∃ δ > 0, ∃ κ > 0, ∃ K > 0, ∀ (x : ℝ → Fin 9 → ℝ) (T : ℝ),
      twoNet.MassActionTrajectoryOn twoK x T → x 0 - y ∈ twoNet.stoichSubspace →
        ‖x 0 - y‖ < δ →
          ∀ t ∈ Ico 0 T, ‖x t - y‖ ^ 2 ≤ K * Real.exp (-κ * t) * ‖x 0 - y‖ ^ 2 :=
  twoNet.classLocallyExpStable_of_restrict hy.1.2 (B := twoB) (C := twoC)
    (fun _ hu => two_proj hu) (two_slice_isHurwitz hσ hy)

/-! ### The multistationary region -/

/-- The asymmetric-branch state with `S₀ = r`: `(r, 1, 1/r, E, rE, 2rE, E, 2E, rE)`,
`E = c/(2 + 2r)`. -/
def twoBr (c r : ℝ) : Fin 9 → ℝ :=
  ![r, 1, 1 / r, c / (2 + 2 * r), r * (c / (2 + 2 * r)), 2 * r * (c / (2 + 2 * r)),
    c / (2 + 2 * r), 2 * (c / (2 + 2 * r)), r * (c / (2 + 2 * r))]

/-- `twoBr c r` is in the slice when `r + 1/r + 1 + 3c/2 = σ`. -/
theorem twoBr_slice {c σ r : ℝ} (hc : 0 < c) (hr : 0 < r) (hS : r + 1 / r + 1 + 3 * c / 2 = σ) :
    TwoSlice c σ (twoBr c r) := by
  have hE : 0 < c / (2 + 2 * r) := by positivity
  have h2 : (2 + 2 * r) ≠ 0 := by positivity
  refine ⟨⟨fun i => ?_, ?_⟩, ?_, ?_, ?_⟩
  · fin_cases i
    exacts [hr, one_pos, one_div_pos.mpr hr, hE, mul_pos hr hE, mul_pos (mul_pos two_pos hr) hE,
      hE, mul_pos two_pos hE, mul_pos hr hE]
  · refine two_steady_of rfl ?_ ?_ ?_ ?_ ?_
    · change c / (2 + 2 * r) = 1 * (c / (2 + 2 * r)); ring
    · change 2 * (c / (2 + 2 * r)) = 2 * (1 / r) * (r * (c / (2 + 2 * r))); field_simp
    · change r * (c / (2 + 2 * r)) = 1 * (r * (c / (2 + 2 * r))); ring
    · change r * (c / (2 + 2 * r)) = 1 * (r * (c / (2 + 2 * r))); ring
    · change 1 * (c / (2 + 2 * r)) = 1 / r * (r * (c / (2 + 2 * r))); field_simp
  · change c / (2 + 2 * r) + 2 * r * (c / (2 + 2 * r)) + c / (2 + 2 * r) = c
    field_simp; ring
  · change r * (c / (2 + 2 * r)) + 2 * (c / (2 + 2 * r)) + r * (c / (2 + 2 * r)) = c
    field_simp; ring
  · change r + 1 + 1 / r + 2 * r * (c / (2 + 2 * r)) + c / (2 + 2 * r) + 2 * (c / (2 + 2 * r))
      + r * (c / (2 + 2 * r)) = σ
    rw [← hS]
    field_simp
    ring

/-- The larger root of `r² − m r + 1`, `m = σ − 1 − 3c/2`. -/
def twoRp (c σ : ℝ) : ℝ :=
  ((σ - 1 - 3 * c / 2) + √((σ - 1 - 3 * c / 2) ^ 2 - 4)) / 2

/-- The smaller root of `r² − m r + 1`, `m = σ − 1 − 3c/2`. -/
def twoRm (c σ : ℝ) : ℝ :=
  ((σ - 1 - 3 * c / 2) - √((σ - 1 - 3 * c / 2) ^ 2 - 4)) / 2

/-- Properties of the two roots beyond the threshold: positive, distinct, different from `1`,
sum `m`, product `1`. -/
theorem twoR_roots {c σ : ℝ} (hσ : 3 + 3 * c / 2 < σ) :
    0 < twoRm c σ ∧ twoRm c σ < twoRp c σ ∧ twoRm c σ < 1 ∧ 1 < twoRp c σ ∧
      twoRp c σ + twoRm c σ = σ - 1 - 3 * c / 2 ∧ twoRp c σ * twoRm c σ = 1 := by
  set m := σ - 1 - 3 * c / 2 with hm
  have hm2 : 2 < m := by linarith
  have hD : 0 ≤ m ^ 2 - 4 := by nlinarith
  have hR := Real.sq_sqrt hD
  have hR0 : 0 < √(m ^ 2 - 4) := Real.sqrt_pos.mpr (by nlinarith)
  have hRm : √(m ^ 2 - 4) < m := by nlinarith
  have hR2 : m - 2 < √(m ^ 2 - 4) := by nlinarith
  unfold twoRp twoRm
  refine ⟨by linarith, by linarith, by linarith, by linarith, by ring, by
    linear_combination -hR / 4⟩

/-- The asymmetric state with `S₀ = twoRp` or `twoRm` is in the slice. -/
theorem twoBr_root_slice {c σ r r' : ℝ} (hc : 0 < c) (hr : 0 < r)
    (hsum : r + r' = σ - 1 - 3 * c / 2) (hprod : r * r' = 1) : TwoSlice c σ (twoBr c r) := by
  refine twoBr_slice hc hr ?_
  have : 1 / r = r' := by field_simp; linarith
  rw [this]
  linarith

/-- **Exactly three positive steady states beyond the threshold** `σ > 3 + 3c/2`: the symmetric
one and the two asymmetric ones, pairwise distinct, and every positive steady state of the slice
is one of them. -/
theorem two_slice_three {c σ : ℝ} (hc : 0 < c) (hσ : 3 + 3 * c / 2 < σ) :
    TwoSlice c σ (twoSym c σ) ∧ TwoSlice c σ (twoBr c (twoRp c σ)) ∧
      TwoSlice c σ (twoBr c (twoRm c σ)) ∧
      twoSym c σ ≠ twoBr c (twoRp c σ) ∧ twoSym c σ ≠ twoBr c (twoRm c σ) ∧
      twoBr c (twoRp c σ) ≠ twoBr c (twoRm c σ) ∧
      ∀ y, TwoSlice c σ y →
        y = twoSym c σ ∨ y = twoBr c (twoRp c σ) ∨ y = twoBr c (twoRm c σ) := by
  obtain ⟨hm0, hmp, hm1, hp1, hsum, hprod⟩ := twoR_roots hσ
  have hσ0 : 0 < σ := by linarith
  have hsym := twoSym_slice hc hσ0
  have hp := twoBr_root_slice hc (by linarith) hsum hprod
  have hm := twoBr_root_slice (σ := σ) (r' := twoRp c σ) hc hm0 (by linarith)
    (by linarith : twoRm c σ * twoRp c σ = 1)
  -- the symmetric state has `S₀ = S₁`, the asymmetric ones have `S₁ = 1 ≠ S₀`
  have hne : ∀ r, r ≠ 1 → twoSym c σ ≠ twoBr c r := fun r hr h => by
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    change twoSymS c σ = r at h0
    change twoSymS c σ = 1 at h1
    exact hr (h0.symm.trans h1)
  refine ⟨hsym, hp, hm, hne _ hp1.ne', hne _ hm1.ne, fun h => ?_, fun y hy => ?_⟩
  · have h0 := congrFun h 0
    change twoRp c σ = twoRm c σ at h0
    linarith
  rcases hy.cases with ⟨a3, a1, a2, aE, aS⟩ | ⟨hB, hy1, hpr, hE, hS⟩
  · left
    obtain ⟨hs0, bE, bS⟩ := twoSym_spec (c := c) hσ0
    obtain ⟨hs, he⟩ := two_sym_unique hσ0 (hy.1.1 0) hs0 aE aS bE bS
    exact two_eq_of hy.1.2 hsym.1.2 hs (by rw [a1, hs]; rfl) (by rw [a2, hs]; rfl) he
      (by rw [← a3, he]; rfl)
  · right
    have p0 := hy.1.1 0
    have hq : (y 0 - twoRp c σ) * (y 0 - twoRm c σ) = 0 := by
      linear_combination y 0 * hS - hpr - y 0 * hsum + hprod
    have key : ∀ r, 0 < r → y 0 = r → y = twoBr c r := fun r hr hr0 => by
      have h2 : (2 : ℝ) + 2 * r ≠ 0 := by positivity
      have hy3 : y 3 = c / (2 + 2 * r) := by
        rw [eq_div_iff h2, ← hr0]; exact hE
      refine two_eq_of hy.1.2 (twoBr_slice (σ := σ) hc hr (by
        have : 1 / r = y 2 := by rw [← hr0]; field_simp; linarith
        linarith)).1.2 hr0 hy1 ?_ hy3 ?_
      · change y 2 = 1 / r
        rw [← hr0]; field_simp; linarith
      · change y 4 = r * (c / (2 + 2 * r))
        rw [hB, hy3, hr0]
    rcases mul_eq_zero.mp hq with h | h
    · exact Or.inl (key _ (by linarith) (sub_eq_zero.mp h))
    · exact Or.inr (key _ hm0 (sub_eq_zero.mp h))

/-- Beyond the threshold the symmetric state is linearly unstable. -/
theorem two_slice_sym_unstable {c σ : ℝ} (hc : 0 < c) (hσ : 3 + 3 * c / 2 < σ) :
    ¬ IsHurwitz (twoC * twoNet.massActionJacobian twoK (twoSym c σ) * twoB) := by
  have hσ0 : 0 < σ := by linarith
  obtain ⟨hs, hE, hS⟩ := twoSym_spec (c := c) hσ0
  set s := twoSymS c σ
  have h1 : (0 : ℝ) < 1 + 3 * s := by linarith
  have hth := two_slice_threshold hE hS
  have he : 0 < c / (1 + 3 * s) := by positivity
  have hs1 : 1 < s := by
    by_contra h
    push Not at h
    nlinarith
  rw [two_restrict]
  change ¬ IsHurwitz (twoR (twoXm s (c / (1 + 3 * s))))
  rw [twoR_twoXm]
  exact twoRM_not_isHurwitz hs1 he

end LeanTheory.CRN.Design
