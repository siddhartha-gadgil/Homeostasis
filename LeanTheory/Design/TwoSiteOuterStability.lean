/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Design.TwoSiteMonostable

/-!
# Two-site phosphorylation: the outer states are stable (notes N-010, Q-2)

On the slice `E_tot = F_tot = c`, `S_tot = σ` at the witness rates (`Design/TwoSiteMonostable`),
beyond the threshold `σ > 3 + 3c/2` there are exactly three positive steady states. Here we prove
that the two **asymmetric** ones `twoBr c r` (`S₀ = r`, `r = twoRp c σ`, `twoRm c σ`) are locally
exponentially stable within their class, for **all** such `(c, σ)` (`two_slice_outer_classStable`),
completing the bistability picture (`two_slice_bistable`): in every class of the slice beyond the
threshold, two stable states and one unstable state.

On the asymmetric branch the restricted Jacobian has entries with `1/r`; we work with
`twoSB r E = r • twoR (twoBr c r)` (`E = c/(2 + 2r)`), whose entries are polynomials, and use that
scaling by `r > 0` preserves the Hurwitz property (`isHurwitz_of_smul`). Its characteristic
polynomial (sympy oracle) has constant term `288E²(r − 1)²(r + 1)²r⁵`, positive exactly when
`r ≠ 1`, and Hurwitz determinants `Δ₂, …, Δ₅` that are polynomials in `(r, E)` with **positive
coefficients** (20, 56, 109 and 168 terms). Degree-6 Routh–Hurwitz (format 8) concludes.

Label: exact, idealized; witness rates `twoK`, all classes with `E_tot = F_tot`.
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN.Design

open Matrix ReactionNetwork Set

/-- Scaling by a positive constant preserves the Hurwitz property (eigenvalues scale by `r`). -/
theorem isHurwitz_of_smul {n : ℕ} {J : Matrix (Fin n) (Fin n) ℝ} {r : ℝ} (hr : 0 < r)
    (h : IsHurwitz (r • J)) : IsHurwitz J := by
  intro lam v hv he
  have hs : toComplex (r • J) = (r : ℂ) • toComplex J := by
    ext i j; simp [toComplex_apply]
  have := h ((r : ℂ) * lam) v hv (by rw [hs, Matrix.smul_mulVec, he, smul_smul])
  rw [Complex.re_ofReal_mul] at this
  exact neg_of_mul_neg_right this hr.le

/-- `r` times the restricted Jacobian on the asymmetric branch (`S₀ = r`, `E = e`). -/
def twoSB (r E : ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  !![-3*E*r ^ 2 - 3*E*r, 0, 4*r, 4*r, 4*r, 4*r;
     0, -4*E*r ^ 2, 0, 2*r, r + 4, 4;
     -4*E*r, -4*E*r, -4*E*r - 4*r ^ 2 - 2*r, -4*E*r - 4*r ^ 2, -4*E*r, -4*E*r;
     3*E*r, 0, -3*r, -6*r, 0, 0;
     0, 4*E*r ^ 2, 0, 0, -2*r - 4, -4;
     3*E*r ^ 2, 0, 0, 0, -3*r, -6*r]

/-- Coefficient `b1` of the characteristic polynomial of `twoSB r E`. -/
def twoBB1 (r E : ℝ) : ℝ :=
  7 * r ^ 2 * E + 4 * r ^ 2 + 7 * r * E + 16 * r + 4

/-- Coefficient `b2` of the characteristic polynomial of `twoSB r E`. -/
def twoBB2 (r E : ℝ) : ℝ :=
  12 * r ^ 4 * E ^ 2 + 28 * r ^ 4 * E + 40 * r ^ 3 * E ^ 2 + 108 * r ^ 3 * E + 44 * r ^ 3 + 12 * r
  ^ 2 * E ^ 2 + 108 * r ^ 2 * E + 104 * r ^ 2 + 28 * r * E + 44 * r

/-- Coefficient `b3` of the characteristic polynomial of `twoSB r E`. -/
def twoBB3 (r E : ℝ) : ℝ :=
  48 * r ^ 6 * E ^ 2 + 48 * r ^ 5 * E ^ 3 + 180 * r ^ 5 * E ^ 2 + 244 * r ^ 5 * E + 48 * r ^ 4 * E
  ^ 3 + 488 * r ^ 4 * E ^ 2 + 620 * r ^ 4 * E + 144 * r ^ 4 + 180 * r ^ 3 * E ^ 2 + 620 * r ^ 3 *
  E + 288 * r ^ 3 + 48 * r ^ 2 * E ^ 2 + 244 * r ^ 2 * E + 144 * r ^ 2

/-- Coefficient `b4` of the characteristic polynomial of `twoSB r E`. -/
def twoBB4 (r E : ℝ) : ℝ :=
  288 * r ^ 7 * E ^ 2 + 480 * r ^ 6 * E ^ 3 + 936 * r ^ 6 * E ^ 2 + 624 * r ^ 6 * E + 480 * r ^ 5
  * E ^ 3 + 1696 * r ^ 5 * E ^ 2 + 1488 * r ^ 5 * E + 144 * r ^ 5 + 936 * r ^ 4 * E ^ 2 + 1488 * r
  ^ 4 * E + 288 * r ^ 4 + 288 * r ^ 3 * E ^ 2 + 624 * r ^ 3 * E + 144 * r ^ 3

/-- Coefficient `b5` of the characteristic polynomial of `twoSB r E`. -/
def twoBB5 (r E : ℝ) : ℝ :=
  528 * r ^ 8 * E ^ 2 + 1008 * r ^ 7 * E ^ 3 + 1536 * r ^ 7 * E ^ 2 + 432 * r ^ 7 * E + 1008 * r ^
  6 * E ^ 3 + 1632 * r ^ 6 * E ^ 2 + 1296 * r ^ 6 * E + 1536 * r ^ 5 * E ^ 2 + 1296 * r ^ 5 * E +
  528 * r ^ 4 * E ^ 2 + 432 * r ^ 4 * E

/-- Constant coefficient `b6 = 288 E² (r − 1)² (r + 1)² r⁵`. -/
def twoBB6 (r E : ℝ) : ℝ :=
  288 * E ^ 2 * (r - 1) ^ 2 * (r + 1) ^ 2 * r ^ 5

/-- The Hurwitz determinant `Δ₂` of `twoSB r E` (20 terms, all positive). -/
def twoBΔ₂ (r E : ℝ) : ℝ :=
  84 * r ^ 6 * E ^ 3 + 196 * r ^ 6 * E ^ 2 + 112 * r ^ 6 * E + 316 * r ^ 5 * E ^ 3 + 1124 * r ^ 5
  * E ^ 2 + 944 * r ^ 5 * E + 176 * r ^ 5 + 316 * r ^ 4 * E ^ 3 + 1760 * r ^ 4 * E ^ 2 + 2688 * r
  ^ 4 * E + 976 * r ^ 4 + 84 * r ^ 3 * E ^ 3 + 1124 * r ^ 3 * E ^ 2 + 2688 * r ^ 3 * E + 1728 * r
  ^ 3 + 196 * r ^ 2 * E ^ 2 + 944 * r ^ 2 * E + 976 * r ^ 2 + 112 * r * E + 176 * r

/-- Part 0 of the Hurwitz determinant `Δ₃` of `twoSB r E` (positive coefficients). -/
def twoBΔ₃_0 (r E : ℝ) : ℝ :=
  4032 * r ^ 12 * E ^ 5 + 9408 * r ^ 12 * E ^ 4 + 5376 * r ^ 12 * E ^ 3 + 4032 * r ^ 11 * E ^ 6 +
  39696 * r ^ 11 * E ^ 5 + 100992 * r ^ 11 * E ^ 4 + 97168 * r ^ 11 * E ^ 3 + 31168 * r ^ 11 * E ^
  2 + 19200 * r ^ 10 * E ^ 6 + 152880 * r ^ 10 * E ^ 5 + 461352 * r ^ 10 * E ^ 4 + 602304 * r ^ 10
  * E ^ 3 + 321856 * r ^ 10 * E ^ 2 + 49088 * r ^ 10 * E + 30336 * r ^ 9 * E ^ 6 + 298112 * r ^ 9
  * E ^ 5 + 1110816 * r ^ 9 * E ^ 4 + 1844128 * r ^ 9 * E ^ 3 + 1396032 * r ^ 9 * E ^ 2 + 405440 *
  r ^ 9 * E + 23040 * r ^ 9 + 19200 * r ^ 8 * E ^ 6 + 298112 * r ^ 8 * E ^ 5 + 1460592 * r ^ 8 * E
  ^ 4 + 3192592 * r ^ 8 * E ^ 3 + 3210176 * r ^ 8 * E ^ 2 + 1372608 * r ^ 8 * E + 168192 * r ^ 8 +
  4032 * r ^ 7 * E ^ 6 + 152880 * r ^ 7 * E ^ 5

/-- Part 1 of the Hurwitz determinant `Δ₃` of `twoSB r E` (positive coefficients). -/
def twoBΔ₃_1 (r E : ℝ) : ℝ :=
  1110816 * r ^ 7 * E ^ 4 + 3192592 * r ^ 7 * E ^ 3 + 4209664 * r ^ 7 * E ^ 2 + 2444480 * r ^ 7 *
  E + 474624 * r ^ 7 + 39696 * r ^ 6 * E ^ 5 + 461352 * r ^ 6 * E ^ 4 + 1844128 * r ^ 6 * E ^ 3 +
  3210176 * r ^ 6 * E ^ 2 + 2444480 * r ^ 6 * E + 658944 * r ^ 6 + 4032 * r ^ 5 * E ^ 5 + 100992 *
  r ^ 5 * E ^ 4 + 602304 * r ^ 5 * E ^ 3 + 1396032 * r ^ 5 * E ^ 2 + 1372608 * r ^ 5 * E + 474624
  * r ^ 5 + 9408 * r ^ 4 * E ^ 4 + 97168 * r ^ 4 * E ^ 3 + 321856 * r ^ 4 * E ^ 2 + 405440 * r ^ 4
  * E + 168192 * r ^ 4 + 5376 * r ^ 3 * E ^ 3 + 31168 * r ^ 3 * E ^ 2 + 49088 * r ^ 3 * E + 23040
  * r ^ 3

/-- The Hurwitz determinant `Δ₃` of `twoSB r E` (56 terms, all positive), in parts. -/
def twoBΔ₃ (r E : ℝ) : ℝ :=
  twoBΔ₃_0 r E + twoBΔ₃_1 r E

/-- Part 0 of the Hurwitz determinant `Δ₄` of `twoSB r E` (positive coefficients). -/
def twoBΔ₄_0 (r E : ℝ) : ℝ :=
  1161216 * r ^ 19 * E ^ 7 + 2709504 * r ^ 19 * E ^ 6 + 1548288 * r ^ 19 * E ^ 5 + 3096576 * r ^
  18 * E ^ 8 + 19190016 * r ^ 18 * E ^ 7 + 40504320 * r ^ 18 * E ^ 6 + 35279616 * r ^ 18 * E ^ 5 +
  10675200 * r ^ 18 * E ^ 4 + 1935360 * r ^ 17 * E ^ 9 + 29276928 * r ^ 17 * E ^ 8 + 133464960 * r
  ^ 17 * E ^ 7 + 288243840 * r ^ 17 * E ^ 6 + 313867008 * r ^ 17 * E ^ 5 + 159134976 * r ^ 17 * E
  ^ 4 + 27930624 * r ^ 17 * E ^ 3 + 11151360 * r ^ 16 * E ^ 9 + 117757440 * r ^ 16 * E ^ 8 +
  521813376 * r ^ 16 * E ^ 7 + 1217653824 * r ^ 16 * E ^ 6 + 1557632512 * r ^ 16 * E ^ 5 +
  1061341696 * r ^ 16 * E ^ 4 + 336211968 * r ^ 16 * E ^ 3 + 33610752 * r ^ 16 * E ^ 2 + 23777280
  * r ^ 15 * E ^ 9 + 261948672 * r ^ 15 * E ^ 8 + 1263794304 * r ^ 15 * E ^ 7 + 3290388096 * r ^
  15 * E ^ 6 + 4912813056 * r ^ 15 * E ^ 5 + 4142912512 * r ^ 15 * E ^ 4 + 1837137920 * r ^ 15 * E
  ^ 3

/-- Part 1 of the Hurwitz determinant `Δ₄` of `twoSB r E` (positive coefficients). -/
def twoBΔ₄_1 (r E : ℝ) : ℝ :=
  354683904 * r ^ 15 * E ^ 2 + 18100224 * r ^ 15 * E + 23777280 * r ^ 14 * E ^ 9 + 340743168 * r ^
  14 * E ^ 8 + 1952144768 * r ^ 14 * E ^ 7 + 5929424832 * r ^ 14 * E ^ 6 + 10357208320 * r ^ 14 *
  E ^ 5 + 10519543296 * r ^ 14 * E ^ 4 + 5946079232 * r ^ 14 * E ^ 3 + 1667036160 * r ^ 14 * E ^ 2
  + 175509504 * r ^ 14 * E + 3317760 * r ^ 14 + 11151360 * r ^ 13 * E ^ 9 + 261948672 * r ^ 13 * E
  ^ 8 + 1952144768 * r ^ 13 * E ^ 7 + 7203291648 * r ^ 13 * E ^ 6 + 14981362432 * r ^ 13 * E ^ 5 +
  18169104128 * r ^ 13 * E ^ 4 + 12579072000 * r ^ 13 * E ^ 3 + 4597518336 * r ^ 13 * E ^ 2 +
  734994432 * r ^ 13 * E + 30855168 * r ^ 13 + 1935360 * r ^ 12 * E ^ 9 + 117757440 * r ^ 12 * E ^
  8 + 1263794304 * r ^ 12 * E ^ 7 + 5929424832 * r ^ 12 * E ^ 6 + 14981362432 * r ^ 12 * E ^ 5 +
  21758003200 * r ^ 12 * E ^ 4 + 18155061248 * r ^ 12 * E ^ 3 + 8224567296 * r ^ 12 * E ^ 2

/-- Part 2 of the Hurwitz determinant `Δ₄` of `twoSB r E` (positive coefficients). -/
def twoBΔ₄_2 (r E : ℝ) : ℝ :=
  1757896704 * r ^ 12 * E + 120102912 * r ^ 12 + 29276928 * r ^ 11 * E ^ 8 + 521813376 * r ^ 11 *
  E ^ 7 + 3290388096 * r ^ 11 * E ^ 6 + 10357208320 * r ^ 11 * E ^ 5 + 18169104128 * r ^ 11 * E ^
  4 + 18155061248 * r ^ 11 * E ^ 3 + 9946810368 * r ^ 11 * E ^ 2 + 2664382464 * r ^ 11 * E +
  255799296 * r ^ 11 + 3096576 * r ^ 10 * E ^ 8 + 133464960 * r ^ 10 * E ^ 7 + 1217653824 * r ^ 10
  * E ^ 6 + 4912813056 * r ^ 10 * E ^ 5 + 10519543296 * r ^ 10 * E ^ 4 + 12579072000 * r ^ 10 * E
  ^ 3 + 8224567296 * r ^ 10 * E ^ 2 + 2664382464 * r ^ 10 * E + 326467584 * r ^ 10 + 19190016 * r
  ^ 9 * E ^ 7 + 288243840 * r ^ 9 * E ^ 6 + 1557632512 * r ^ 9 * E ^ 5 + 4142912512 * r ^ 9 * E ^
  4 + 5946079232 * r ^ 9 * E ^ 3 + 4597518336 * r ^ 9 * E ^ 2 + 1757896704 * r ^ 9 * E + 255799296
  * r ^ 9 + 1161216 * r ^ 8 * E ^ 7 + 40504320 * r ^ 8 * E ^ 6

/-- Part 3 of the Hurwitz determinant `Δ₄` of `twoSB r E` (positive coefficients). -/
def twoBΔ₄_3 (r E : ℝ) : ℝ :=
  313867008 * r ^ 8 * E ^ 5 + 1061341696 * r ^ 8 * E ^ 4 + 1837137920 * r ^ 8 * E ^ 3 + 1667036160
  * r ^ 8 * E ^ 2 + 734994432 * r ^ 8 * E + 120102912 * r ^ 8 + 2709504 * r ^ 7 * E ^ 6 + 35279616
  * r ^ 7 * E ^ 5 + 159134976 * r ^ 7 * E ^ 4 + 336211968 * r ^ 7 * E ^ 3 + 354683904 * r ^ 7 * E
  ^ 2 + 175509504 * r ^ 7 * E + 30855168 * r ^ 7 + 1548288 * r ^ 6 * E ^ 5 + 10675200 * r ^ 6 * E
  ^ 4 + 27930624 * r ^ 6 * E ^ 3 + 33610752 * r ^ 6 * E ^ 2 + 18100224 * r ^ 6 * E + 3317760 * r ^
  6

/-- The Hurwitz determinant `Δ₄` of `twoSB r E` (109 terms, all positive), in parts. -/
def twoBΔ₄ (r E : ℝ) : ℝ :=
  twoBΔ₄_0 r E + twoBΔ₄_1 r E + twoBΔ₄_2 r E + twoBΔ₄_3 r E

/-- Part 0 of the Hurwitz determinant `Δ₅` of `twoSB r E` (positive coefficients). -/
def twoBΔ₅_0 (r E : ℝ) : ℝ :=
  557383680 * r ^ 27 * E ^ 9 + 1300561920 * r ^ 27 * E ^ 8 + 743178240 * r ^ 27 * E ^ 7 +
  2694021120 * r ^ 26 * E ^ 10 + 13759303680 * r ^ 26 * E ^ 9 + 25368920064 * r ^ 26 * E ^ 8 +
  19893252096 * r ^ 26 * E ^ 7 + 5496717312 * r ^ 26 * E ^ 6 + 4087480320 * r ^ 25 * E ^ 11 +
  39649665024 * r ^ 25 * E ^ 10 + 140301766656 * r ^ 25 * E ^ 9 + 248233936896 * r ^ 25 * E ^ 8 +
  231122534400 * r ^ 25 * E ^ 7 + 103662802944 * r ^ 25 * E ^ 6 + 16335396864 * r ^ 25 * E ^ 5 +
  1950842880 * r ^ 24 * E ^ 12 + 41171963904 * r ^ 24 * E ^ 11 + 262490609664 * r ^ 24 * E ^ 10 +
  835929206784 * r ^ 24 * E ^ 9 + 1515223240704 * r ^ 24 * E ^ 8 + 1594156756992 * r ^ 24 * E ^ 7
  + 931957702656 * r ^ 24 * E ^ 6 + 263594151936 * r ^ 24 * E ^ 5 + 24909373440 * r ^ 24 * E ^ 4 +
  13191413760 * r ^ 23 * E ^ 12 + 180478734336 * r ^ 23 * E ^ 11 + 1030744645632 * r ^ 23 * E ^ 10
  + 3270298438656 * r ^ 23 * E ^ 9 + 6254926387200 * r ^ 23 * E ^ 8 + 7356864703488 * r ^ 23 * E ^
  7

/-- Part 1 of the Hurwitz determinant `Δ₅` of `twoSB r E` (positive coefficients). -/
def twoBΔ₅_1 (r E : ℝ) : ℝ :=
  5181358596096 * r ^ 23 * E ^ 6 + 2019756969984 * r ^ 23 * E ^ 5 + 365914791936 * r ^ 23 * E ^ 4
  + 20509507584 * r ^ 23 * E ^ 3 + 35208069120 * r ^ 22 * E ^ 12 + 452949331968 * r ^ 22 * E ^ 11
  + 2642742484992 * r ^ 22 * E ^ 10 + 8830075339776 * r ^ 22 * E ^ 9 + 18287664500736 * r ^ 22 * E
  ^ 8 + 24005929651200 * r ^ 22 * E ^ 7 + 19702433378304 * r ^ 22 * E ^ 6 + 9611449552896 * r ^ 22
  * E ^ 5 + 2505003761664 * r ^ 22 * E ^ 4 + 281533612032 * r ^ 22 * E ^ 3 + 8615559168 * r ^ 22 *
  E ^ 2 + 47934996480 * r ^ 21 * E ^ 12 + 707870748672 * r ^ 21 * E ^ 11 + 4593467326464 * r ^ 21
  * E ^ 10 + 16931229305856 * r ^ 21 * E ^ 9 + 38824544507904 * r ^ 21 * E ^ 8 + 57145649283072 *
  r ^ 21 * E ^ 7 + 53862025285632 * r ^ 21 * E ^ 6 + 31430702075904 * r ^ 21 * E ^ 5 +
  10550170091520 * r ^ 21 * E ^ 4 + 1766640402432 * r ^ 21 * E ^ 3 + 111779315712 * r ^ 21 * E ^ 2
  + 1433272320 * r ^ 21 * E + 35208069120 * r ^ 20 * E ^ 12 + 707870748672 * r ^ 20 * E ^ 11 +
  5511869042688 * r ^ 20 * E ^ 10

/-- Part 2 of the Hurwitz determinant `Δ₅` of `twoSB r E` (positive coefficients). -/
def twoBΔ₅_2 (r E : ℝ) : ℝ :=
  23377305572352 * r ^ 20 * E ^ 9 + 60699722784768 * r ^ 20 * E ^ 8 + 101061508214784 * r ^ 20 * E
  ^ 7 + 108817172152320 * r ^ 20 * E ^ 6 + 74232474415104 * r ^ 20 * E ^ 5 + 30391917133824 * r ^
  20 * E ^ 4 + 6718969626624 * r ^ 20 * E ^ 3 + 651979653120 * r ^ 20 * E ^ 2 + 17629249536 * r ^
  20 * E + 13191413760 * r ^ 19 * E ^ 12 + 452949331968 * r ^ 19 * E ^ 11 + 4593467326464 * r ^ 19
  * E ^ 10 + 23377305572352 * r ^ 19 * E ^ 9 + 70401477611520 * r ^ 19 * E ^ 8 + 134091254102016 *
  r ^ 19 * E ^ 7 + 165049500628992 * r ^ 19 * E ^ 6 + 130084412436480 * r ^ 19 * E ^ 5 +
  63056995835904 * r ^ 19 * E ^ 4 + 17285118197760 * r ^ 19 * E ^ 3 + 2266337968128 * r ^ 19 * E ^
  2 + 96172572672 * r ^ 19 * E + 1950842880 * r ^ 18 * E ^ 12 + 180478734336 * r ^ 18 * E ^ 11 +
  2642742484992 * r ^ 18 * E ^ 10 + 16931229305856 * r ^ 18 * E ^ 9 + 60699722784768 * r ^ 18 * E
  ^ 8 + 134091254102016 * r ^ 18 * E ^ 7 + 189479427710976 * r ^ 18 * E ^ 6 + 171636492582912 * r
  ^ 18 * E ^ 5 + 96829521813504 * r ^ 18 * E ^ 4

/-- Part 3 of the Hurwitz determinant `Δ₅` of `twoSB r E` (positive coefficients). -/
def twoBΔ₅_3 (r E : ℝ) : ℝ :=
  31742717018112 * r ^ 18 * E ^ 3 + 5242257211392 * r ^ 18 * E ^ 2 + 307580239872 * r ^ 18 * E +
  41171963904 * r ^ 17 * E ^ 11 + 1030744645632 * r ^ 17 * E ^ 10 + 8830075339776 * r ^ 17 * E ^ 9
  + 38824544507904 * r ^ 17 * E ^ 8 + 101061508214784 * r ^ 17 * E ^ 7 + 165049500628992 * r ^ 17
  * E ^ 6 + 171636492582912 * r ^ 17 * E ^ 5 + 111556240736256 * r ^ 17 * E ^ 4 + 42765829963776 *
  r ^ 17 * E ^ 3 + 8519338819584 * r ^ 17 * E ^ 2 + 641532690432 * r ^ 17 * E + 4087480320 * r ^
  16 * E ^ 11 + 262490609664 * r ^ 16 * E ^ 10 + 3270298438656 * r ^ 16 * E ^ 9 + 18287664500736 *
  r ^ 16 * E ^ 8 + 57145649283072 * r ^ 16 * E ^ 7 + 108817172152320 * r ^ 16 * E ^ 6 +
  130084412436480 * r ^ 16 * E ^ 5 + 96829521813504 * r ^ 16 * E ^ 4 + 42765829963776 * r ^ 16 * E
  ^ 3 + 9989207359488 * r ^ 16 * E ^ 2 + 917007630336 * r ^ 16 * E + 39649665024 * r ^ 15 * E ^ 10
  + 835929206784 * r ^ 15 * E ^ 9 + 6254926387200 * r ^ 15 * E ^ 8 + 24005929651200 * r ^ 15 * E ^
  7 + 53862025285632 * r ^ 15 * E ^ 6

/-- Part 4 of the Hurwitz determinant `Δ₅` of `twoSB r E` (positive coefficients). -/
def twoBΔ₅_4 (r E : ℝ) : ℝ :=
  74232474415104 * r ^ 15 * E ^ 5 + 63056995835904 * r ^ 15 * E ^ 4 + 31742717018112 * r ^ 15 * E
  ^ 3 + 8519338819584 * r ^ 15 * E ^ 2 + 917007630336 * r ^ 15 * E + 2694021120 * r ^ 14 * E ^ 10
  + 140301766656 * r ^ 14 * E ^ 9 + 1515223240704 * r ^ 14 * E ^ 8 + 7356864703488 * r ^ 14 * E ^
  7 + 19702433378304 * r ^ 14 * E ^ 6 + 31430702075904 * r ^ 14 * E ^ 5 + 30391917133824 * r ^ 14
  * E ^ 4 + 17285118197760 * r ^ 14 * E ^ 3 + 5242257211392 * r ^ 14 * E ^ 2 + 641532690432 * r ^
  14 * E + 13759303680 * r ^ 13 * E ^ 9 + 248233936896 * r ^ 13 * E ^ 8 + 1594156756992 * r ^ 13 *
  E ^ 7 + 5181358596096 * r ^ 13 * E ^ 6 + 9611449552896 * r ^ 13 * E ^ 5 + 10550170091520 * r ^
  13 * E ^ 4 + 6718969626624 * r ^ 13 * E ^ 3 + 2266337968128 * r ^ 13 * E ^ 2 + 307580239872 * r
  ^ 13 * E + 557383680 * r ^ 12 * E ^ 9 + 25368920064 * r ^ 12 * E ^ 8 + 231122534400 * r ^ 12 * E
  ^ 7 + 931957702656 * r ^ 12 * E ^ 6 + 2019756969984 * r ^ 12 * E ^ 5 + 2505003761664 * r ^ 12 *
  E ^ 4

/-- Part 5 of the Hurwitz determinant `Δ₅` of `twoSB r E` (positive coefficients). -/
def twoBΔ₅_5 (r E : ℝ) : ℝ :=
  1766640402432 * r ^ 12 * E ^ 3 + 651979653120 * r ^ 12 * E ^ 2 + 96172572672 * r ^ 12 * E +
  1300561920 * r ^ 11 * E ^ 8 + 19893252096 * r ^ 11 * E ^ 7 + 103662802944 * r ^ 11 * E ^ 6 +
  263594151936 * r ^ 11 * E ^ 5 + 365914791936 * r ^ 11 * E ^ 4 + 281533612032 * r ^ 11 * E ^ 3 +
  111779315712 * r ^ 11 * E ^ 2 + 17629249536 * r ^ 11 * E + 743178240 * r ^ 10 * E ^ 7 +
  5496717312 * r ^ 10 * E ^ 6 + 16335396864 * r ^ 10 * E ^ 5 + 24909373440 * r ^ 10 * E ^ 4 +
  20509507584 * r ^ 10 * E ^ 3 + 8615559168 * r ^ 10 * E ^ 2 + 1433272320 * r ^ 10 * E

/-- The Hurwitz determinant `Δ₅` of `twoSB r E` (168 terms, all positive), in parts. -/
def twoBΔ₅ (r E : ℝ) : ℝ :=
  twoBΔ₅_0 r E + twoBΔ₅_1 r E + twoBΔ₅_2 r E + twoBΔ₅_3 r E + twoBΔ₅_4 r E + twoBΔ₅_5 r E

set_option maxHeartbeats 8000000 in
-- Laplace expansion of a symbolic `6 × 6` determinant
/-- The characteristic polynomial of `twoSB r E`. -/
theorem twoSB_charpoly (r E : ℝ) (lam : ℂ) :
    (lam • (1 : Matrix (Fin 6) (Fin 6) ℂ) - toComplex (twoSB r E)).det =
      lam ^ 6 + (twoBB1 r E : ℂ) * lam ^ 5 + (twoBB2 r E : ℂ) * lam ^ 4
        + (twoBB3 r E : ℂ) * lam ^ 3 + (twoBB4 r E : ℂ) * lam ^ 2 + (twoBB5 r E : ℂ) * lam
        + (twoBB6 r E : ℂ) := by
  simp [det_succ_row_zero, Fin.sum_univ_succ, twoSB, twoBB1, twoBB2, twoBB3, twoBB4, twoBB5,
    twoBB6, toComplex_apply, Matrix.one_apply, Fin.succAbove]
  ring

set_option maxHeartbeats 8000000 in
-- normalizing the degree-6 Hurwitz determinants of polynomial coefficients
/-- **`twoSB r E` is Hurwitz for `r, E > 0`, `r ≠ 1`.** -/
theorem twoSB_isHurwitz {r E : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) (hE : 0 < E) :
    IsHurwitz (twoSB r E) := by
  refine isHurwitz_of_charpoly6 (twoSB_charpoly r E) ?_ ?_ ?_ ?_ ?_ ?_
  · unfold twoBB1; positivity
  · unfold twoBB6
    have h1 : 0 < (r - 1) ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (sub_ne_zero.mpr hr1)))
    positivity
  · rw [show hurwitz6Δ₂ (twoBB1 r E) (twoBB2 r E) (twoBB3 r E) = twoBΔ₂ r E by
      unfold hurwitz6Δ₂ twoBB1 twoBB2 twoBB3 twoBΔ₂; ring]
    unfold twoBΔ₂; positivity
  · rw [show hurwitz6Δ₃ (twoBB1 r E) (twoBB2 r E) (twoBB3 r E) (twoBB4 r E) (twoBB5 r E)
        = twoBΔ₃ r E by
      unfold hurwitz6Δ₃ twoBB1 twoBB2 twoBB3 twoBB4 twoBB5 twoBΔ₃
       twoBΔ₃_0 twoBΔ₃_1; ring]
    unfold twoBΔ₃ twoBΔ₃_0 twoBΔ₃_1; positivity
  · rw [show hurwitz6Δ₄ (twoBB1 r E) (twoBB2 r E) (twoBB3 r E) (twoBB4 r E) (twoBB5 r E)
        (twoBB6 r E) = twoBΔ₄ r E by
      unfold hurwitz6Δ₄ twoBB1 twoBB2 twoBB3 twoBB4 twoBB5 twoBB6 twoBΔ₄
       twoBΔ₄_0 twoBΔ₄_1 twoBΔ₄_2 twoBΔ₄_3; ring]
    unfold twoBΔ₄ twoBΔ₄_0 twoBΔ₄_1 twoBΔ₄_2 twoBΔ₄_3; positivity
  · rw [show hurwitz6Δ₅ (twoBB1 r E) (twoBB2 r E) (twoBB3 r E) (twoBB4 r E) (twoBB5 r E)
        (twoBB6 r E) = twoBΔ₅ r E by
      unfold hurwitz6Δ₅ twoBB1 twoBB2 twoBB3 twoBB4 twoBB5 twoBB6 twoBΔ₅
       twoBΔ₅_0 twoBΔ₅_1 twoBΔ₅_2 twoBΔ₅_3 twoBΔ₅_4 twoBΔ₅_5; ring]
    unfold twoBΔ₅ twoBΔ₅_0 twoBΔ₅_1 twoBΔ₅_2 twoBΔ₅_3 twoBΔ₅_4 twoBΔ₅_5; positivity

/-- On the asymmetric branch, `r • twoR (twoBr c r) = twoSB r (c/(2 + 2r))`. -/
theorem twoR_twoBr_smul {c r : ℝ} (hr : 0 < r) :
    r • twoR (twoBr c r) = twoSB r (c / (2 + 2 * r)) := by
  have hr0 : r ≠ 0 := hr.ne'
  ext i j
  fin_cases i <;> fin_cases j <;> simp [twoR, twoSB, twoBr] <;> field_simp <;> ring

/-- **The asymmetric states are linearly stable within their class** (`r > 0`, `r ≠ 1`). -/
theorem twoBr_isHurwitz {c r : ℝ} (hc : 0 < c) (hr : 0 < r) (hr1 : r ≠ 1) :
    IsHurwitz (twoC * twoNet.massActionJacobian twoK (twoBr c r) * twoB) := by
  rw [two_restrict]
  apply isHurwitz_of_smul hr
  rw [twoR_twoBr_smul hr]
  exact twoSB_isHurwitz hr hr1 (by positivity)

/-- **Beyond the threshold the two asymmetric states are locally exponentially stable within
their class**, for all `c > 0`, `σ > 3 + 3c/2`. -/
theorem two_slice_outer_classStable {c σ r : ℝ} (hc : 0 < c) (hσ : 3 + 3 * c / 2 < σ)
    (hr : r = twoRp c σ ∨ r = twoRm c σ) :
    ∃ δ > 0, ∃ κ > 0, ∃ K > 0, ∀ (x : ℝ → Fin 9 → ℝ) (T : ℝ),
      twoNet.MassActionTrajectoryOn twoK x T → x 0 - twoBr c r ∈ twoNet.stoichSubspace →
        ‖x 0 - twoBr c r‖ < δ →
          ∀ t ∈ Ico 0 T,
            ‖x t - twoBr c r‖ ^ 2 ≤ K * Real.exp (-κ * t) * ‖x 0 - twoBr c r‖ ^ 2 := by
  obtain ⟨hm0, -, hm1, hp1, -, -⟩ := twoR_roots hσ
  obtain ⟨hslice, hpos, hr1⟩ : TwoSlice c σ (twoBr c r) ∧ 0 < r ∧ r ≠ 1 := by
    obtain ⟨-, hp, hm, -, -, -, -⟩ := two_slice_three hc hσ
    rcases hr with rfl | rfl
    · exact ⟨hp, by linarith, hp1.ne'⟩
    · exact ⟨hm, hm0, hm1.ne⟩
  exact twoNet.classLocallyExpStable_of_restrict hslice.1.2 (B := twoB) (C := twoC)
    (fun _ hu => two_proj hu) (twoBr_isHurwitz hc hpos hr1)

/-- **Bistability throughout the multistationary region of the slice.** For `c > 0` and
`σ > 3 + 3c/2`, every positive steady state with `E_tot = F_tot = c`, `S_tot = σ` is either one of
the two asymmetric states, whose restricted Jacobian is Hurwitz, or the symmetric state, whose
restricted Jacobian is not. -/
theorem two_slice_bistable {c σ : ℝ} (hc : 0 < c) (hσ : 3 + 3 * c / 2 < σ) {y : Fin 9 → ℝ}
    (hy : TwoSlice c σ y) :
    ((y = twoBr c (twoRp c σ) ∨ y = twoBr c (twoRm c σ)) ∧
        IsHurwitz (twoC * twoNet.massActionJacobian twoK y * twoB)) ∨
      (y = twoSym c σ ∧ ¬ IsHurwitz (twoC * twoNet.massActionJacobian twoK y * twoB)) := by
  obtain ⟨hm0, -, hm1, hp1, -, -⟩ := twoR_roots hσ
  obtain ⟨-, -, -, -, -, -, hall⟩ := two_slice_three hc hσ
  rcases hall y hy with rfl | rfl | rfl
  · exact Or.inr ⟨rfl, two_slice_sym_unstable hc hσ⟩
  · exact Or.inl ⟨Or.inl rfl, twoBr_isHurwitz hc (by linarith) hp1.ne'⟩
  · exact Or.inl ⟨Or.inr rfl, twoBr_isHurwitz hc hm0 hm1.ne⟩

end LeanTheory.CRN.Design
