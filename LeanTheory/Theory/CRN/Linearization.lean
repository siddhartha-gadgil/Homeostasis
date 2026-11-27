/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Kernel.Stability
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Topology.Order.Compact

/-!
# Linearized stability via a Lyapunov certificate (notes N-003, N-016)

**Theorem** (`lyapunov_local_exp_stable`). Let `F : ℝ^ι → ℝ^ι` vanish at `x⋆` and be
differentiable there with derivative `J`. If a matrix `P` gives a positive definite quadratic form
and `Jᵀ P + P J` a negative definite one, then `x⋆` is **locally exponentially stable**: there are
`δ, c, C > 0` such that every solution of `ẋ = F(x)` on `[0, T)` with `‖x(0) − x⋆‖ < δ` satisfies
`‖x(t) − x⋆‖² ≤ C e^{−ct} ‖x(0) − x⋆‖²` on `[0, T)`.

Only differentiability of `F` at `x⋆` is used (`F(x⋆ + e) = J e + o(‖e‖)`). The Lyapunov function
is `V(e) = eᵀ P e`: along solutions `V' = eᵀ (JᵀP + PJ) e + O(‖e‖ · o(‖e‖)) ≤ −c V` near `x⋆`,
and a first-exit-time argument keeps solutions in the region where this holds.

Preliminaries: `quad_lower` (a positive definite form is `≥ α ‖e‖²`, by compactness of the unit
sphere) and `quad_upper`, `dot_mulVec_le` (bounds by norms).

Scope: the hypothesis is a Lyapunov certificate (as produced by `Certificates/LyapunovCert`), not
the Hurwitz property itself; the converse Lyapunov theorem (Hurwitz ⇒ such `P` exists) is not
formalized. Existence of solutions is not asserted.
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN

open Matrix Set Filter Topology

variable {ι : Type*} [Fintype ι]

/-- The real quadratic form `eᵀ A e`. -/
def quad (A : Matrix ι ι ℝ) (e : ι → ℝ) : ℝ := e ⬝ᵥ (A *ᵥ e)

/-- Quadratic forms are homogeneous of degree two. -/
theorem quad_smul (A : Matrix ι ι ℝ) (c : ℝ) (e : ι → ℝ) : quad A (c • e) = c ^ 2 * quad A e := by
  simp [quad, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring

/-- Quadratic forms are continuous. -/
theorem continuous_quad (A : Matrix ι ι ℝ) : Continuous (quad A) := by
  unfold quad; fun_prop

/-- **Coercivity of a positive definite form**: `α ‖e‖² ≤ eᵀ A e` for some `α > 0`. -/
theorem quad_lower {A : Matrix ι ι ℝ} (hA : ∀ e, e ≠ 0 → 0 < quad A e) :
    ∃ α > 0, ∀ e, α * ‖e‖ ^ 2 ≤ quad A e := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · refine ⟨1, one_pos, fun e => ?_⟩
    have : e = 0 := Subsingleton.elim _ _
    simp [this, quad]
  · have hne : (Metric.sphere (0 : ι → ℝ) 1).Nonempty :=
      NormedSpace.sphere_nonempty.mpr zero_le_one
    obtain ⟨u, hu, hmin⟩ := (isCompact_sphere (0 : ι → ℝ) 1).exists_isMinOn hne
      (continuous_quad A).continuousOn
    have hu0 : u ≠ 0 := by
      intro h; rw [h] at hu; simp at hu
    refine ⟨quad A u, hA u hu0, fun e => ?_⟩
    rcases eq_or_ne e 0 with rfl | he
    · simp [quad]
    · have hn : 0 < ‖e‖ := norm_pos_iff.mpr he
      have hs : ‖e‖⁻¹ • e ∈ Metric.sphere (0 : ι → ℝ) 1 := by
        simp [norm_smul, hn.ne']
      have := hmin hs
      simp only [mem_ofPred_eq] at this
      rw [quad_smul] at this
      have h2 : (‖e‖⁻¹) ^ 2 * ‖e‖ ^ 2 = 1 := by field_simp
      have h3 := mul_le_mul_of_nonneg_left this (sq_nonneg ‖e‖)
      have h4 : ‖e‖ ^ 2 * ((‖e‖⁻¹) ^ 2 * quad A e) = quad A e := by
        rw [← mul_assoc, mul_comm (‖e‖ ^ 2), h2, one_mul]
      rw [h4] at h3
      linarith

/-- **Bound of a quadratic form**: `|eᵀ A e| ≤ K ‖e‖²` for some `K > 0`. -/
theorem quad_upper (A : Matrix ι ι ℝ) : ∃ K > 0, ∀ e, |quad A e| ≤ K * ‖e‖ ^ 2 := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · refine ⟨1, one_pos, fun e => ?_⟩
    have : e = 0 := Subsingleton.elim _ _
    simp [this, quad]
  · have hne : (Metric.sphere (0 : ι → ℝ) 1).Nonempty :=
      NormedSpace.sphere_nonempty.mpr zero_le_one
    obtain ⟨u, -, hmax⟩ := (isCompact_sphere (0 : ι → ℝ) 1).exists_isMaxOn hne
      (continuous_abs.comp (continuous_quad A)).continuousOn
    refine ⟨|quad A u| + 1, by positivity, fun e => ?_⟩
    rcases eq_or_ne e 0 with rfl | he
    · simp [quad]
    · have hn : 0 < ‖e‖ := norm_pos_iff.mpr he
      have hs : ‖e‖⁻¹ • e ∈ Metric.sphere (0 : ι → ℝ) 1 := by
        simp [norm_smul, hn.ne']
      have := hmax hs
      simp only [mem_ofPred_eq, Function.comp_apply] at this
      rw [quad_smul, abs_mul, abs_of_nonneg (sq_nonneg _)] at this
      have h2 : (‖e‖⁻¹) ^ 2 * ‖e‖ ^ 2 = 1 := by field_simp
      have hq : |quad A e| = ‖e‖ ^ 2 * ((‖e‖⁻¹) ^ 2 * |quad A e|) := by
        rw [← mul_assoc, mul_comm (‖e‖ ^ 2), h2, one_mul]
      rw [hq]
      nlinarith [sq_nonneg ‖e‖, abs_nonneg (quad A u)]

/-- **Bilinear bound**: `|u ⬝ (A v)| ≤ B ‖u‖ ‖v‖`. -/
theorem dot_mulVec_le (A : Matrix ι ι ℝ) :
    ∃ B > 0, ∀ u v : ι → ℝ, |u ⬝ᵥ (A *ᵥ v)| ≤ B * ‖u‖ * ‖v‖ := by
  classical
  let L := LinearMap.toContinuousLinearMap (Matrix.toLin' A)
  refine ⟨(Fintype.card ι + 1) * (‖L‖ + 1), by positivity, fun u v => ?_⟩
  have hAv : ‖A *ᵥ v‖ ≤ (‖L‖ + 1) * ‖v‖ := by
    have := L.le_opNorm v
    have hL : L v = A *ᵥ v := by simp [L]
    rw [hL] at this
    nlinarith [norm_nonneg v]
  calc |u ⬝ᵥ (A *ᵥ v)| ≤ ∑ i, |u i * (A *ᵥ v) i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, ‖u‖ * ‖A *ᵥ v‖ := Finset.sum_le_sum fun i _ => by
        rw [abs_mul]
        exact mul_le_mul (norm_le_pi_norm u i) (norm_le_pi_norm (A *ᵥ v) i) (abs_nonneg _)
          (norm_nonneg _)
    _ = Fintype.card ι * (‖u‖ * ‖A *ᵥ v‖) := by simp
    _ ≤ (Fintype.card ι + 1) * (‖u‖ * ((‖L‖ + 1) * ‖v‖)) := by
        gcongr
        linarith
    _ = (Fintype.card ι + 1) * (‖L‖ + 1) * ‖u‖ * ‖v‖ := by ring

/-- Derivative of a quadratic form along a curve: `(eᵀPe)' = e'ᵀ P e + eᵀ P e'`. -/
theorem hasDerivAt_quad (P : Matrix ι ι ℝ) {e : ℝ → ι → ℝ} {e' : ι → ℝ} {t : ℝ}
    (h : HasDerivAt e e' t) :
    HasDerivAt (fun s => quad P (e s)) (e' ⬝ᵥ (P *ᵥ e t) + e t ⬝ᵥ (P *ᵥ e')) t := by
  have hc : ∀ i, HasDerivAt (fun s => e s i) (e' i) t := hasDerivAt_pi.mp h
  have hPe : ∀ i, HasDerivAt (fun s => (P *ᵥ e s) i) ((P *ᵥ e') i) t := by
    intro i
    simp only [mulVec, dotProduct]
    exact HasDerivAt.fun_sum fun j _ => (hc j).const_mul (P i j)
  have := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => (hc i).mul (hPe i)
  simp only [quad, dotProduct]
  convert this using 1
  simp only [Finset.sum_add_distrib]

/-- `(J e) ⬝ w = e ⬝ (Jᵀ w)`. -/
theorem mulVec_dotProduct_eq (J : Matrix ι ι ℝ) (e w : ι → ℝ) :
    (J *ᵥ e) ⬝ᵥ w = e ⬝ᵥ (Jᵀ *ᵥ w) := by
  rw [dotProduct_mulVec, vecMul_transpose, dotProduct_comm]

/-- **Linearized stability via a Lyapunov certificate.** If `F x⋆ = 0`, `F` is differentiable at
`x⋆` with Jacobian `J`, `P` gives a positive definite form and `JᵀP + PJ` a negative definite one,
then `x⋆` is locally exponentially stable for `ẋ = F(x)`: solutions on `[0, T)` starting within `δ`
of `x⋆` satisfy `‖x(t) − x⋆‖² ≤ C e^{−ct} ‖x(0) − x⋆‖²`. -/
theorem lyapunov_local_exp_stable [DecidableEq ι] {F : (ι → ℝ) → (ι → ℝ)} {xs : ι → ℝ}
    {J P : Matrix ι ι ℝ}
    (hF : HasFDerivAt F (LinearMap.toContinuousLinearMap (Matrix.toLin' J)) xs)
    (h0 : F xs = 0) (hP : ∀ e, e ≠ 0 → 0 < quad P e)
    (hM : ∀ e, e ≠ 0 → quad (Jᵀ * P + P * J) e < 0) :
    ∃ δ > 0, ∃ c > 0, ∃ C > 0, ∀ (x : ℝ → ι → ℝ) (T : ℝ),
      (∀ t ∈ Ico 0 T, HasDerivWithinAt x (F (x t)) (Ico 0 T) t) → ‖x 0 - xs‖ < δ →
        ∀ t ∈ Ico 0 T, ‖x t - xs‖ ^ 2 ≤ C * Real.exp (-c * t) * ‖x 0 - xs‖ ^ 2 := by
  set M := Jᵀ * P + P * J with hMdef
  obtain ⟨α, hα, hlow⟩ := quad_lower hP
  obtain ⟨β, hβ, hneg⟩ := quad_lower (A := -M) fun e he => by
    have := hM e he
    simp only [quad, neg_mulVec, dotProduct_neg] at this ⊢
    linarith
  obtain ⟨K, hK, hup⟩ := quad_upper P
  obtain ⟨B, hB, hbil⟩ := dot_mulVec_le P
  -- the remainder `F(x⋆ + e) − J e` is small near `x⋆`
  set ε := β / (4 * B) with hε
  have hεpos : 0 < ε := by positivity
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.mp (hF.isLittleO.def hεpos)
  -- the key differential inequality near `x⋆`
  have hkey : ∀ y, ‖y - xs‖ < ρ →
      F y ⬝ᵥ (P *ᵥ (y - xs)) + (y - xs) ⬝ᵥ (P *ᵥ F y) ≤ -(β / (2 * K)) * quad P (y - xs) := by
    intro y hy
    set e := y - xs
    have hR := hball (by rwa [dist_eq_norm])
    simp only [h0, sub_zero] at hR
    set R := F y - J *ᵥ e with hRdef
    have hRe : ‖R‖ ≤ ε * ‖e‖ := by
      have : (LinearMap.toContinuousLinearMap (Matrix.toLin' J)) (y - xs) = J *ᵥ e := by simp [e]
      rw [this] at hR
      exact hR
    have hFy : F y = J *ᵥ e + R := by rw [hRdef]; abel
    have hsplit : F y ⬝ᵥ (P *ᵥ e) + e ⬝ᵥ (P *ᵥ F y) =
        quad M e + (R ⬝ᵥ (P *ᵥ e) + e ⬝ᵥ (P *ᵥ R)) := by
      rw [hFy, add_dotProduct, mulVec_add, dotProduct_add, mulVec_dotProduct_eq, quad, hMdef,
        add_mulVec, dotProduct_add, ← mulVec_mulVec, ← mulVec_mulVec]
      ring
    have h1 := hbil R e
    have h2 := hbil e R
    have hq := hneg e
    have hqM : quad (-M) e = -quad M e := by simp [quad, neg_mulVec, dotProduct_neg]
    rw [hqM] at hq
    have hVu := hup e
    have hb1 : R ⬝ᵥ (P *ᵥ e) ≤ B * (ε * ‖e‖) * ‖e‖ :=
      (le_abs_self _).trans (h1.trans (by gcongr))
    have hb2 : e ⬝ᵥ (P *ᵥ R) ≤ B * ‖e‖ * (ε * ‖e‖) :=
      (le_abs_self _).trans (h2.trans (by gcongr))
    have hBε : B * ε = β / 4 := by rw [hε]; field_simp
    have hV : β / (2 * K) * quad P e ≤ β / 2 * ‖e‖ ^ 2 := by
      have : quad P e ≤ K * ‖e‖ ^ 2 := (le_abs_self _).trans hVu
      calc β / (2 * K) * quad P e ≤ β / (2 * K) * (K * ‖e‖ ^ 2) := by gcongr
        _ = β / 2 * ‖e‖ ^ 2 := by field_simp
    rw [hsplit]
    nlinarith [sq_nonneg ‖e‖]
  set c := β / (2 * K) with hc
  have hcpos : 0 < c := by positivity
  set δ := ρ * min 1 (α / K) with hδ
  have hδpos : 0 < δ := by positivity
  refine ⟨δ, hδpos, c, hcpos, K / α, by positivity, fun x T hx hx0 => ?_⟩
  -- continuity and interior derivatives of the solution
  have hcont : ∀ t ∈ Ico 0 T, ContinuousOn x (Icc 0 t) := fun t ht s hs =>
    ((hx s ⟨hs.1, hs.2.trans_lt ht.2⟩).continuousWithinAt).mono
      (Icc_subset_Ico_right ht.2)
  have hderiv : ∀ s, 0 < s → s < T → HasDerivAt x (F (x s)) s := fun s hs hsT =>
    (hx s ⟨hs.le, hsT⟩).hasDerivAt (Ico_mem_nhds hs hsT)
  -- decay of `V` while the solution stays in the ball
  have hdecay : ∀ t ∈ Ico 0 T, (∀ s ∈ Ico 0 t, ‖x s - xs‖ < ρ) →
      quad P (x t - xs) ≤ Real.exp (-c * t) * quad P (x 0 - xs) := by
    intro t ht hin
    set W : ℝ → ℝ := fun s => Real.exp (c * s) * quad P (x s - xs)
    have hWc : ContinuousOn W (Icc 0 t) := by
      apply ContinuousOn.mul (by fun_prop)
      exact (continuous_quad P).comp_continuousOn ((hcont t ht).sub continuousOn_const)
    have hWd : ∀ s ∈ Ioo 0 t, HasDerivAt W (c * Real.exp (c * s) * quad P (x s - xs) +
        Real.exp (c * s) * (F (x s) ⬝ᵥ (P *ᵥ (x s - xs)) + (x s - xs) ⬝ᵥ (P *ᵥ F (x s)))) s := by
      intro s hs
      have he := (hderiv s hs.1 (hs.2.trans ht.2)).sub_const xs
      have hq := hasDerivAt_quad P he
      have hexp : HasDerivAt (fun s => Real.exp (c * s)) (Real.exp (c * s) * c) s := by
        simpa using ((hasDerivAt_id s).const_mul c).exp
      convert hexp.mul hq using 1
      ring
    have hanti : AntitoneOn W (Icc 0 t) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc 0 t) hWc
      · rw [interior_Icc]
        exact fun s hs => (hWd s hs).differentiableAt.differentiableWithinAt
      · rw [interior_Icc]
        intro s hs
        rw [(hWd s hs).deriv]
        have hk := hkey (x s) (hin s ⟨hs.1.le, hs.2⟩)
        have hexp := Real.exp_pos (c * s)
        nlinarith [mul_le_mul_of_nonneg_left hk hexp.le]
    have hWt := hanti ⟨le_rfl, ht.1⟩ ⟨ht.1, le_rfl⟩ ht.1
    simp only [W, mul_zero, Real.exp_zero, one_mul] at hWt
    have hexpt : Real.exp (-c * t) * Real.exp (c * t) = 1 := by
      rw [← Real.exp_add]; simp
    calc quad P (x t - xs) = Real.exp (-c * t) * (Real.exp (c * t) * quad P (x t - xs)) := by
          rw [← mul_assoc, hexpt, one_mul]
      _ ≤ Real.exp (-c * t) * quad P (x 0 - xs) := by gcongr
  -- the initial value of `V` is below the level `α ρ²`
  have hV0 : quad P (x 0 - xs) < α * ρ ^ 2 := by
    have hm : min 1 (α / K) ≤ 1 := min_le_left _ _
    have hm' : min 1 (α / K) ≤ α / K := min_le_right _ _
    have hm0 : 0 < min 1 (α / K) := by positivity
    have hn0 : ‖x 0 - xs‖ ^ 2 < δ ^ 2 := by
      have := norm_nonneg (x 0 - xs)
      nlinarith
    have hδ2 : δ ^ 2 ≤ ρ ^ 2 * (α / K) := by
      rw [hδ, mul_pow]
      gcongr
      nlinarith
    calc quad P (x 0 - xs) ≤ K * ‖x 0 - xs‖ ^ 2 := (le_abs_self _).trans (hup _)
      _ < K * δ ^ 2 := by gcongr
      _ ≤ K * (ρ ^ 2 * (α / K)) := by gcongr
      _ = α * ρ ^ 2 := by field_simp
  -- the solution never leaves the ball (first exit time)
  have hstay : ∀ t ∈ Ico 0 T, ∀ s ∈ Icc 0 t, ‖x s - xs‖ < ρ := by
    intro t ht
    by_contra hout
    simp only [not_forall, not_lt] at hout
    obtain ⟨s₀, hs₀, hs₀ρ⟩ := hout
    set A : Set ℝ := Icc 0 t ∩ (fun s => ‖x s - xs‖) ⁻¹' Ici ρ
    have hAc : IsClosed A := (continuous_norm.comp_continuousOn
      ((hcont t ht).sub continuousOn_const)).preimage_isClosed_of_isClosed isClosed_Icc
        isClosed_Ici
    have hbdd : BddBelow A := ⟨0, fun s hs => hs.1.1⟩
    have hτA : sInf A ∈ A := hAc.csInf_mem ⟨s₀, hs₀, hs₀ρ⟩ hbdd
    set τ := sInf A
    have hin : ∀ s ∈ Ico 0 τ, ‖x s - xs‖ < ρ := by
      intro s hs
      by_contra hns
      have : s ∈ A := ⟨⟨hs.1, hs.2.le.trans hτA.1.2⟩, not_lt.mp hns⟩
      exact absurd (csInf_le hbdd this) (not_le.mpr hs.2)
    have hτT : τ ∈ Ico 0 T := ⟨hτA.1.1, hτA.1.2.trans_lt ht.2⟩
    have hdec := hdecay τ hτT hin
    have hlowτ := hlow (x τ - xs)
    have hρτ : ρ ≤ ‖x τ - xs‖ := hτA.2
    have hexp : Real.exp (-c * τ) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hτA.1.1])
    have hV0nn : 0 ≤ quad P (x 0 - xs) := by
      have := hlow (x 0 - xs); nlinarith [sq_nonneg ‖x 0 - xs‖]
    have hsq : ρ ^ 2 ≤ ‖x τ - xs‖ ^ 2 := pow_le_pow_left₀ hρ.le hρτ 2
    have h1 : α * ρ ^ 2 ≤ α * ‖x τ - xs‖ ^ 2 := mul_le_mul_of_nonneg_left hsq hα.le
    have h2 := mul_le_mul_of_nonneg_right hexp hV0nn
    linarith
  -- conclusion
  intro t ht
  have hdec := hdecay t ht fun s hs => hstay t ht s ⟨hs.1, hs.2.le⟩
  have hlowt := hlow (x t - xs)
  have hup0 := (le_abs_self _).trans (hup (x 0 - xs))
  have hexp := Real.exp_pos (-c * t)
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hα]
  nlinarith [mul_le_mul_of_nonneg_left hup0 hexp.le]

/-- **No full-space Lyapunov certificate for a singular Jacobian**: if `J v = 0` with `v ≠ 0`,
then `vᵀ (JᵀP + PJ) v = 0`, so `JᵀP + PJ` is never negative definite. Networks with conservation
laws have singular Jacobians; for them `lyapunov_local_exp_stable` does not apply and a
class-relative version is needed. -/
theorem quad_lyapunov_eq_zero_of_mulVec_eq_zero {J P : Matrix ι ι ℝ} {v : ι → ℝ}
    (hJv : J *ᵥ v = 0) : quad (Jᵀ * P + P * J) v = 0 := by
  rw [quad, add_mulVec, dotProduct_add, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_dotProduct_eq,
    hJv]
  simp

/-- **Real `LᵀDL` positivity**: for invertible `L` and positive `d`, `eᵀ (Lᵀ D L) e > 0` for
`e ≠ 0`. -/
theorem quad_ldl_pos [DecidableEq ι] {L : Matrix ι ι ℝ} {d : ι → ℝ} (hd : ∀ i, 0 < d i)
    (hL : L.det ≠ 0) {e : ι → ℝ} (he : e ≠ 0) : 0 < quad (Lᵀ * diagonal d * L) e := by
  have hw : L *ᵥ e ≠ 0 := fun h0 => hL ((exists_mulVec_eq_zero_iff).mp ⟨e, he, h0⟩)
  have hq : quad (Lᵀ * diagonal d * L) e = ∑ i, d i * (L *ᵥ e) i ^ 2 := by
    rw [quad, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_dotProduct_eq]
    simp only [dotProduct, mulVec_diagonal]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hq]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
  exact lt_of_lt_of_le (mul_pos (hd i) (pow_pos (abs_pos.mpr hi) 2 |>.trans_eq (sq_abs _)))
    (Finset.single_le_sum (f := fun j => d j * (L *ᵥ e) j ^ 2)
      (fun j _ => mul_nonneg (hd j).le (sq_nonneg _)) (Finset.mem_univ i))

/-- **Linearized stability for mass-action networks.** If `x⋆` is a steady state and a Lyapunov
certificate `P = L₁ᵀ D₁ L₁`, `JᵀP + PJ = −L₂ᵀ D₂ L₂` exists for the Jacobian at `x⋆`, then `x⋆` is
locally exponentially stable for finite-horizon mass-action trajectories. -/
theorem ReactionNetwork.locallyExpStable_of_ldl {C R : Type*} [Fintype R] [DecidableEq ι]
    (N : ReactionNetwork ι C R) {k : R → ℝ} {xs : ι → ℝ} (hxs : N.massActionField k xs = 0)
    {L₁ L₂ : Matrix ι ι ℝ} {d₁ d₂ : ι → ℝ} (hd₁ : ∀ i, 0 < d₁ i) (hd₂ : ∀ i, 0 < d₂ i)
    (hL₁ : L₁.det ≠ 0) (hL₂ : L₂.det ≠ 0)
    (hid : (N.massActionJacobian k xs)ᵀ * (L₁ᵀ * diagonal d₁ * L₁) +
      (L₁ᵀ * diagonal d₁ * L₁) * N.massActionJacobian k xs = -(L₂ᵀ * diagonal d₂ * L₂)) :
    ∃ δ > 0, ∃ c > 0, ∃ C > 0, ∀ (x : ℝ → ι → ℝ) (T : ℝ), N.MassActionTrajectoryOn k x T →
      ‖x 0 - xs‖ < δ →
        ∀ t ∈ Ico 0 T, ‖x t - xs‖ ^ 2 ≤ C * Real.exp (-c * t) * ‖x 0 - xs‖ ^ 2 := by
  obtain ⟨δ, hδ, c, hc, C, hC, h⟩ := lyapunov_local_exp_stable
    (N.hasFDerivAt_massActionField k xs) hxs (fun e he => quad_ldl_pos hd₁ hL₁ he)
    (fun e he => by
      rw [hid]
      have := quad_ldl_pos hd₂ hL₂ he
      simp only [quad, neg_mulVec, dotProduct_neg] at this ⊢
      linarith)
  exact ⟨δ, hδ, c, hc, C, hC, fun x T hx => h x T hx.hasDerivWithinAt⟩

end LeanTheory.CRN
