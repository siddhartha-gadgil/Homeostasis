/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.CRN.ConverseLyapunovPD

/-!
# Linearized stability relative to a compatibility class (notes N-003, N-002)

Networks with conservation laws have singular Jacobians, so `hurwitz_local_exp_stable` never
applies to them (`Sanity.isoNet_no_lyapunov`). The relevant notion is stability **within the
stoichiometric compatibility class**. We pass to coordinates on the stoichiometric subspace `S`:
a matrix `B : ι × κ` whose columns lie in `S` and a left inverse `C : κ × ι` (`C B = I`) with
`B C u = u` for `u ∈ S` (coordinates of `S`). The **restricted Jacobian** is `C J B`.

* `isHurwitz_restrict`: if `J` maps into `S` and is Hurwitz on `S` (`IsHurwitzOn J S`), then the
  restricted Jacobian `C J B` is Hurwitz.
* `class_local_exp_stable` (abstract): if `F(x⋆) = 0`, `F` is differentiable at `x⋆` with
  Jacobian `J`, and `C J B` is Hurwitz, then solutions **staying in `x⋆ + S`** and starting within
  `δ` converge exponentially: `‖x(t) − x⋆‖² ≤ K e^{−ct} ‖x(0) − x⋆‖²`.
* `ReactionNetwork.classLocallyExpStable`: for mass action, the Jacobian maps into `S`
  (`massActionJacobian_mulVec_mem`) and trajectories stay in their class, so linear stability
  relative to the class (`IsLinearlyStable`) gives **local exponential stability within the
  compatibility class**.
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN

open Matrix Set

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq ι] [DecidableEq κ] in
/-- Rectangular matrices are bounded: `‖M v‖ ≤ K ‖v‖`. -/
theorem mulVec_norm_le (M : Matrix ι κ ℝ) : ∃ K > 0, ∀ v : κ → ℝ, ‖M *ᵥ v‖ ≤ K * ‖v‖ := by
  classical
  let L := LinearMap.toContinuousLinearMap (Matrix.toLin' M)
  refine ⟨‖L‖ + 1, by positivity, fun v => ?_⟩
  have h := L.le_opNorm v
  have hL : L v = M *ᵥ v := by simp [L]
  rw [hL] at h
  nlinarith [norm_nonneg v]

/-- The complexification of a rectangular real matrix. -/
def cmap (M : Matrix ι κ ℝ) : Matrix ι κ ℂ := M.map Complex.ofRealHom

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
/-- Real part of a complexified product. -/
theorem re_cmap_mulVec (M : Matrix ι κ ℝ) (w : κ → ℂ) (i : ι) :
    ((cmap M *ᵥ w) i).re = (M *ᵥ fun j => (w j).re) i := by
  simp [cmap, mulVec, dotProduct, Complex.re_sum]

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
/-- Imaginary part of a complexified product. -/
theorem im_cmap_mulVec (M : Matrix ι κ ℝ) (w : κ → ℂ) (i : ι) :
    ((cmap M *ᵥ w) i).im = (M *ᵥ fun j => (w j).im) i := by
  simp [cmap, mulVec, dotProduct, Complex.im_sum]

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
/-- Complexification is multiplicative for rectangular matrices. -/
theorem cmap_mul {ν : Type*} (M : Matrix ι κ ℝ) (N : Matrix κ ν ℝ) :
    cmap (M * N) = cmap M * cmap N :=
  Matrix.map_mul

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
/-- For square matrices `cmap` is `toComplex`. -/
theorem cmap_eq_toComplex (M : Matrix ι ι ℝ) : cmap M = toComplex M := rfl

omit [DecidableEq ι] in
/-- **Hurwitz on `S` ⇒ the restricted Jacobian is Hurwitz.** -/
theorem isHurwitz_restrict {J : Matrix ι ι ℝ} {S : Submodule ℝ (ι → ℝ)} {B : Matrix ι κ ℝ}
    {C : Matrix κ ι ℝ} (hJ : IsHurwitzOn J S) (hJS : ∀ u, J *ᵥ u ∈ S) (hBS : ∀ y, B *ᵥ y ∈ S)
    (hCB : C * B = 1) (hproj : ∀ u ∈ S, B *ᵥ (C *ᵥ u) = u) : IsHurwitz (C * J * B) := by
  intro lam w hw he
  set v := cmap B *ᵥ w with hv
  -- `v` is a nonzero vector in the complexification of `S`
  have hCv : cmap C *ᵥ v = w := by
    rw [hv, mulVec_mulVec, ← cmap_mul, hCB]
    simp [cmap, Matrix.map_one, one_mulVec]
  have hv0 : v ≠ 0 := fun h => hw (by rw [← hCv, h, mulVec_zero])
  have hvS : InComplexification S v := by
    constructor
    · have : (fun i => (v i).re) = B *ᵥ fun j => (w j).re := by
        funext i; exact re_cmap_mulVec B w i
      rw [this]; exact hBS _
    · have : (fun i => (v i).im) = B *ᵥ fun j => (w j).im := by
        funext i; exact im_cmap_mulVec B w i
      rw [this]; exact hBS _
  -- `J v` lies in the complexification of `S`, hence `B C (J v) = J v`
  set Jv := cmap J *ᵥ v
  have hproj_c : cmap B *ᵥ (cmap C *ᵥ Jv) = Jv := by
    have hre : (fun i => (Jv i).re) ∈ S := by
      have : (fun i => (Jv i).re) = J *ᵥ fun j => (v j).re := by
        funext i; exact re_cmap_mulVec J v i
      rw [this]; exact hJS _
    have him : (fun i => (Jv i).im) ∈ S := by
      have : (fun i => (Jv i).im) = J *ᵥ fun j => (v j).im := by
        funext i; exact im_cmap_mulVec J v i
      rw [this]; exact hJS _
    funext i
    apply Complex.ext
    · rw [re_cmap_mulVec, show (fun j => ((cmap C *ᵥ Jv) j).re) = C *ᵥ fun j => (Jv j).re by
        funext j; exact re_cmap_mulVec C Jv j]
      exact congrFun (hproj _ hre) i
    · rw [im_cmap_mulVec, show (fun j => ((cmap C *ᵥ Jv) j).im) = C *ᵥ fun j => (Jv j).im by
        funext j; exact im_cmap_mulVec C Jv j]
      exact congrFun (hproj _ him) i
  have hCJv : cmap C *ᵥ Jv = lam • w := by
    rw [← he, ← cmap_eq_toComplex, cmap_mul, cmap_mul, ← mulVec_mulVec, ← mulVec_mulVec]
  have heig : toComplex J *ᵥ v = lam • v := by
    rw [← cmap_eq_toComplex]
    change Jv = lam • v
    rw [← hproj_c, hCJv, mulVec_smul]
  exact hJ lam v hv0 hvS heig

omit [DecidableEq κ] in
/-- **Local exponential stability within an invariant affine subspace.** If `F x⋆ = 0`, `F` is
differentiable at `x⋆` with Jacobian `J`, and the restricted Jacobian `C J B` is Hurwitz (with
`B C u = u` on `S`), then solutions staying in `x⋆ + S` and starting within `δ`
converge exponentially. -/
theorem class_local_exp_stable {F : (ι → ℝ) → (ι → ℝ)} {xs : ι → ℝ} {J : Matrix ι ι ℝ}
    {S : Submodule ℝ (ι → ℝ)} {B : Matrix ι κ ℝ} {C : Matrix κ ι ℝ}
    (hF : HasFDerivAt F (LinearMap.toContinuousLinearMap (Matrix.toLin' J)) xs) (h0 : F xs = 0)
    (hJ : IsHurwitz (C * J * B)) (hproj : ∀ u ∈ S, B *ᵥ (C *ᵥ u) = u) :
    ∃ δ > 0, ∃ c > 0, ∃ K > 0, ∀ (x : ℝ → ι → ℝ) (T : ℝ),
      (∀ t ∈ Ico 0 T, HasDerivWithinAt x (F (x t)) (Ico 0 T) t) →
      (∀ t ∈ Ico 0 T, x t - xs ∈ S) → ‖x 0 - xs‖ < δ →
        ∀ t ∈ Ico 0 T, ‖x t - xs‖ ^ 2 ≤ K * Real.exp (-c * t) * ‖x 0 - xs‖ ^ 2 := by
  classical
  -- the reduced field on `S`-coordinates
  set G : (κ → ℝ) → (κ → ℝ) := fun y => C *ᵥ F (xs + B *ᵥ y) with hG
  have hG0 : G 0 = 0 := by simp [hG, h0]
  have hGd : HasFDerivAt G (LinearMap.toContinuousLinearMap (Matrix.toLin' (C * J * B))) 0 := by
    let Bc := LinearMap.toContinuousLinearMap (Matrix.toLin' B)
    let Cc := LinearMap.toContinuousLinearMap (Matrix.toLin' C)
    have hφ : HasFDerivAt (fun y : κ → ℝ => xs + B *ᵥ y) Bc 0 := by
      have := Bc.hasFDerivAt.const_add xs (x := 0)
      simpa [Bc] using this
    have hFx : HasFDerivAt F (LinearMap.toContinuousLinearMap (Matrix.toLin' J))
        (xs + B *ᵥ (0 : κ → ℝ)) := by simpa using hF
    have hc := Cc.hasFDerivAt.comp (0 : κ → ℝ) (hFx.comp (0 : κ → ℝ) hφ)
    convert hc using 1
    · ext1 y
      rfl
    · ext1 y
      simp [Bc, Cc, mulVec_mulVec, Matrix.mul_assoc]
  obtain ⟨δ, hδ, c, hc, K₀, hK₀, h⟩ := hurwitz_local_exp_stable hGd hG0 hJ
  obtain ⟨KB, hKB, hBn⟩ := mulVec_norm_le B
  obtain ⟨KC, hKC, hCn⟩ := mulVec_norm_le C
  refine ⟨δ / KC, by positivity, c, hc, KB ^ 2 * K₀ * KC ^ 2, by positivity,
    fun x T hx hstay hx0 t ht => ?_⟩
  set y : ℝ → κ → ℝ := fun s => C *ᵥ (x s - xs) with hy
  have hxy : ∀ s ∈ Ico 0 T, x s = xs + B *ᵥ y s := by
    intro s hs
    rw [hy, hproj _ (hstay s hs)]
    abel
  have hyd : ∀ s ∈ Ico 0 T, HasDerivWithinAt y (G (y s)) (Ico 0 T) s := by
    intro s hs
    have hd := (hx s hs).sub_const xs
    have := (LinearMap.toContinuousLinearMap (Matrix.toLin' C)).hasFDerivAt.comp_hasDerivWithinAt
      s hd
    have hyf : y = fun s => (LinearMap.toContinuousLinearMap (Matrix.toLin' C)) (x s - xs) := by
      funext s; simp [hy]
    have hval : G (y s) = (LinearMap.toContinuousLinearMap (Matrix.toLin' C)) (F (x s)) := by
      simp only [hG, ← hxy s hs]; simp
    rw [hval, hyf]
    exact this
  have hy0 : ‖y 0 - 0‖ < δ := by
    rw [sub_zero]
    calc ‖y 0‖ ≤ KC * ‖x 0 - xs‖ := hCn _
      _ < KC * (δ / KC) := by gcongr
      _ = δ := by field_simp
  have hyt := h y T hyd hy0 t ht
  rw [sub_zero, sub_zero] at hyt
  have hxt : ‖x t - xs‖ ≤ KB * ‖y t‖ := by
    rw [hxy t ht, add_sub_cancel_left]; exact hBn _
  have hy0' : ‖y 0‖ ≤ KC * ‖x 0 - xs‖ := hCn _
  have hexp := Real.exp_pos (-c * t)
  calc ‖x t - xs‖ ^ 2 ≤ (KB * ‖y t‖) ^ 2 := by gcongr
    _ = KB ^ 2 * ‖y t‖ ^ 2 := by ring
    _ ≤ KB ^ 2 * (K₀ * Real.exp (-c * t) * ‖y 0‖ ^ 2) := by gcongr
    _ ≤ KB ^ 2 * (K₀ * Real.exp (-c * t) * (KC * ‖x 0 - xs‖) ^ 2) := by gcongr
    _ = KB ^ 2 * K₀ * KC ^ 2 * Real.exp (-c * t) * ‖x 0 - xs‖ ^ 2 := by ring

/-! ### Mass-action networks -/

namespace ReactionNetwork

variable {C' R : Type*} [Fintype R]

/-- The mass-action Jacobian maps into the stoichiometric subspace. -/
theorem massActionJacobian_mulVec_mem (N : ReactionNetwork ι C' R) (k : R → ℝ) (x u : ι → ℝ) :
    N.massActionJacobian k x *ᵥ u ∈ N.stoichSubspace := by
  have h : N.massActionJacobian k x *ᵥ u = ∑ r, (∑ j, k r * (N.complex (N.src r) j : ℝ) *
      monomial (Function.update (N.complex (N.src r)) j (N.complex (N.src r) j - 1)) x * u j) •
        N.reactionVector r := by
    funext i
    simp only [mulVec, dotProduct, massActionJacobian, of_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [h]
  exact Submodule.sum_mem _ fun r _ =>
    Submodule.smul_mem _ _ (N.reactionVector_mem_stoichSubspace r)

omit [DecidableEq κ] in
/-- **Local exponential stability within the compatibility class** (restricted-Jacobian form): if
`x⋆` is a steady state and the restricted Jacobian `C J B` is Hurwitz, trajectories in the
compatibility class of `x⋆` starting within `δ` converge exponentially to `x⋆`. -/
theorem classLocallyExpStable_of_restrict (N : ReactionNetwork ι C' R) {k : R → ℝ}
    {xs : ι → ℝ} (hxs : N.massActionField k xs = 0) {B : Matrix ι κ ℝ} {C : Matrix κ ι ℝ}
    (hproj : ∀ u ∈ N.stoichSubspace, B *ᵥ (C *ᵥ u) = u)
    (hJ : IsHurwitz (C * N.massActionJacobian k xs * B)) :
    ∃ δ > 0, ∃ c > 0, ∃ K > 0, ∀ (x : ℝ → ι → ℝ) (T : ℝ), N.MassActionTrajectoryOn k x T →
      x 0 - xs ∈ N.stoichSubspace → ‖x 0 - xs‖ < δ →
        ∀ t ∈ Ico 0 T, ‖x t - xs‖ ^ 2 ≤ K * Real.exp (-c * t) * ‖x 0 - xs‖ ^ 2 := by
  obtain ⟨δ, hδ, c, hc, K, hK, h⟩ :=
    class_local_exp_stable (N.hasFDerivAt_massActionField k xs) hxs hJ hproj
  refine ⟨δ, hδ, c, hc, K, hK, fun x T hx hx0 => h x T hx.hasDerivWithinAt fun t ht => ?_⟩
  have := hx.sub_mem_stoichSubspace ht
  rw [show x t - xs = (x t - x 0) + (x 0 - xs) by abel]
  exact N.stoichSubspace.add_mem this hx0

/-- **Linear stability relative to the class ⇒ local exponential stability within the class.**
Given coordinates `B, C` of the stoichiometric subspace (`C B = I`, columns of `B` in `S`,
`B C u = u` on `S`), a linearly stable steady state (`IsLinearlyStable`) attracts, exponentially,
every trajectory of its compatibility class that starts close enough. -/
theorem classLocallyExpStable (N : ReactionNetwork ι C' R) {k : R → ℝ} {xs : ι → ℝ}
    (hst : N.IsLinearlyStable k xs) {B : Matrix ι κ ℝ} {C : Matrix κ ι ℝ}
    (hBS : ∀ y, B *ᵥ y ∈ N.stoichSubspace) (hCB : C * B = 1)
    (hproj : ∀ u ∈ N.stoichSubspace, B *ᵥ (C *ᵥ u) = u) :
    ∃ δ > 0, ∃ c > 0, ∃ K > 0, ∀ (x : ℝ → ι → ℝ) (T : ℝ), N.MassActionTrajectoryOn k x T →
      x 0 - xs ∈ N.stoichSubspace → ‖x 0 - xs‖ < δ →
        ∀ t ∈ Ico 0 T, ‖x t - xs‖ ^ 2 ≤ K * Real.exp (-c * t) * ‖x 0 - xs‖ ^ 2 :=
  N.classLocallyExpStable_of_restrict hst.1.2 hproj
    (isHurwitz_restrict hst.2 (N.massActionJacobian_mulVec_mem k xs) hBS hCB hproj)

end ReactionNetwork

end LeanTheory.CRN
