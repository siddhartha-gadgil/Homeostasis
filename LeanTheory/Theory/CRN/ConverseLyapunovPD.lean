/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.CRN.ConverseLyapunov
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Analysis.Normed.Operator.Banach

/-!
# The converse Lyapunov theorem (notes N-003, N-016)

**Theorem** (`converse_lyapunov`). If `J` is Hurwitz, there is a symmetric positive definite `P`
with `JᵀP + PJ = −I`.

Proof by homotopy. `J_t = (1 − t) J − t I` is Hurwitz for `t ∈ [0, 1]` (`isHurwitz_homotopy`),
so its Lyapunov operator `L_t` is invertible and `P_t = L_t⁻¹(−I)` is the unique, symmetric,
nonsingular Lyapunov solution (`ConverseLyapunov`). `t ↦ L_t` is affine and inversion is
continuous at units, so `t ↦ P_t` is continuous on `[0, 1]`; `P_1 = I/2` is positive definite. If
`P_0` were not, let `s` be the largest `t` at which `vᵀP_t v ≤ 0` for some unit vector `v`
(compactness); then `P_s` is positive semidefinite (limit from the right) with `vᵀP_s v = 0`, so
`P_s v = 0` (`mulVec_eq_zero_of_psd`), contradicting nonsingularity.

**Corollary** (`hurwitz_local_exp_stable`): an equilibrium of a `C¹` field (differentiable at the
point) with Hurwitz Jacobian is locally exponentially stable — the principle of linearized
stability, now without a separately supplied certificate.
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN

open Matrix Set Filter Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The homotopy stays Hurwitz -/

/-- The homotopy `J_t = (1 − t) J − t I` from `J` to `−I`. -/
def homotopyJ (J : Matrix ι ι ℝ) (t : ℝ) : Matrix ι ι ℝ := (1 - t) • J - t • (1 : Matrix ι ι ℝ)

omit [Fintype ι] in
/-- The complexified homotopy. -/
theorem toComplex_homotopyJ (J : Matrix ι ι ℝ) (t : ℝ) :
    toComplex (homotopyJ J t) = ((1 - t : ℝ) : ℂ) • toComplex J - (t : ℂ) • (1 : Matrix ι ι ℂ) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [toComplex_apply, homotopyJ]
  · simp [toComplex_apply, homotopyJ, Matrix.one_apply_ne h]

/-- **The homotopy stays Hurwitz** on `[0, 1]`. -/
theorem isHurwitz_homotopy {J : Matrix ι ι ℝ} (hJ : IsHurwitz J) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : IsHurwitz (homotopyJ J t) := by
  intro lam v hv he
  rw [toComplex_homotopyJ, sub_mulVec, smul_mulVec, smul_mulVec, one_mulVec] at he
  rcases eq_or_lt_of_le ht1 with h1 | h1
  · subst h1
    have : (lam + 1) • v = 0 := by
      simp only [sub_self, Complex.ofReal_zero, zero_smul, zero_sub, Complex.ofReal_one,
        one_smul] at he
      rw [add_smul, ← he, one_smul, neg_add_cancel]
    rcases smul_eq_zero.mp this with h | h
    · have : lam = -1 := by linear_combination h
      rw [this]; norm_num
    · exact absurd h hv
  · have hpos : (0 : ℝ) < 1 - t := by linarith
    have hne : ((1 - t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    have heig : toComplex J *ᵥ v = ((lam + t) / ((1 - t : ℝ) : ℂ)) • v := by
      have h2 : ((1 - t : ℝ) : ℂ) • (toComplex J *ᵥ v) = (lam + t) • v := by
        rw [add_smul, ← he]; abel
      rw [div_eq_inv_mul, mul_smul, ← h2, smul_smul, inv_mul_cancel₀ hne, one_smul]
    have := hJ _ v hv heig
    rw [Complex.div_ofReal_re] at this
    have h3 : (lam + t).re < 0 := by
      by_contra h; push Not at h; exact absurd this (not_lt.mpr (div_nonneg h hpos.le))
    simp at h3
    linarith

/-! ### Positive semidefinite forms -/

omit [DecidableEq ι] in
/-- **Kernel of a semidefinite form**: if `P` is symmetric, `wᵀ P w ≥ 0` for all `w`, and
`vᵀ P v = 0`, then `P v = 0`. -/
theorem mulVec_eq_zero_of_psd {P : Matrix ι ι ℝ} (hsym : Pᵀ = P) (hpsd : ∀ w, 0 ≤ quad P w)
    {v : ι → ℝ} (hv : quad P v = 0) : P *ᵥ v = 0 := by
  set w := P *ᵥ v
  have hexp : ∀ s : ℝ, quad P (v + s • w) = 2 * s * (w ⬝ᵥ w) + s ^ 2 * quad P w := by
    intro s
    have hsw : v ⬝ᵥ (P *ᵥ w) = w ⬝ᵥ w := by
      rw [dotProduct_mulVec, ← mulVec_transpose, hsym, dotProduct_comm]
    simp only [quad, mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
      smul_dotProduct, smul_eq_mul] at hv ⊢
    rw [hv, hsw]
    ring
  have hww : w ⬝ᵥ w = 0 := by
    set a := w ⬝ᵥ w
    set b := quad P w
    have hb := hpsd w
    have h := hpsd (v + (-(a / (b + 1))) • w)
    rw [hexp] at h
    have hb1 : 0 < b + 1 := by linarith
    have ha : 0 ≤ a := Finset.sum_nonneg fun i _ => mul_self_nonneg (w i)
    field_simp at h
    nlinarith
  exact dotProduct_self_eq_zero.mp hww

/-! ### Continuity of the Lyapunov solution along the homotopy -/

section Continuity

/-- The Lyapunov operator on the plain function space `ι → ι → ℝ` (sup norm). -/
def lyapLin (J : Matrix ι ι ℝ) : (ι → ι → ℝ) →ₗ[ℝ] (ι → ι → ℝ) where
  toFun X := Jᵀ * Matrix.of X + Matrix.of X * J
  map_add' X Y := by
    change Jᵀ * Matrix.of (X + Y) + Matrix.of (X + Y) * J =
      (Jᵀ * Matrix.of X + Matrix.of X * J) + (Jᵀ * Matrix.of Y + Matrix.of Y * J)
    rw [← Matrix.of_add_of, Matrix.mul_add, Matrix.add_mul]
    abel
  map_smul' c X := by
    change Jᵀ * Matrix.of (c • X) + Matrix.of (c • X) * J = c • (Jᵀ * Matrix.of X + Matrix.of X * J)
    rw [← Matrix.smul_of, Matrix.mul_smul, Matrix.smul_mul, smul_add]

/-- The Lyapunov operator as a continuous linear map on `ι → ι → ℝ`. -/
def lyapCLM (J : Matrix ι ι ℝ) : (ι → ι → ℝ) →L[ℝ] (ι → ι → ℝ) :=
  LinearMap.toContinuousLinearMap (lyapLin J)

omit [DecidableEq ι] in
/-- Evaluation of the Lyapunov operator. -/
theorem lyapCLM_apply (J : Matrix ι ι ℝ) (X : ι → ι → ℝ) :
    lyapCLM J X = Jᵀ * Matrix.of X + Matrix.of X * J := rfl

/-- Along the homotopy the Lyapunov operator is affine: `L_t = (1 − t) L₀ − 2t · id`. -/
theorem lyapCLM_homotopy (J : Matrix ι ι ℝ) (t : ℝ) :
    lyapCLM (homotopyJ J t) = (1 - t) • lyapCLM J - (2 * t) • ContinuousLinearMap.id ℝ _ := by
  ext1 X
  funext i k
  change (lyapCLM (homotopyJ J t) X) i k = (1 - t) * (lyapCLM J X) i k - 2 * t * X i k
  rw [lyapCLM_apply, lyapCLM_apply]
  simp only [homotopyJ, transpose_sub, transpose_smul, transpose_one, Matrix.sub_mul,
    Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
    Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]
  ring

/-- `t ↦ L_t` is continuous. -/
theorem continuous_lyapCLM_homotopy (J : Matrix ι ι ℝ) :
    Continuous fun t => lyapCLM (homotopyJ J t) := by
  simp_rw [lyapCLM_homotopy]
  fun_prop

omit [DecidableEq ι] in
/-- The Lyapunov operator of a Hurwitz matrix is a unit. -/
theorem isUnit_lyapCLM {J : Matrix ι ι ℝ} (hJ : IsHurwitz J) : IsUnit (lyapCLM J) := by
  classical
  have hinj : Function.Injective (lyapLin J) := by
    intro X Y h
    have := lyapOp_injective hJ (a₁ := Matrix.of X) (a₂ := Matrix.of Y) h
    exact Matrix.of.injective this
  exact ContinuousLinearMap.isUnit_iff_bijective.mpr
    ⟨hinj, (LinearMap.injective_iff_surjective (f := lyapLin J)).mp hinj⟩

/-- The Lyapunov solution `L⁻¹(−I)` (junk value when `L` is not invertible). -/
def lyapSol (J : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  Matrix.of (Ring.inverse (lyapCLM J) (fun i k => (-1 : Matrix ι ι ℝ) i k))

/-- For Hurwitz `J`, `lyapSol J` solves `JᵀP + PJ = −I`. -/
theorem lyapSol_spec {J : Matrix ι ι ℝ} (hJ : IsHurwitz J) :
    Jᵀ * lyapSol J + lyapSol J * J = -1 := by
  have hu := isUnit_lyapCLM hJ
  have h : lyapCLM J (Ring.inverse (lyapCLM J) (fun i k => (-1 : Matrix ι ι ℝ) i k)) =
      fun i k => (-1 : Matrix ι ι ℝ) i k := by
    have h1 := congrArg (fun f : (ι → ι → ℝ) →L[ℝ] (ι → ι → ℝ) =>
      f (fun i k => (-1 : Matrix ι ι ℝ) i k)) (Ring.mul_inverse_cancel _ hu)
    exact h1
  exact h

/-- **Continuity of the Lyapunov solution along the homotopy** (entrywise). -/
theorem continuousOn_lyapSol_entry {J : Matrix ι ι ℝ} (hJ : IsHurwitz J) (i k : ι) :
    ContinuousOn (fun t => lyapSol (homotopyJ J t) i k) (Icc 0 1) := by
  intro t ht
  apply ContinuousAt.continuousWithinAt
  have hu := isUnit_lyapCLM (isHurwitz_homotopy hJ ht.1 ht.2)
  have hinv : ContinuousAt Ring.inverse (lyapCLM (homotopyJ J t)) := by
    have := NormedRing.inverse_continuousAt hu.unit
    rwa [hu.unit_spec] at this
  have hcomp : ContinuousAt (fun s => Ring.inverse (lyapCLM (homotopyJ J s))) t :=
    hinv.comp (f := fun s => lyapCLM (homotopyJ J s)) (continuous_lyapCLM_homotopy J).continuousAt
  have happ := hcomp.clm_apply (continuousAt_const (y := fun i k => (-1 : Matrix ι ι ℝ) i k))
  exact ((continuous_apply k).comp (continuous_apply i)).continuousAt.comp happ

end Continuity

/-! ### Positive definiteness -/

/-- **The converse Lyapunov theorem.** If `J` is Hurwitz, there is a symmetric positive definite
`P` with `JᵀP + PJ = −I`. -/
theorem converse_lyapunov {J : Matrix ι ι ℝ} (hJ : IsHurwitz J) :
    ∃ P : Matrix ι ι ℝ, Jᵀ * P + P * J = -1 ∧ Pᵀ = P ∧ ∀ v : ι → ℝ, v ≠ 0 → 0 < quad P v := by
  set Pt : ℝ → Matrix ι ι ℝ := fun t => lyapSol (homotopyJ J t) with hPt
  -- symmetry and nonsingularity along the homotopy
  have hprop : ∀ t ∈ Icc (0 : ℝ) 1, (Pt t)ᵀ = Pt t ∧ ∀ v : ι → ℝ, v ≠ 0 → Pt t *ᵥ v ≠ 0 := by
    intro t ht
    have hJt := isHurwitz_homotopy hJ ht.1 ht.2
    obtain ⟨P', -, hs, hn, hu⟩ := exists_lyapunov_solution hJt
    have : Pt t = P' := hu _ (lyapSol_spec hJt)
    rw [this]
    exact ⟨hs, hn⟩
  -- positivity at `t = 1`, where `J₁ = −I` and `P₁ = I/2`
  have hpos1 : ∀ v : ι → ℝ, v ≠ 0 → 0 < quad (Pt 1) v := by
    intro v hv
    have hJ1 : homotopyJ J 1 = -1 := by simp [homotopyJ]
    have hH : IsHurwitz (-1 : Matrix ι ι ℝ) := by
      rw [← hJ1]; exact isHurwitz_homotopy hJ zero_le_one le_rfl
    have h1 := lyapSol_spec hH
    simp only [transpose_neg, transpose_one, Matrix.neg_mul, Matrix.mul_neg, Matrix.one_mul,
      Matrix.mul_one] at h1
    have hP1 : Pt 1 = lyapSol (-1) := by simp [hPt, hJ1]
    have h2 : (2 : ℝ) • Pt 1 = 1 := by
      rw [hP1, two_smul]
      have := congrArg Neg.neg h1
      simpa [neg_add] using this
    have hq : (2 : ℝ) * quad (Pt 1) v = v ⬝ᵥ v := by
      have := congrArg (fun M => quad M v) h2
      simp only [quad, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul] at this
      exact this
    have hvv : 0 < v ⬝ᵥ v := lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg (v i))
      (Ne.symm fun h => hv (dotProduct_self_eq_zero.mp h))
    linarith
  -- joint continuity of `(t, v) ↦ vᵀ P_t v`
  set qf : ℝ × (ι → ℝ) → ℝ := fun p => quad (Pt p.1) p.2 with hqf
  have hqf_eq : qf = fun p => ∑ i, p.2 i * ∑ j, Pt p.1 i j * p.2 j := by
    funext p; simp [hqf, quad, dotProduct, mulVec]
  have hqc : ContinuousOn qf (Icc 0 1 ×ˢ univ) := by
    rw [hqf_eq]
    apply continuousOn_finsetSum
    intro i _
    apply ContinuousOn.mul ((continuous_apply i).comp continuous_snd).continuousOn
    apply continuousOn_finsetSum
    intro j _
    apply ContinuousOn.mul _ ((continuous_apply j).comp continuous_snd).continuousOn
    exact (continuousOn_lyapSol_entry hJ i j).comp continuous_fst.continuousOn
      fun p hp => hp.1
  refine ⟨Pt 0, ?_, (hprop 0 ⟨le_rfl, zero_le_one⟩).1, ?_⟩
  · have h0 := lyapSol_spec (isHurwitz_homotopy hJ le_rfl zero_le_one)
    have hJ0 : homotopyJ J 0 = J := by simp [homotopyJ]
    rw [hJ0] at h0
    simpa [hPt, hJ0] using h0
  -- the main argument
  by_contra hnot
  simp only [not_forall, not_lt] at hnot
  obtain ⟨v, hv, hv0⟩ := hnot
  have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
  set u₀ := ‖v‖⁻¹ • v
  have hu₀ : u₀ ∈ Metric.sphere (0 : ι → ℝ) 1 := by simp [u₀, norm_smul, hnv.ne']
  have hq₀ : quad (Pt 0) u₀ ≤ 0 := by
    rw [quad_smul]; exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hv0
  set K : Set (ℝ × (ι → ℝ)) := (Icc 0 1 ×ˢ Metric.sphere 0 1) ∩ qf ⁻¹' Iic 0 with hK
  have hKc : IsCompact K := by
    apply (isCompact_Icc.prod (isCompact_sphere 0 1)).of_isClosed_subset _ inter_subset_left
    exact (hqc.mono (prod_mono subset_rfl (subset_univ _))).preimage_isClosed_of_isClosed
      (isClosed_Icc.prod Metric.isClosed_sphere) isClosed_Iic
  set A := Prod.fst '' K
  have hAc : IsCompact A := hKc.image continuous_fst
  have hAne : A.Nonempty := ⟨0, (0, u₀), ⟨⟨⟨le_rfl, zero_le_one⟩, hu₀⟩, hq₀⟩, rfl⟩
  have hsA := hAc.sSup_mem hAne
  set s := sSup A
  obtain ⟨⟨s', u⟩, ⟨⟨hs'I, hu⟩, hqu⟩, hs'⟩ := hsA
  simp only at hs'I hu hs'
  have hqu' : quad (Pt s') u ≤ 0 := hqu
  have hbdd : BddAbove A := hAc.bddAbove
  have huz : u ≠ 0 := by
    intro h; rw [h] at hu; simp at hu
  have hs1 : s' < 1 := by
    rcases eq_or_lt_of_le hs'I.2 with h | h
    · rw [h] at hqu'
      exact absurd hqu' (not_le.mpr (hpos1 u huz))
    · exact h
  -- positive semidefinite at `s'`
  have hpsd : ∀ w, 0 ≤ quad (Pt s') w := by
    intro w
    rcases eq_or_ne w 0 with rfl | hw
    · simp [quad]
    have hnw : 0 < ‖w‖ := norm_pos_iff.mpr hw
    set u' := ‖w‖⁻¹ • w
    have hu' : u' ∈ Metric.sphere (0 : ι → ℝ) 1 := by simp [u', norm_smul, hnw.ne']
    have hright : ∀ t ∈ Ioc s' 1, 0 < quad (Pt t) u' := by
      intro t ht
      by_contra hle
      have : t ∈ A := ⟨(t, u'), ⟨⟨⟨by linarith [ht.1, hs'I.1], ht.2⟩, hu'⟩, not_lt.mp hle⟩, rfl⟩
      have h3 : t ≤ s' := by rw [hs']; exact le_csSup hbdd this
      linarith [ht.1]
    have hcont : ContinuousWithinAt (fun t => quad (Pt t) u') (Ioc s' 1) s' := by
      have hc := (hqc (s', u') ⟨hs'I, mem_univ _⟩).comp (f := fun t => (t, u'))
        (continuous_id.prodMk continuous_const).continuousWithinAt
        (fun t (ht : t ∈ Ioc s' 1) => ⟨⟨by linarith [ht.1, hs'I.1], ht.2⟩, mem_univ _⟩)
      exact hc
    have hlim : Tendsto (fun t => quad (Pt t) u') (𝓝[>] s') (𝓝 (quad (Pt s') u')) := by
      rw [← nhdsWithin_Ioc_eq_nhdsGT hs1]; exact hcont
    have hev : ∀ᶠ t in 𝓝[>] s', 0 ≤ quad (Pt t) u' := by
      rw [← nhdsWithin_Ioc_eq_nhdsGT hs1]
      exact eventually_nhdsWithin_of_forall fun t ht => (hright t ht).le
    have hu'0 := ge_of_tendsto hlim hev
    have hw' : w = ‖w‖ • u' := by simp [u', smul_smul, hnw.ne']
    rw [hw', quad_smul]
    positivity
  have hzero : quad (Pt s') u = 0 := le_antisymm hqu' (hpsd u)
  have hker := mulVec_eq_zero_of_psd (hprop s' hs'I).1 hpsd hzero
  exact (hprop s' hs'I).2 u huz hker

/-- **Principle of linearized stability.** If `F x⋆ = 0` and `F` is differentiable at `x⋆` with a
Hurwitz Jacobian `J`, then `x⋆` is locally exponentially stable for `ẋ = F(x)`. -/
theorem hurwitz_local_exp_stable {F : (ι → ℝ) → (ι → ℝ)} {xs : ι → ℝ} {J : Matrix ι ι ℝ}
    (hF : HasFDerivAt F (LinearMap.toContinuousLinearMap (Matrix.toLin' J)) xs)
    (h0 : F xs = 0) (hJ : IsHurwitz J) :
    ∃ δ > 0, ∃ c > 0, ∃ C > 0, ∀ (x : ℝ → ι → ℝ) (T : ℝ),
      (∀ t ∈ Ico 0 T, HasDerivWithinAt x (F (x t)) (Ico 0 T) t) → ‖x 0 - xs‖ < δ →
        ∀ t ∈ Ico 0 T, ‖x t - xs‖ ^ 2 ≤ C * Real.exp (-c * t) * ‖x 0 - xs‖ ^ 2 := by
  obtain ⟨P, hP, -, hpos⟩ := converse_lyapunov hJ
  refine lyapunov_local_exp_stable hF h0 hpos fun e he => ?_
  rw [hP]
  have hee : 0 < e ⬝ᵥ e := lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg (e i))
    (Ne.symm fun h => he (dotProduct_self_eq_zero.mp h))
  simp only [quad, neg_mulVec, one_mulVec, dotProduct_neg]
  linarith

/-- **Linearized stability for mass-action networks**: a steady state whose Jacobian is Hurwitz is
locally exponentially stable for finite-horizon mass-action trajectories. -/
theorem ReactionNetwork.locallyExpStable_of_isHurwitz {C R : Type*} [Fintype R]
    (N : ReactionNetwork ι C R) {k : R → ℝ} {xs : ι → ℝ} (hxs : N.massActionField k xs = 0)
    (hJ : IsHurwitz (N.massActionJacobian k xs)) :
    ∃ δ > 0, ∃ c > 0, ∃ C > 0, ∀ (x : ℝ → ι → ℝ) (T : ℝ), N.MassActionTrajectoryOn k x T →
      ‖x 0 - xs‖ < δ →
        ∀ t ∈ Ico 0 T, ‖x t - xs‖ ^ 2 ≤ C * Real.exp (-c * t) * ‖x 0 - xs‖ ^ 2 := by
  obtain ⟨δ, hδ, c, hc, C, hC, h⟩ :=
    hurwitz_local_exp_stable (N.hasFDerivAt_massActionField k xs) hxs hJ
  exact ⟨δ, hδ, c, hc, C, hC, fun x T hx => h x T hx.hasDerivWithinAt⟩

end LeanTheory.CRN
