/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Design.EnvZOmpR
public import LeanTheory.Design.EnvZOmpRATP
public import LeanTheory.Design.IDHKP
public import LeanTheory.Theory.CRN.Persistence

/-!
# The siphon criterion fails for the source's ACR networks (notes N-012, N-008)

The siphon oracle (`scripts/oracles/siphon_cert.py`) finds, in each of the three Shinar–Feinberg
networks, a minimal siphon that supports **no** nonzero nonnegative conservation law, so the
persistence criterion cannot apply. This is not a weakness of the method:

* the face of each such siphon carries a **steady state in every compatibility class**: all
  reactions stop when only the "free" phosphorylated forms remain (`*_boundary_steady`);
* every **positive** steady state has total output above the ACR value (`*_total_gt`), so in
  classes whose total is at most the ACR value there is no positive steady state at all.

* IDHKP–IDH: siphon `{Ip, EIp, EIpI}` (`idh_isSiphon`, `idh_siphon_not_covered`), boundary states
  with only `E, I`, and `[I]* < I_total`.
* EnvZ–OmpR, ATP (Fig. 2B): siphon `{X, XT, Y, XpY, XTYp}`, boundary states with only `Xp, Yp`, and
  `[Yp]* < Y_total`.
* EnvZ–OmpR, ADP (Fig. 2D): siphon `{EnvZ-D, EnvZ, EnvZ-T, OmpR, EnvZ-OmpR-P, EnvZ-OmpR-D-P}`,
  boundary states with only `EnvZ-P, OmpR-P`, and `[OmpR-P]* < OmpR_total`.

Whether trajectories in low-total classes actually approach the boundary is a dynamical question
not formalized here.
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN.Design

open ReactionNetwork

/-- A coordinate outside the support set of a nonnegative vector supported there vanishes. -/
theorem eq_zero_of_not_supp {ι : Type*} {Z : ι → Prop} {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i)
    (hsupp : ∀ i, 0 < w i → Z i) {j : ι} (hj : ¬ Z j) : w j = 0 :=
  le_antisymm (not_lt.mp fun h => hj (hsupp j h)) (hw0 j)

/-! ### IDHKP–IDH (species E, Ip, EIp, I, EIpI) -/

/-- `{Ip, EIp, EIpI}` is a siphon of the IDHKP–IDH module. -/
theorem idh_isSiphon : idhNet.IsSiphon fun i => i = 1 ∨ i = 2 ∨ i = 4 := by
  rintro r ⟨i, hi, hpos⟩
  fin_cases r
  · exact ⟨1, by simp, by simp [idhNet]⟩
  · exact ⟨2, by simp, by simp [idhNet]⟩
  · exact ⟨2, by simp, by simp [idhNet]⟩
  · exact ⟨2, by simp, by simp [idhNet]⟩
  · exact ⟨4, by simp, by simp [idhNet]⟩
  · exact ⟨4, by simp, by simp [idhNet]⟩

/-- No nonzero nonnegative conservation law is supported in `{Ip, EIp, EIpI}`. -/
theorem idh_siphon_not_covered {w : Fin 5 → ℝ} (hw : idhNet.IsConservationLaw w)
    (hw0 : ∀ i, 0 ≤ w i) (hsupp : ∀ i, 0 < w i → i = 1 ∨ i = 2 ∨ i = 4) : w = 0 := by
  have z0 := eq_zero_of_not_supp hw0 hsupp (j := 0) (by simp)
  have z3 := eq_zero_of_not_supp hw0 hsupp (j := 3) (by simp)
  have r0 := hw _ (idhNet.reactionVector_mem_stoichSubspace 0)
  have r2 := hw _ (idhNet.reactionVector_mem_stoichSubspace 2)
  have r3 := hw _ (idhNet.reactionVector_mem_stoichSubspace 3)
  norm_num [reactionVector, complexVec, idhNet, dotProduct, Fin.sum_univ_succ] at r0 r2 r3
  funext i
  fin_cases i <;> simp <;> linarith

/-- **Boundary steady states**: with only `E` and `I` present, nothing reacts. -/
theorem idh_boundary_steady (k : Fin 6 → ℝ) (a b : ℝ) :
    idhNet.massActionField k ![a, 0, 0, b, 0] = 0 := by
  rw [idh_field]
  funext i
  fin_cases i <;> simp

/-- **Positive steady states need `I_total` above the ACR value**:
`[I]* < x_Ip + x_EIp + x_I + 2 x_EIpI`. -/
theorem idh_total_gt {k : Fin 6 → ℝ} (hk : ∀ r, 0 < k r) {x : Fin 5 → ℝ}
    (hx : idhNet.IsPosSteadyState k x) : idhACRValue k < x 1 + x 2 + x 3 + 2 * x 4 := by
  rw [← idh_steady_I hk hx]
  have := hx.1 1; have := hx.1 2; have := hx.1 4
  linarith

/-! ### EnvZ–OmpR, ATP (species X, XT, Xp, Y, XpY, Yp, XTYp) -/

/-- `{X, XT, Y, XpY, XTYp}` is a siphon of the ATP model. -/
theorem atp_isSiphon : atpNet.IsSiphon fun i => i = 0 ∨ i = 1 ∨ i = 3 ∨ i = 4 ∨ i = 6 := by
  rintro r ⟨i, hi, hpos⟩
  fin_cases r
  · exact ⟨0, by simp, by simp [atpNet]⟩
  · exact ⟨1, by simp, by simp [atpNet]⟩
  · exact ⟨1, by simp, by simp [atpNet]⟩
  · exact ⟨3, by simp, by simp [atpNet]⟩
  · exact ⟨4, by simp, by simp [atpNet]⟩
  · exact ⟨4, by simp, by simp [atpNet]⟩
  · exact ⟨1, by simp, by simp [atpNet]⟩
  · exact ⟨6, by simp, by simp [atpNet]⟩
  · exact ⟨6, by simp, by simp [atpNet]⟩

/-- No nonzero nonnegative conservation law is supported in `{X, XT, Y, XpY, XTYp}`. -/
theorem atp_siphon_not_covered {w : Fin 7 → ℝ} (hw : atpNet.IsConservationLaw w)
    (hw0 : ∀ i, 0 ≤ w i)
    (hsupp : ∀ i, 0 < w i → i = 0 ∨ i = 1 ∨ i = 3 ∨ i = 4 ∨ i = 6) : w = 0 := by
  have z2 := eq_zero_of_not_supp hw0 hsupp (j := 2) (by simp)
  have z5 := eq_zero_of_not_supp hw0 hsupp (j := 5) (by simp)
  have r0 := hw _ (atpNet.reactionVector_mem_stoichSubspace 0)
  have r2 := hw _ (atpNet.reactionVector_mem_stoichSubspace 2)
  have r3 := hw _ (atpNet.reactionVector_mem_stoichSubspace 3)
  have r5 := hw _ (atpNet.reactionVector_mem_stoichSubspace 5)
  have r6 := hw _ (atpNet.reactionVector_mem_stoichSubspace 6)
  norm_num [reactionVector, complexVec, atpNet, dotProduct, Fin.sum_univ_succ] at r0 r2 r3 r5 r6
  funext i
  fin_cases i <;> simp <;> linarith

/-- **Boundary steady states**: with only `Xp` and `Yp` present, nothing reacts. -/
theorem atp_boundary_steady (k : Fin 9 → ℝ) (a b : ℝ) :
    atpNet.massActionField k ![0, 0, a, 0, 0, b, 0] = 0 := by
  rw [atp_field]
  funext i
  fin_cases i <;> simp

/-- **Positive steady states need `Y_total` above the ACR value**. -/
theorem atp_total_gt {k : Fin 9 → ℝ} (hk : ∀ r, 0 < k r) {x : Fin 7 → ℝ}
    (hx : atpNet.IsPosSteadyState k x) : atpACRValue k < x 3 + x 4 + x 5 + x 6 := by
  rw [← atp_steady_Yp hk hx]
  have := hx.1 3; have := hx.1 4; have := hx.1 6
  linarith

/-! ### EnvZ–OmpR, ADP (species EnvZ-D, EnvZ, EnvZ-T, EnvZ-P, OmpR, EnvZ-OmpR-P, OmpR-P,
EnvZ-OmpR-D-P) -/

/-- `{EnvZ-D, EnvZ, EnvZ-T, OmpR, EnvZ-OmpR-P, EnvZ-OmpR-D-P}` is a siphon of the ADP model. -/
theorem envz_isSiphon :
    envzNet.IsSiphon fun i => i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 4 ∨ i = 5 ∨ i = 7 := by
  rintro r ⟨i, hi, hpos⟩
  fin_cases r
  · exact ⟨0, by simp, by simp [envzNet]⟩
  · exact ⟨1, by simp, by simp [envzNet]⟩
  · exact ⟨1, by simp, by simp [envzNet]⟩
  · exact ⟨2, by simp, by simp [envzNet]⟩
  · exact ⟨2, by simp, by simp [envzNet]⟩
  · exact ⟨4, by simp, by simp [envzNet]⟩
  · exact ⟨5, by simp, by simp [envzNet]⟩
  · exact ⟨5, by simp, by simp [envzNet]⟩
  · exact ⟨0, by simp, by simp [envzNet]⟩
  · exact ⟨7, by simp, by simp [envzNet]⟩
  · exact ⟨7, by simp, by simp [envzNet]⟩

/-- No nonzero nonnegative conservation law is supported in that siphon. -/
theorem envz_siphon_not_covered {w : Fin 8 → ℝ} (hw : envzNet.IsConservationLaw w)
    (hw0 : ∀ i, 0 ≤ w i)
    (hsupp : ∀ i, 0 < w i → i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 4 ∨ i = 5 ∨ i = 7) : w = 0 := by
  have z3 := eq_zero_of_not_supp hw0 hsupp (j := 3) (by simp)
  have z6 := eq_zero_of_not_supp hw0 hsupp (j := 6) (by simp)
  have r0 := hw _ (envzNet.reactionVector_mem_stoichSubspace 0)
  have r2 := hw _ (envzNet.reactionVector_mem_stoichSubspace 2)
  have r4 := hw _ (envzNet.reactionVector_mem_stoichSubspace 4)
  have r5 := hw _ (envzNet.reactionVector_mem_stoichSubspace 5)
  have r7 := hw _ (envzNet.reactionVector_mem_stoichSubspace 7)
  have r8 := hw _ (envzNet.reactionVector_mem_stoichSubspace 8)
  norm_num [reactionVector, complexVec, envzNet, dotProduct, Fin.sum_univ_succ]
    at r0 r2 r4 r5 r7 r8
  funext i
  fin_cases i <;> simp <;> linarith

/-- **Boundary steady states**: with only `EnvZ-P` and `OmpR-P` present, nothing reacts. -/
theorem envz_boundary_steady (k : Fin 11 → ℝ) (a b : ℝ) :
    envzNet.massActionField k ![0, 0, 0, a, 0, 0, b, 0] = 0 := by
  rw [envz_field]
  funext i
  fin_cases i <;> simp

/-- **Positive steady states need `OmpR_total` above the ACR value**. -/
theorem envz_total_gt {k : Fin 11 → ℝ} (hk : ∀ r, 0 < k r) {x : Fin 8 → ℝ}
    (hx : envzNet.IsPosSteadyState k x) : envzACRValue k < x 4 + x 5 + x 6 + x 7 := by
  rw [← envz_steady_OmpRP hk hx]
  have := hx.1 4; have := hx.1 5; have := hx.1 7
  linarith

end LeanTheory.CRN.Design
