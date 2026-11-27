/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Design.IDHKP
public import LeanTheory.Theory.CRN.ClassStability
public import LeanTheory.Certificates.RouthHurwitz

/-!
# Case study: IDHKP–IDH is stable within its compatibility classes (note N-008)

For the IDHKP–IDH module of `Design/IDHKP` we prove, for **all positive rate constants** and
**every positive steady state**, local exponential stability within the compatibility class
(`idh_classStable`).

Coordinates of the stoichiometric subspace `S = span{r₀, r₂, r₃}` (rank 3): `B` has the reaction
vectors `r₀ = (−1, −1, 1, 0, 0)`, `r₂ = (1, 0, −1, 1, 0)`, `r₃ = (0, 0, −1, −1, 1)` as columns, and
`C u = (−u₁, u₀ − u₁, u₄)` recovers the coefficients (`idhB`, `idhC`, `idh_proj`, using the two
conservation laws). The restricted Jacobian `C J B` is, at **every** state `x`,

```text
[ −κ₁x₀ − κ₁x₁ − κ₂   κ₁x₁ + κ₂            κ₂ − κ₆               ]
[ κ₃                  −κ₃                  −κ₃ − κ₆              ]
[ κ₄x₃                κ₄(x₂ − x₃)          −κ₄x₂ − κ₄x₃ − κ₅ − κ₆ ]
```

(`idhR`, `idh_restrict`; indices of `κ` shifted by one from `k`). Routh–Hurwitz (format 7,
`isHurwitz_fin_three`) with polynomial certificates found by the sympy oracle:

* `tr R < 0` at every positive `x`;
* `det R = −D(k, x) < 0` at every positive steady state: `D` is a positive polynomial, and the
  identity uses the ACR relation `κ₄κ₆ x_I = κ₃(κ₅ + κ₆)` (`idh_steady_I`);
* `det R − tr R · m(R) = E(k, x) > 0` at every positive `x`, where `E` is an explicit polynomial
  with 83 terms, all with positive coefficients (`idhE`).

Label: exact, idealized; all positive rates, every positive steady state.
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN.Design

open Matrix ReactionNetwork Set

/-- Gradients of the six reaction monomials: row `r` is `∇ x^{y(src r)}`. -/
def idhG (x : Fin 5 → ℝ) : Fin 6 → Fin 5 → ℝ :=
  ![![x 1, x 0, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, x 3, x 2, 0],
    ![0, 0, 0, 0, 1], ![0, 0, 0, 0, 1]]

/-- The six reaction vectors. -/
def idhZ : Fin 6 → Fin 5 → ℝ :=
  ![![-1, -1, 1, 0, 0], ![1, 1, -1, 0, 0], ![1, 0, -1, 1, 0], ![0, 0, -1, -1, 1],
    ![0, 0, 1, 1, -1], ![0, 1, 1, 0, -1]]

/-- The entries `y_j x^{y − e_j}` of the Jacobian formula are the monomial gradients `idhG`. -/
theorem idh_grad (x : Fin 5 → ℝ) (r : Fin 6) (j : Fin 5) :
    (idhNet.complex (idhNet.src r) j : ℝ) *
      monomial (Function.update (idhNet.complex (idhNet.src r)) j
        (idhNet.complex (idhNet.src r) j - 1)) x = idhG x r j := by
  fin_cases r <;> fin_cases j <;>
    simp [idhNet, idhG, monomial, Fin.prod_univ_succ, Function.update]

/-- The reaction vectors are `idhZ`. -/
theorem idh_rv (r : Fin 6) : idhNet.reactionVector r = idhZ r := by
  funext i
  fin_cases r <;> fin_cases i <;> simp [reactionVector, complexVec, idhNet, idhZ]

/-- The mass-action Jacobian of the IDHKP–IDH module at a state `x`. -/
theorem idh_jacobian (k : Fin 6 → ℝ) (x : Fin 5 → ℝ) :
    idhNet.massActionJacobian k x =
      !![-(k 0 * x 1), -(k 0 * x 0), k 1 + k 2, 0, 0;
         -(k 0 * x 1), -(k 0 * x 0), k 1, 0, k 5;
         k 0 * x 1, k 0 * x 0, -k 1 - k 2 - k 3 * x 3, -(k 3 * x 2), k 4 + k 5;
         0, 0, k 2 - k 3 * x 3, -(k 3 * x 2), k 4;
         0, 0, k 3 * x 3, k 3 * x 2, -k 4 - k 5] := by
  ext i j
  simp only [massActionJacobian, of_apply, mul_assoc, idh_grad, idh_rv]
  fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_succ, idhG, idhZ] <;> ring

/-! ### Coordinates on the stoichiometric subspace -/

/-- Reconstruction `ℝ³ → S`: the reaction vectors `r₀, r₂, r₃` as columns. -/
def idhB : Matrix (Fin 5) (Fin 3) ℝ :=
  !![-1, 1, 0;
     -1, 0, 0;
     1, -1, -1;
     0, 1, -1;
     0, 0, 1]

/-- Coordinates `(−u₁, u₀ − u₁, u₄)` of a vector of `S` in the basis `r₀, r₂, r₃`. -/
def idhC : Matrix (Fin 3) (Fin 5) ℝ :=
  !![0, -1, 0, 0, 0;
     1, -1, 0, 0, 0;
     0, 0, 0, 0, 1]

/-- Vectors of the stoichiometric subspace satisfy both conservation laws. -/
theorem idh_cons_of_mem {u : Fin 5 → ℝ} (hu : u ∈ idhNet.stoichSubspace) :
    u 0 + u 2 + u 4 = 0 ∧ u 1 + u 2 + u 3 + 2 * u 4 = 0 := by
  have hle : idhNet.stoichSubspace ≤ LinearMap.ker idhCons := by
    rw [stoichSubspace, Submodule.span_le]
    rintro _ ⟨r, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    funext i
    fin_cases r <;> fin_cases i <;>
      norm_num [idhCons, reactionVector, complexVec, idhNet]
  have h := LinearMap.mem_ker.mp (hle hu)
  exact ⟨congrFun h 0, congrFun h 1⟩

/-- `B C u = u` on the stoichiometric subspace. -/
theorem idh_proj {u : Fin 5 → ℝ} (hu : u ∈ idhNet.stoichSubspace) :
    idhB *ᵥ (idhC *ᵥ u) = u := by
  obtain ⟨h1, h2⟩ := idh_cons_of_mem hu
  funext i
  fin_cases i <;>
    simp [idhB, idhC, mulVec, dotProduct, Fin.sum_univ_succ] <;> linarith

/-! ### The restricted Jacobian and Routh–Hurwitz -/

/-- The restricted Jacobian `C J B` at a state `x`. -/
def idhR (k : Fin 6 → ℝ) (x : Fin 5 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-(k 0 * x 0) - k 0 * x 1 - k 1, k 0 * x 1 + k 1, k 1 - k 5;
     k 2, -k 2, -k 2 - k 5;
     k 3 * x 3, k 3 * (x 2 - x 3), -(k 3 * x 2) - k 3 * x 3 - k 4 - k 5]

/-- The restricted Jacobian is `idhR` at every state. -/
theorem idh_restrict (k : Fin 6 → ℝ) (x : Fin 5 → ℝ) :
    idhC * idhNet.massActionJacobian k x * idhB = idhR k x := by
  rw [idh_jacobian]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [idhB, idhC, idhR, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

/-- The Routh–Hurwitz certificate polynomial `E = det R − tr R · m(R)` (sympy oracle): all 83
coefficients are positive. -/
def idhE (k : Fin 6 → ℝ) (x : Fin 5 → ℝ) : ℝ :=
  k 0^2*k 2*x 0^2 + k 0^2*k 2*x 0*x 1 + k 0^2*k 3*x 0^2*x 2 + k 0^2*k 3*x 0^2*x 3
  + 2*k 0^2*k 3*x 0*x 1*x 2 + 2*k 0^2*k 3*x 0*x 1*x 3 + k 0^2*k 3*x 1^2*x 2 + k 0^2*k 3*x 1^2*x 3
  + k 0^2*k 4*x 0^2 + 2*k 0^2*k 4*x 0*x 1 + k 0^2*k 4*x 1^2 + k 0^2*k 5*x 0^2
  + 2*k 0^2*k 5*x 0*x 1 + k 0^2*k 5*x 1^2 + k 0*k 1*k 2*x 0 + 2*k 0*k 1*k 3*x 0*x 2
  + k 0*k 1*k 3*x 0*x 3 + 2*k 0*k 1*k 3*x 1*x 2 + k 0*k 1*k 3*x 1*x 3 + 2*k 0*k 1*k 4*x 0
  + 2*k 0*k 1*k 4*x 1 + 2*k 0*k 1*k 5*x 0 + 2*k 0*k 1*k 5*x 1 + k 0*k 2^2*x 0
  + 2*k 0*k 2*k 3*x 0*x 2 + 2*k 0*k 2*k 3*x 0*x 3 + 2*k 0*k 2*k 3*x 1*x 2 + k 0*k 2*k 3*x 1*x 3
  + 2*k 0*k 2*k 4*x 0 + 2*k 0*k 2*k 4*x 1 + 2*k 0*k 2*k 5*x 0 + 2*k 0*k 2*k 5*x 1
  + k 0*k 3^2*x 0*x 2^2 + 2*k 0*k 3^2*x 0*x 2*x 3 + k 0*k 3^2*x 0*x 3^2 + k 0*k 3^2*x 1*x 2^2
  + 2*k 0*k 3^2*x 1*x 2*x 3 + k 0*k 3^2*x 1*x 3^2 + 2*k 0*k 3*k 4*x 0*x 2
  + 2*k 0*k 3*k 4*x 0*x 3 + 2*k 0*k 3*k 4*x 1*x 2 + 2*k 0*k 3*k 4*x 1*x 3
  + 2*k 0*k 3*k 5*x 0*x 2 + 3*k 0*k 3*k 5*x 0*x 3 + 2*k 0*k 3*k 5*x 1*x 2
  + 2*k 0*k 3*k 5*x 1*x 3 + k 0*k 4^2*x 0 + k 0*k 4^2*x 1 + 2*k 0*k 4*k 5*x 0
  + 2*k 0*k 4*k 5*x 1 + k 0*k 5^2*x 0 + k 0*k 5^2*x 1 + k 1^2*k 3*x 2 + k 1^2*k 4 + k 1^2*k 5
  + 3*k 1*k 2*k 3*x 2 + 2*k 1*k 2*k 4 + 2*k 1*k 2*k 5 + k 1*k 3^2*x 2^2 + k 1*k 3^2*x 2*x 3
  + 2*k 1*k 3*k 4*x 2 + k 1*k 3*k 4*x 3 + 2*k 1*k 3*k 5*x 2 + k 1*k 3*k 5*x 3 + k 1*k 4^2
  + 2*k 1*k 4*k 5 + k 1*k 5^2 + 2*k 2^2*k 3*x 2 + k 2^2*k 4 + k 2^2*k 5 + 2*k 2*k 3^2*x 2^2
  + 2*k 2*k 3^2*x 2*x 3 + 3*k 2*k 3*k 4*x 2 + k 2*k 3*k 4*x 3 + 3*k 2*k 3*k 5*x 2
  + k 2*k 3*k 5*x 3 + k 2*k 4^2 + 2*k 2*k 4*k 5 + k 2*k 5^2 + k 3^2*k 5*x 2^2
  + k 3^2*k 5*x 2*x 3 + k 3*k 4*k 5*x 2 + k 3*k 5^2*x 2

/-- **The restricted Jacobian is Hurwitz** at every positive steady state, for all positive rate
constants. Only positivity of `x` and the ACR relation for `x_I` are used. -/
theorem idhR_isHurwitz {k : Fin 6 → ℝ} (hk : ∀ r, 0 < k r) {x : Fin 5 → ℝ} (hx : IsPos x)
    (hI : x 3 = idhACRValue k) : IsHurwitz (idhR k x) := by
  have k0 := hk 0; have k1 := hk 1; have k2 := hk 2; have k3 := hk 3; have k4 := hk 4
  have k5 := hk 5
  have x0 := hx 0; have x1 := hx 1; have x2 := hx 2; have x3 := hx 3
  have h3 : k 3 * k 5 * x 3 = k 2 * (k 4 + k 5) := by
    rw [hI, idhACRValue]; field_simp
  have htr : (idhR k x).trace = -(k 0 * x 0 + k 0 * x 1 + k 1 + k 2 + k 3 * x 2 + k 3 * x 3 + k 4
      + k 5) := by
    simp [idhR, Matrix.trace, Fin.sum_univ_three]; ring
  have hdet0 : (idhR k x).det = -2 * k 0 * k 2 * k 3 * x 0 * x 2 - k 0 * k 2 * k 3 * x 1 * x 2
      - k 0 * k 2 * k 4 * x 0 - k 0 * k 2 * k 5 * x 0 - k 0 * k 3 * k 5 * x 0 * x 2
      + k 0 * k 3 * k 5 * x 0 * x 3 - k 0 * k 3 * k 5 * x 1 * x 2 - k 1 * k 3 * k 5 * x 2
      - k 2 * k 3 * k 5 * x 2 := by
    simp [idhR, Matrix.det_fin_three]; ring
  have hm : principalMinorSum (idhR k x) = k 0 * k 2 * x 0 + k 0 * k 3 * x 0 * x 2
      + k 0 * k 3 * x 0 * x 3 + k 0 * k 3 * x 1 * x 2 + k 0 * k 3 * x 1 * x 3 + k 0 * k 4 * x 0
      + k 0 * k 4 * x 1 + k 0 * k 5 * x 0 + k 0 * k 5 * x 1 + k 1 * k 3 * x 2 + k 1 * k 4
      + k 1 * k 5 + 2 * k 2 * k 3 * x 2 + k 2 * k 4 + k 2 * k 5 + k 3 * k 5 * x 2 := by
    simp [idhR, principalMinorSum]; ring
  have hdet : (idhR k x).det = -(2 * k 0 * k 2 * k 3 * x 0 * x 2 + k 0 * k 2 * k 3 * x 1 * x 2
      + k 0 * k 3 * k 5 * x 0 * x 2 + k 0 * k 3 * k 5 * x 1 * x 2 + k 1 * k 3 * k 5 * x 2
      + k 2 * k 3 * k 5 * x 2) := by
    rw [hdet0]
    linear_combination (k 0 * x 0) * h3
  have hE : (idhR k x).det - (idhR k x).trace * principalMinorSum (idhR k x) = idhE k x := by
    rw [hdet0, htr, hm, idhE]
    ring
  have hEpos : 0 < idhE k x := by unfold idhE; positivity
  refine isHurwitz_fin_three ?_ ?_ (by linarith)
  · rw [htr]; nlinarith [mul_pos k0 x0, mul_pos k3 x2]
  · rw [hdet]
    have : 0 < k 1 * k 3 * k 5 * x 2 := by positivity
    have : 0 < 2 * k 0 * k 2 * k 3 * x 0 * x 2 + k 0 * k 2 * k 3 * x 1 * x 2
      + k 0 * k 3 * k 5 * x 0 * x 2 + k 0 * k 3 * k 5 * x 1 * x 2 + k 2 * k 3 * k 5 * x 2 := by
      positivity
    linarith

/-- **IDHKP–IDH is stable within its compatibility classes**: for all positive rate constants,
every positive steady state attracts, exponentially, nearby trajectories with the same totals of
`E` and `I`. -/
theorem idh_classStable {k : Fin 6 → ℝ} (hk : ∀ r, 0 < k r) {xs : Fin 5 → ℝ}
    (hxs : idhNet.IsPosSteadyState k xs) :
    ∃ δ > 0, ∃ c > 0, ∃ K > 0, ∀ (x : ℝ → Fin 5 → ℝ) (T : ℝ),
      idhNet.MassActionTrajectoryOn k x T → x 0 - xs ∈ idhNet.stoichSubspace →
        ‖x 0 - xs‖ < δ →
          ∀ t ∈ Ico 0 T, ‖x t - xs‖ ^ 2 ≤ K * Real.exp (-c * t) * ‖x 0 - xs‖ ^ 2 := by
  refine idhNet.classLocallyExpStable_of_restrict hxs.2 (B := idhB) (C := idhC)
    (fun u hu => idh_proj hu) ?_
  rw [idh_restrict]
  exact idhR_isHurwitz hk hxs.1 (idh_steady_I hk hxs)

end LeanTheory.CRN.Design
