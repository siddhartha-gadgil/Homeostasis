/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Kernel.CME
public import LeanTheory.Certificates.PolyCert

/-!
# Foster–Lyapunov drift and stationary moment bounds for the CME (note N-014, goal G-3)

For a reaction network with stochastic rate constants `κ` and a test function
`V : (ι → ℕ) → ℝ`:

* `HasDrift N κ V c b`: the drift inequality `(𝒜 V)(x) ≤ −c V(x) + b` at **every** state
  (user idea `U-FL`; the generator `𝒜` acts on `V` itself, correction `X-6`).
* `stationary_moment_le`: if `c > 0`, then every nonnegative `π` of total mass `1` under which `V`
  has finite mean `m`, and which is generator-stationary for `V`, satisfies the **moment bound**
  `m ≤ b / c`.
* `hasDrift_of_cert` (certificate format 5): the drift inequality follows from an identity
  `−c V + b − 𝒜V = SOS + (nonnegative-coefficient polynomial)` in the real copy numbers, checked
  by `ring` at the use site (formats 3 and 1 of `Certificates/PolyCert`).

Scope: generator level only. The moment bound needs generator-stationarity for `V` with
integrability as a hypothesis; the classical consequences of the drift inequality for the process
(non-explosion, positive recurrence, existence of a stationary distribution) need the process
layer (Q-8) and are not proved here.
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN.ReactionNetwork

open LeanTheory.Certificates.Poly

variable {ι C R : Type*} [Fintype ι] [Fintype R] (N : ReactionNetwork ι C R)

/-- **Foster–Lyapunov drift**: `(𝒜 V)(x) ≤ −c V(x) + b` at every state. -/
def HasDrift (κ : R → ℝ) (V : (ι → ℕ) → ℝ) (c b : ℝ) : Prop :=
  ∀ x, N.generator κ V x ≤ -c * V x + b

/-- **Stationary moment bound**: under the drift inequality with `c > 0`, every probability
distribution that is generator-stationary for `V` and has finite `V`-moment `m` satisfies
`m ≤ b / c`. -/
theorem stationary_moment_le {κ : R → ℝ} {V : (ι → ℕ) → ℝ} {c b : ℝ}
    (hdrift : N.HasDrift κ V c b) (hc : 0 < c) {π : (ι → ℕ) → ℝ} (hπ0 : ∀ x, 0 ≤ π x)
    (hπ1 : HasSum π 1) {m : ℝ} (hm : HasSum (fun x => π x * V x) m)
    (hst : N.IsGenStationaryFor κ π V) : m ≤ b / c := by
  have hrhs : HasSum (fun x => π x * (-c * V x + b)) (-c * m + b * 1) := by
    have := (hm.mul_left (-c)).add (hπ1.mul_left b)
    convert this using 1
    funext x
    ring
  have hle := hasSum_le (fun x => mul_le_mul_of_nonneg_left (hdrift x) (hπ0 x)) hst hrhs
  rw [le_div_iff₀ hc]
  linarith

/-- **Drift certificate (format 5)**: the identity `−c V + b − 𝒜V = SOS + Σ (nonneg) · x^e` in the
real copy numbers gives the drift inequality. -/
theorem hasDrift_of_cert {κ : R → ℝ} {V : (ι → ℕ) → ℝ} {c b : ℝ}
    {sos : List (ℚ × ((ι → ℝ) → ℝ))} {pos : List (ℚ × (ι → ℕ))} (hsos : ∀ t ∈ sos, 0 ≤ t.1)
    (hpos : ∀ t ∈ pos, 0 ≤ t.1)
    (hid : ∀ x, -c * V x + b - N.generator κ V x =
      sosComb sos (toReal x) + posComb pos (toReal x)) :
    N.HasDrift κ V c b := by
  intro x
  have h1 := sosComb_nonneg hsos (toReal x)
  have h2 := posComb_nonneg hpos (x := toReal x) (fun i => Nat.cast_nonneg (x i))
  linarith [hid x]

end LeanTheory.CRN.ReactionNetwork
