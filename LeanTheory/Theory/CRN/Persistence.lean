/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Kernel.MassAction
public import Mathlib.Topology.MetricSpace.Sequences

/-!
# Persistence via siphons (note N-012, goal G-2)

A set of species `Z` is a **siphon** (`IsSiphon`) if every reaction producing a species of `Z`
consumes a species of `Z`.

* `massActionField_eq_zero_on_face`: on the face `{x ≥ 0 : x_Z = 0}` of a siphon, the field has no
  `Z`-component — the face is invariant.
* `massActionField_pos_of_not_isSiphon`: conversely, at a nonnegative point `p` whose zero set is
  **not** a siphon, some species with `p_i = 0` has `f_i(p) > 0`.
* `isSiphon_zeroSet_of_omegaLimit` (**Angeli–De Leenheer–Sontag**): for a bounded positive
  trajectory and positive rate constants, the zero set of every ω-limit point is a siphon. Proof
  without ω-limit invariance: if not, `f_i > c > 0` near `p` for some `i` with `p_i = 0`; along the
  trajectory, which moves at bounded speed, each visit close to `p` is preceded by a time `τ`
  spent near `p`, during which `x_i` grows by at least `cτ`; so `x_i(t_n) ≥ cτ`, contradicting
  `x_i(t_n) → 0`.
* `isPos_of_omegaLimit` (**siphon criterion**): if every nonempty siphon contains the support of a
  nonnegative conservation law, every ω-limit point of a bounded positive trajectory is positive
  (the conserved quantity `⟨w, x(t)⟩ > 0` would vanish at a boundary limit).
* `isPersistent_of_siphon`: under the same hypotheses, the trajectory is **persistent**, with a
  uniform lower bound `x_i(t) ≥ ε > 0` for all `t ≥ 0` (compactness of `[0, ∞]`).
* `bounded_of_pos_conservationLaw`: a strictly positive conservation law bounds every positive
  trajectory.

Scope: deterministic mass action, trajectories assumed to exist for all `t ≥ 0`. Certifying that a
list of siphons is complete for a given network is a separate (combinatorial) problem.
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN

open Filter Topology Set Finset

namespace ReactionNetwork

variable {ι C R : Type*} (N : ReactionNetwork ι C R)

/-- A **siphon**: a set of species such that every reaction producing a species of the set
consumes a species of the set. -/
def IsSiphon (Z : ι → Prop) : Prop :=
  ∀ r, (∃ i, Z i ∧ 0 < N.complex (N.tgt r) i) → ∃ j, Z j ∧ 0 < N.complex (N.src r) j

/-- The empty set is a siphon. -/
theorem isSiphon_empty : N.IsSiphon fun _ => False := fun _ ⟨_, h, _⟩ => h.elim

/-- A union of siphons is a siphon. -/
theorem IsSiphon.union {Z Z' : ι → Prop} (h : N.IsSiphon Z) (h' : N.IsSiphon Z') :
    N.IsSiphon fun i => Z i ∨ Z' i := by
  rintro r ⟨i, hi | hi, hpos⟩
  · obtain ⟨j, hj, hj'⟩ := h r ⟨i, hi, hpos⟩; exact ⟨j, Or.inl hj, hj'⟩
  · obtain ⟨j, hj, hj'⟩ := h' r ⟨i, hi, hpos⟩; exact ⟨j, Or.inr hj, hj'⟩

variable [Fintype ι] [Fintype R]

/-- A monomial vanishes at a point where one of its species is absent. -/
theorem monomial_eq_zero_of {y : ι → ℕ} {x : ι → ℝ} {j : ι} (hj : 0 < y j) (hx : x j = 0) :
    monomial y x = 0 :=
  Finset.prod_eq_zero (mem_univ j) (by rw [hx, zero_pow hj.ne'])

/-- **Siphon faces are invariant**: on `{x ≥ 0 : x_i = 0 for i ∈ Z}` the field has no
`Z`-component. -/
theorem massActionField_eq_zero_on_face {Z : ι → Prop} (hZ : N.IsSiphon Z) (k : R → ℝ)
    {x : ι → ℝ} (hx : ∀ i, Z i → x i = 0) {i : ι} (hi : Z i) : N.massActionField k x i = 0 := by
  rw [massActionField_apply]
  refine Finset.sum_eq_zero fun r _ => ?_
  by_cases hsrc : N.complex (N.src r) i = 0
  · by_cases htgt : N.complex (N.tgt r) i = 0
    · simp [reactionVector, complexVec, hsrc, htgt]
    · obtain ⟨j, hj, hj'⟩ := hZ r ⟨i, hi, Nat.pos_of_ne_zero htgt⟩
      simp [rate, monomial_eq_zero_of hj' (hx j hj)]
  · simp [rate, monomial_eq_zero_of (Nat.pos_of_ne_zero hsrc) (hx i hi)]

/-- **Escape from a non-siphon face**: if `p ≥ 0` and the zero set of `p` is not a siphon, some
species absent at `p` is produced at a positive rate: `f_i(p) > 0`. -/
theorem massActionField_pos_of_not_isSiphon {k : R → ℝ} (hk : ∀ r, 0 < k r) {p : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hns : ¬ N.IsSiphon fun i => p i = 0) :
    ∃ i, p i = 0 ∧ 0 < N.massActionField k p i := by
  classical
  simp only [IsSiphon, not_forall, not_exists, not_and, not_lt, exists_prop] at hns
  obtain ⟨r₀, ⟨i, hi, hprod⟩, hcons⟩ := hns
  refine ⟨i, hi, ?_⟩
  rw [massActionField_apply]
  have hterm : ∀ r, 0 ≤ N.rate k p r * N.reactionVector r i := by
    intro r
    by_cases hsrc : N.complex (N.src r) i = 0
    · have : 0 ≤ N.reactionVector r i := by simp [reactionVector, complexVec, hsrc]
      exact mul_nonneg (mul_nonneg (hk r).le
        (Finset.prod_nonneg fun j _ => pow_nonneg (hp j) _)) this
    · simp [rate, monomial_eq_zero_of (Nat.pos_of_ne_zero hsrc) hi]
  have hmono : 0 < monomial (N.complex (N.src r₀)) p := by
    refine Finset.prod_pos fun j _ => ?_
    by_cases hj : N.complex (N.src r₀) j = 0
    · simp [hj]
    · have hpj : p j ≠ 0 := fun h => hj (Nat.le_zero.mp (hcons j h))
      exact pow_pos (lt_of_le_of_ne (hp j) (Ne.symm hpj)) _
  have hr₀ : 0 < N.rate k p r₀ * N.reactionVector r₀ i := by
    have hsrc : N.complex (N.src r₀) i = 0 := Nat.le_zero.mp (hcons i hi)
    have : N.reactionVector r₀ i = N.complex (N.tgt r₀) i := by
      simp [reactionVector, complexVec, hsrc]
    rw [this]
    exact mul_pos (mul_pos (hk r₀) hmono) (by exact_mod_cast hprod)
  exact lt_of_lt_of_le hr₀ (Finset.single_le_sum (fun r _ => hterm r) (mem_univ r₀))

/-! ### ω-limit points -/

section Omega

variable {N} {k : R → ℝ} {x : ℝ → ι → ℝ}

/-- **Angeli–De Leenheer–Sontag**: for positive rate constants and a bounded positive trajectory,
the zero set of every ω-limit point is a siphon. -/
theorem isSiphon_zeroSet_of_omegaLimit (hk : ∀ r, 0 < k r) (hx : N.MassActionTrajectory k x)
    (h0 : IsPos (x 0)) {M : ℝ} (hM : ∀ t, 0 ≤ t → ‖x t‖ ≤ M) {t : ℕ → ℝ}
    (ht : Tendsto t atTop atTop) {p : ι → ℝ} (hp : Tendsto (fun n => x (t n)) atTop (𝓝 p)) :
    N.IsSiphon fun i => p i = 0 := by
  have hpos : ∀ s, 0 ≤ s → IsPos (x s) := fun s hs => hx.isPos (fun r => (hk r).le) h0 hs
  have hp0 : ∀ i, 0 ≤ p i := by
    intro i
    have hi : Tendsto (fun n => x (t n) i) atTop (𝓝 (p i)) :=
      ((continuous_apply i).tendsto p).comp hp
    refine ge_of_tendsto hi ?_
    filter_upwards [ht.eventually_ge_atTop 0] with n hn
    exact (hpos _ hn i).le
  by_contra hns
  obtain ⟨i, hpi, hfi⟩ := N.massActionField_pos_of_not_isSiphon hk hp0 hns
  set c := N.massActionField k p i / 2 with hc
  have hc0 : 0 < c := by positivity
  -- `f_i > c` near `p`
  have hcont : Continuous fun y => N.massActionField k y i :=
    (continuous_apply i).comp (N.continuous_massActionField k)
  obtain ⟨δ, hδ, hball⟩ : ∃ δ > 0, ∀ y, dist y p < δ → c < N.massActionField k y i := by
    have : ∀ᶠ y in 𝓝 p, c < N.massActionField k y i :=
      hcont.continuousAt.eventually (lt_mem_nhds (by linarith))
    exact Metric.eventually_nhds_iff.mp this
  -- the trajectory moves at bounded speed
  obtain ⟨L, hL⟩ := (isCompact_closedBall (0 : ι → ℝ) M).exists_bound_of_continuousOn
    (N.continuous_massActionField k).continuousOn
  set L' := max L 0 + 1 with hL'
  have hL'pos : 0 < L' := by positivity
  have hspeed : ∀ s, 0 ≤ s → ‖N.massActionField k (x s)‖ ≤ L' := fun s hs =>
    ((hL _ (mem_closedBall_zero_iff.mpr (hM s hs))).trans (le_max_left _ _)).trans (by linarith)
  set τ := δ / (4 * L') with hτ
  have hτ0 : 0 < τ := by positivity
  -- choose a visit `t n` close to `p`, late, with `x_i(t n)` small
  have hci : Tendsto (fun n => x (t n) i) atTop (𝓝 0) := by
    rw [← hpi]; exact ((continuous_apply i).tendsto p).comp hp
  obtain ⟨n, hn1, hn2, hn3⟩ : ∃ n, τ ≤ t n ∧ dist (x (t n)) p < δ / 2 ∧ x (t n) i < c * τ := by
    have e1 := ht.eventually_ge_atTop τ
    have e2 := (Metric.tendsto_nhds.mp hp) (δ / 2) (by positivity)
    have e3 := hci.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < c * τ))
    exact (e1.and (e2.and e3)).exists
  set a := t n - τ with ha
  have ha0 : 0 ≤ a := by linarith
  -- on `[a, t n]` the trajectory stays within `δ` of `p`
  have hlip : ∀ s ∈ Icc a (t n), ‖x s - x a‖ ≤ L' * (s - a) :=
    norm_image_sub_le_of_norm_deriv_le_segment'
      (fun s hs => (hx.hasDerivWithinAt s (ha0.trans hs.1)).mono
        (fun u hu => ha0.trans hu.1))
      (fun s hs => hspeed s (ha0.trans hs.1))
  have hnear : ∀ s ∈ Icc a (t n), dist (x s) p < δ := by
    intro s hs
    have h1 := hlip s hs
    have h2 := hlip (t n) ⟨by linarith, le_refl _⟩
    have hsa : s - a ≤ τ := by linarith [hs.2]
    have : dist (x s) (x (t n)) ≤ δ / 2 := by
      rw [dist_eq_norm]
      calc ‖x s - x (t n)‖ = ‖(x s - x a) - (x (t n) - x a)‖ := by congr 1; abel
        _ ≤ ‖x s - x a‖ + ‖x (t n) - x a‖ := norm_sub_le _ _
        _ ≤ L' * (s - a) + L' * (t n - a) := add_le_add h1 h2
        _ ≤ L' * τ + L' * τ := by gcongr; linarith
        _ = δ / 2 := by rw [hτ]; field_simp; ring
    linarith [dist_triangle (x s) (x (t n)) p]
  -- so `x_i` grows by at least `c τ` on `[a, t n]`
  have hgrow : c * (t n - a) ≤ x (t n) i - x a i := by
    have hD : Convex ℝ (Icc a (t n)) := convex_Icc _ _
    refine hD.mul_sub_le_image_sub_of_le_deriv (f := fun s => x s i) ?_ ?_ ?_ a
      ⟨le_refl _, by linarith⟩ (t n) ⟨by linarith, le_refl _⟩ (by linarith)
    · exact ((continuous_apply i).comp_continuousOn hx.continuousOn).mono
        (fun s hs => ha0.trans hs.1)
    · intro s hs
      rw [interior_Icc] at hs
      have := (hasDerivAt_pi.mp (hx.hasDerivAt (show 0 < s by linarith [hs.1]))) i
      exact this.differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      have := (hasDerivAt_pi.mp (hx.hasDerivAt (show 0 < s by linarith [hs.1]))) i
      rw [this.deriv]
      exact (hball _ (hnear s ⟨hs.1.le, hs.2.le⟩)).le
  have hxa := hpos a ha0 i
  rw [show t n - a = τ by rw [ha]; ring] at hgrow
  linarith

/-- **Siphon criterion**: if every nonempty siphon contains the support of a nonnegative
conservation law, then every ω-limit point of a bounded positive trajectory is positive. -/
theorem isPos_of_omegaLimit (hk : ∀ r, 0 < k r) (hx : N.MassActionTrajectory k x)
    (h0 : IsPos (x 0)) {M : ℝ} (hM : ∀ t, 0 ≤ t → ‖x t‖ ≤ M)
    (hsiph : ∀ Z : ι → Prop, N.IsSiphon Z → (∃ i, Z i) →
      ∃ w : ι → ℝ, N.IsConservationLaw w ∧ (∀ i, 0 ≤ w i) ∧ (∃ i, 0 < w i) ∧
        ∀ i, 0 < w i → Z i)
    {t : ℕ → ℝ} (ht : Tendsto t atTop atTop) {p : ι → ℝ}
    (hp : Tendsto (fun n => x (t n)) atTop (𝓝 p)) : IsPos p := by
  have hpos : ∀ s, 0 ≤ s → IsPos (x s) := fun s hs => hx.isPos (fun r => (hk r).le) h0 hs
  have hp0 : ∀ i, 0 ≤ p i := by
    intro i
    refine ge_of_tendsto (((continuous_apply i).tendsto p).comp hp) ?_
    filter_upwards [ht.eventually_ge_atTop 0] with n hn
    exact (hpos _ hn i).le
  by_contra hnp
  obtain ⟨i₀, hi₀⟩ : ∃ i, p i = 0 := by
    by_contra h
    push Not at h
    exact hnp fun i => lt_of_le_of_ne (hp0 i) (Ne.symm (h i))
  have hZ := isSiphon_zeroSet_of_omegaLimit hk hx h0 hM ht hp
  obtain ⟨w, hw, hw0, ⟨j, hj⟩, hsupp⟩ := hsiph _ hZ ⟨i₀, hi₀⟩
  -- the conserved quantity is positive along the trajectory and zero at `p`
  have hcd : Continuous fun y : ι → ℝ => w ⬝ᵥ y := by
    simp only [dotProduct]; fun_prop
  have hlim : Tendsto (fun n => w ⬝ᵥ x (t n)) atTop (𝓝 (w ⬝ᵥ p)) :=
    (hcd.tendsto p).comp hp
  have hconst : ∀ᶠ n in atTop, w ⬝ᵥ x (t n) = w ⬝ᵥ x 0 := by
    filter_upwards [ht.eventually_ge_atTop 0] with n hn
    exact hx.dotProduct_eq hw hn
  have hwp : w ⬝ᵥ p = w ⬝ᵥ x 0 :=
    tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hconst.mono fun _ h => h.symm))
  have hzero : w ⬝ᵥ p = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hwi : 0 < w i
    · rw [hsupp i hwi, mul_zero]
    · rw [le_antisymm (not_lt.mp hwi) (hw0 i), zero_mul]
  have hpos0 : 0 < w ⬝ᵥ x 0 :=
    lt_of_lt_of_le (mul_pos hj (h0 j)) (Finset.single_le_sum
      (fun i _ => mul_nonneg (hw0 i) (h0 i).le) (mem_univ j))
  linarith

/-- **Persistence**: under the siphon criterion, a bounded positive trajectory stays uniformly
away from the boundary: `x_i(t) ≥ ε > 0` for all `t ≥ 0` and all species `i`. -/
theorem isPersistent_of_siphon (hk : ∀ r, 0 < k r) (hx : N.MassActionTrajectory k x)
    (h0 : IsPos (x 0)) {M : ℝ} (hM : ∀ t, 0 ≤ t → ‖x t‖ ≤ M)
    (hsiph : ∀ Z : ι → Prop, N.IsSiphon Z → (∃ i, Z i) →
      ∃ w : ι → ℝ, N.IsConservationLaw w ∧ (∀ i, 0 ≤ w i) ∧ (∃ i, 0 < w i) ∧
        ∀ i, 0 < w i → Z i) :
    ∃ ε > 0, ∀ s, 0 ≤ s → ∀ i, ε ≤ x s i := by
  have hpos : ∀ s, 0 ≤ s → IsPos (x s) := fun s hs => hx.isPos (fun r => (hk r).le) h0 hs
  by_contra hne
  have hseq : ∀ n : ℕ, ∃ s, 0 ≤ s ∧ ∃ i, x s i < 1 / ((n : ℝ) + 1) := by
    intro n
    by_contra h
    push Not at h
    exact hne ⟨1 / ((n : ℝ) + 1), by positivity, fun s hs i => h s hs i⟩
  choose s hs0 i hi using hseq
  -- compactify time: `u = s / (1 + s) ∈ [0, 1)`
  set u : ℕ → ℝ × (ι → ℝ) := fun n => (s n / (1 + s n), x (s n))
  have hbdd : Bornology.IsBounded (Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : ι → ℝ) M) :=
    (Metric.isBounded_Icc 0 1).prod Metric.isBounded_closedBall
  have hmem : ∀ n, u n ∈ Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : ι → ℝ) M := by
    intro n
    refine ⟨⟨by have := hs0 n; positivity, ?_⟩, mem_closedBall_zero_iff.mpr (hM _ (hs0 n))⟩
    rw [div_le_one (by linarith [hs0 n])]; linarith
  obtain ⟨⟨σ, p⟩, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded hbdd hmem
  have hσ : Tendsto (fun n => s (φ n) / (1 + s (φ n))) atTop (𝓝 σ) :=
    (continuous_fst.tendsto _).comp hlim
  have hp : Tendsto (fun n => x (s (φ n))) atTop (𝓝 p) := (continuous_snd.tendsto _).comp hlim
  -- some coordinate of `p` vanishes (pigeonhole on the finitely many species)
  obtain ⟨j, hj⟩ : ∃ j, ∃ᶠ n in atTop, i (φ n) = j := by
    by_contra h
    push Not at h
    have : ∀ᶠ n in atTop, ∀ j, i (φ n) ≠ j := by
      rw [Filter.eventually_all]; exact fun j => (h j)
    obtain ⟨n, hn⟩ := this.exists
    exact hn _ rfl
  have hpj : p j = 0 := by
    have hpj0 : 0 ≤ p j := by
      refine ge_of_tendsto (((continuous_apply j).tendsto p).comp hp) (Eventually.of_forall
        fun n => (hpos _ (hs0 _) j).le)
    refine le_antisymm ?_ hpj0
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨N₀, hN₀⟩ := exists_nat_gt (2 / ε)
    have hev := ((continuous_apply j).tendsto p).comp hp
    have e1 : ∀ᶠ n in atTop, p j - ε / 2 < x (s (φ n)) j :=
      hev.eventually (lt_mem_nhds (by linarith))
    have e2 : ∀ᶠ n in atTop, N₀ ≤ φ n :=
      (hφ.tendsto_atTop).eventually_ge_atTop N₀
    obtain ⟨n, hn3, hn1, hn2⟩ := (hj.and_eventually (e1.and e2)).exists
    have hlt := hi (φ n)
    rw [hn3] at hlt
    have : 1 / ((φ n : ℝ) + 1) < ε / 2 := by
      rw [div_lt_iff₀ (by positivity)]
      have : (N₀ : ℝ) ≤ φ n := by exact_mod_cast hn2
      rw [div_lt_iff₀ hε] at hN₀
      nlinarith
    linarith
  rcases lt_or_eq_of_le (show σ ≤ 1 from (isClosed_Iic.mem_of_tendsto hσ
    (Eventually.of_forall fun n => by
      rw [Set.mem_Iic, div_le_one (by linarith [hs0 (φ n)])]; linarith))) with hσ1 | hσ1
  · -- bounded times: a limit time `t* = σ / (1 − σ)` with `x(t*) = p`, not positive
    set g : ℝ → ℝ := fun v => v / (1 - v)
    have hg : ContinuousAt g σ := continuousAt_id.div (continuousAt_const.sub continuousAt_id)
      (by linarith)
    have hts : Tendsto (fun n => s (φ n)) atTop (𝓝 (g σ)) := by
      have := hg.tendsto.comp hσ
      refine this.congr fun n => ?_
      have h1 : (1 : ℝ) + s (φ n) ≠ 0 := by linarith [hs0 (φ n)]
      simp only [Function.comp, g]
      field_simp
      ring
    have hgσ : 0 ≤ g σ := ge_of_tendsto hts (Eventually.of_forall fun n => hs0 _)
    have hxt : Tendsto (fun n => x (s (φ n))) atTop (𝓝 (x (g σ))) :=
      (hx.continuousOn.continuousWithinAt hgσ).tendsto.comp
        (tendsto_nhdsWithin_iff.mpr ⟨hts, Eventually.of_forall fun n => hs0 _⟩)
    have := tendsto_nhds_unique hxt hp
    have hpos' := hpos _ hgσ j
    rw [this, hpj] at hpos'
    exact lt_irrefl _ hpos'
  · -- unbounded times: `p` is an ω-limit point with a zero coordinate
    have hts : Tendsto (fun n => s (φ n)) atTop atTop := by
      rw [tendsto_atTop]
      intro B
      have hB : ∀ᶠ n in atTop, (max B 0) / (1 + max B 0) < s (φ n) / (1 + s (φ n)) := by
        rw [hσ1] at hσ
        exact hσ.eventually (lt_mem_nhds (by
          rw [div_lt_one (by positivity)]; linarith))
      filter_upwards [hB] with n hn
      have h1 : 0 < 1 + max B 0 := by positivity
      have h2 : 0 < 1 + s (φ n) := by linarith [hs0 (φ n)]
      rw [div_lt_div_iff₀ h1 h2] at hn
      nlinarith [le_max_left B 0]
    have := isPos_of_omegaLimit hk hx h0 hM hsiph hts hp j
    rw [hpj] at this
    exact lt_irrefl _ this

/-- A strictly positive conservation law bounds every positive trajectory. -/
theorem bounded_of_pos_conservationLaw (hk : ∀ r, 0 ≤ k r) (hx : N.MassActionTrajectory k x)
    (h0 : IsPos (x 0)) {w : ι → ℝ} (hw : N.IsConservationLaw w) (hwpos : ∀ i, 0 < w i) :
    ∃ M, ∀ t, 0 ≤ t → ‖x t‖ ≤ M := by
  refine ⟨∑ i, (w ⬝ᵥ x 0) / w i, fun t ht => ?_⟩
  have hpos := hx.isPos hk h0 ht
  have hcons := hx.dotProduct_eq hw ht
  refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ =>
    div_nonneg (Finset.sum_nonneg fun j _ => mul_nonneg (hwpos j).le (h0 j).le)
      (hwpos i).le)).mpr fun i => ?_
  rw [Real.norm_eq_abs, abs_of_pos (hpos i)]
  have hxi : x t i ≤ (w ⬝ᵥ x 0) / w i := by
    rw [le_div_iff₀ (hwpos i), ← hcons, mul_comm]
    exact Finset.single_le_sum (fun j _ => mul_nonneg (hwpos j).le (hpos j).le) (mem_univ i)
  exact hxi.trans (Finset.single_le_sum (f := fun i => (w ⬝ᵥ x 0) / w i)
    (fun j _ => div_nonneg (Finset.sum_nonneg fun l _ => mul_nonneg (hwpos l).le (h0 l).le)
      (hwpos j).le) (mem_univ i))

end Omega

end ReactionNetwork

end LeanTheory.CRN
