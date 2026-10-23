import ShortTime.Nonlinear.SmoothRepTimeComp

/-!
# `SpC` for finite products

`SpC.pi`: a finite family of functions in `SpC k n` packages to a function into the product space.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set Filter Topology Metric
open scoped ContDiff

namespace ShortTime

namespace SpatialReg

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ} {S : Set ℝ} {U : Set E}

theorem SpC.pi (hS : UniqueDiffOn ℝ S) (hU : IsOpen U) {ι : Type} [Fintype ι] [DecidableEq ι]
    (n : ℕ) : ∀ {V : ι → Type u} [∀ c, NormedAddCommGroup (V c)] [∀ c, NormedSpace ℝ (V c)]
      {φ : ∀ c, ℝ → E → V c}, (∀ c, SpC k S U n (V c) (φ c)) →
      SpC k S U n (∀ c, V c) (fun t y c => φ c t y) := by
  induction n with
  | zero =>
    intro V _ _ φ h
    exact contDiffOn_pi.2 fun c => h c
  | succ n ih =>
    intro V _ _ φ h
    refine ⟨contDiffOn_pi.2 fun c => (h c).1,
      fun t ht y hy => differentiableAt_pi.2 fun c => (h c).2.1 t ht y hy, ?_⟩
    have hp := ih (V := fun c => E →L[ℝ] V c) (φ := fun c t y => fderiv ℝ (φ c t) y)
      (fun c => (h c).2.2)
    let Θ : (∀ c, E →L[ℝ] V c) →L[ℝ] (E →L[ℝ] ∀ c, V c) :=
      ∑ c, (ContinuousLinearMap.compL ℝ E (V c) (∀ c, V c) (ContinuousLinearMap.single ℝ V c)).comp
        (ContinuousLinearMap.proj c)
    have hΘ : ∀ x : ∀ c, E →L[ℝ] V c, Θ x = ContinuousLinearMap.pi x := by
      intro x
      refine ContinuousLinearMap.ext fun v => ?_
      funext c'
      simp only [Θ, ContinuousLinearMap.sum_apply, ContinuousLinearMap.coe_comp',
        Function.comp_apply, ContinuousLinearMap.proj_apply, ContinuousLinearMap.compL_apply,
        ContinuousLinearMap.pi_apply, Finset.sum_apply]
      rw [Finset.sum_eq_single c']
      · simp
      · intro c _ hc
        simp [Pi.single_apply, hc.symm]
      · simp
    have hc := SpC.comp (k := k) hS hU (O := univ)
      (Ψ := fun q : ℝ × E × (∀ c, E →L[ℝ] V c) => Θ q.2.2) isOpen_univ
      (Θ.contDiff.comp (contDiff_snd.comp contDiff_snd)).contDiffOn (fun _ _ _ _ => trivial) hp
    refine SpC.congr hU n (fun t ht y hy => ?_) hc
    rw [fderiv_pi (fun c => (h c).2.1 t ht y hy), hΘ]

end SpatialReg

end ShortTime
