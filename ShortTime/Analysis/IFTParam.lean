import Mathlib

/-!
# A parametric inverse function theorem (for `cor:C`)

If `A : X →L Y` is continuous linear, `𝒩 : X → Y` is `C¹` at `W` with `A W = 𝒩 W`, and
`A - D𝒩(W)` restricts to an isomorphism `Z ≃L Y` on a complete subspace `Z ⊆ X`, then for every
`ε > 0` there is `ρ > 0` such that for every `ζ ∈ X` with `‖ζ‖ < ρ` the equation
`A (W + ζ + v) = 𝒩 (W + ζ + v)` has a solution `v ∈ Z` with `‖v‖ < ε`.

The proof applies the inverse function theorem to `(ζ, v) ↦ (ζ, A(W + ζ + v) - 𝒩(W + ζ + v))`.
-/

noncomputable section

open Set Filter Topology Metric

namespace ShortTime

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y]
  [NormedSpace ℝ Y] [CompleteSpace Y]

theorem exists_solution_param (Z : Submodule ℝ X) [CompleteSpace Z] (A : X →L[ℝ] Y)
    (𝒩 : X → Y) (W : X) (h𝒩 : ContDiffAt ℝ 1 𝒩 W) (hW : A W = 𝒩 W) (Φ : Z ≃L[ℝ] Y)
    (hΦ : ∀ z : Z, Φ z = A z - fderiv ℝ 𝒩 W z) :
    ∀ ε > 0, ∃ ρ > 0, ∀ ζ : X, ‖ζ‖ < ρ → ∃ v : Z, ‖v‖ < ε ∧
      A (W + ζ + (v : X)) = 𝒩 (W + ζ + (v : X)) := by
  intro ε hε
  set a : X × Z → X := fun q => W + q.1 + (q.2 : X) with ha
  set F : X × Z → X × Y := fun q => (q.1, A (a q) - 𝒩 (a q)) with hF
  have h0 : a (0, 0) = W := by simp [ha]
  have haff : HasFDerivAt a ((ContinuousLinearMap.fst ℝ X Z) +
      Z.subtypeL.comp (ContinuousLinearMap.snd ℝ X Z)) (0, 0) := by
    have h1 : HasFDerivAt (fun q : X × Z => q.1) (ContinuousLinearMap.fst ℝ X Z) (0, 0) :=
      (ContinuousLinearMap.fst ℝ X Z).hasFDerivAt
    have h2 : HasFDerivAt (fun q : X × Z => (q.2 : X))
        (Z.subtypeL.comp (ContinuousLinearMap.snd ℝ X Z)) (0, 0) :=
      (Z.subtypeL.comp (ContinuousLinearMap.snd ℝ X Z)).hasFDerivAt
    exact (h1.const_add W).add h2
  have hac : ContDiffAt ℝ 1 a (0, 0) :=
    (contDiffAt_const.add (contDiff_fst.contDiffAt)).add
      (Z.subtypeL.contDiff.contDiffAt.comp (0, 0) contDiff_snd.contDiffAt)
  have h𝒩' : ContDiffAt ℝ 1 𝒩 (a (0, 0)) := by rw [h0]; exact h𝒩
  have hd𝒩 : HasFDerivAt 𝒩 (fderiv ℝ 𝒩 W) (a (0, 0)) := by
    rw [h0]; exact (h𝒩.differentiableAt one_ne_zero).hasFDerivAt
  set L : X × Z →L[ℝ] X := (ContinuousLinearMap.fst ℝ X Z) +
      Z.subtypeL.comp (ContinuousLinearMap.snd ℝ X Z) with hL
  have hG : HasFDerivAt (fun q => A (a q) - 𝒩 (a q))
      (A.comp L - (fderiv ℝ 𝒩 W).comp L) (0, 0) :=
    (A.hasFDerivAt.comp (0, 0) haff).sub (hd𝒩.comp (0, 0) haff)
  have hFd : HasFDerivAt F ((ContinuousLinearMap.fst ℝ X Z).prod
      (A.comp L - (fderiv ℝ 𝒩 W).comp L)) (0, 0) :=
    (ContinuousLinearMap.fst ℝ X Z).hasFDerivAt.prodMk hG
  have hFc : ContDiffAt ℝ 1 F (0, 0) :=
    contDiff_fst.contDiffAt.prodMk
      ((A.contDiff.contDiffAt.comp (0, 0) hac).sub (h𝒩'.comp (0, 0) hac))
  -- the derivative is an isomorphism
  set D : X →L[ℝ] Y := A - fderiv ℝ 𝒩 W with hD
  set e : (X × Z) ≃L[ℝ] (X × Y) := ContinuousLinearEquiv.skewProd (ContinuousLinearEquiv.refl ℝ X) Φ D
    with he
  have hfe : ((ContinuousLinearMap.fst ℝ X Z).prod
      (A.comp L - (fderiv ℝ 𝒩 W).comp L)) = (e : X × Z →L[ℝ] X × Y) := by
    refine ContinuousLinearMap.ext fun q => Prod.ext ?_ ?_
    · simp [he, ContinuousLinearEquiv.skewProd_apply]
    · simp [he, ContinuousLinearEquiv.skewProd_apply, hL, hD, hΦ]
      abel
  have hs : HasStrictFDerivAt F (e : X × Z →L[ℝ] X × Y) (0, 0) := by
    rw [← hfe]
    exact hFc.hasStrictFDerivAt' hFd one_ne_zero
  have hF0 : F (0, 0) = (0, 0) := by
    simp only [hF, h0, hW, sub_self]
  -- the image of a small box
  have hbox : {q : X × Z | ‖q.1‖ < ε ∧ ‖q.2‖ < ε} ∈ 𝓝 ((0 : X), (0 : Z)) := by
    refine (isOpen_lt (continuous_norm.comp continuous_fst) continuous_const).inter
      (isOpen_lt (continuous_norm.comp continuous_snd) continuous_const) |>.mem_nhds ?_
    simp [hε]
  have himg : F '' {q : X × Z | ‖q.1‖ < ε ∧ ‖q.2‖ < ε} ∈ 𝓝 ((0 : X), (0 : Y)) := by
    have h : F '' _ ∈ Filter.map F (𝓝 ((0 : X), (0 : Z))) := image_mem_map hbox
    rw [hs.map_nhds_eq_of_equiv, hF0] at h
    exact h
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp himg
  refine ⟨ρ, hρ, fun ζ hζ => ?_⟩
  have hmem : ((ζ, (0 : Y)) : X × Y) ∈ Metric.ball ((0 : X), (0 : Y)) ρ := by
    rw [Metric.mem_ball, Prod.dist_eq, dist_zero_right, dist_zero_right]
    exact max_lt hζ (by simpa using hρ)
  obtain ⟨q, ⟨hq1, hq2⟩, hqe⟩ := hball hmem
  have h1 : q.1 = ζ := congrArg Prod.fst hqe
  have h2 : A (a q) - 𝒩 (a q) = 0 := congrArg Prod.snd hqe
  refine ⟨q.2, hq2, ?_⟩
  have : a q = W + ζ + (q.2 : X) := by simp [ha, h1]
  rw [← this]
  exact sub_eq_zero.mp h2

end ShortTime
