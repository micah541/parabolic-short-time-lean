import ShortTime.MM.Data
import ShortTime.Sanity.TraceSmooth

/-!
# The MM contraction in the trivialisations at `x₀`

`evalFirst_inCoords`: evaluating the first `q` slots of `(trivAt x₀).symm z` on the coordinate frame
and reading the result in the trivialisation at `x₀` gives `z` evaluated on the model vectors.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Analysis.Sobolev
open scoped Manifold ContDiff BigOperators

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

theorem evalFirst_inCoords (x₀ y : M) (q : ℕ)
    (hy : y ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (hx0 : y ∈ (trivAt I M 0 0 x₀).baseSet) (hxq : y ∈ (trivAt I M 0 (0 + q) x₀).baseSet)
    (w : Fin q → E)
    (z : TensorRSModel 0 (0 + q) ℝ E) (β : Tensor0SModel 0 ℝ E) (v : Fin 0 → E) :
    ((trivAt I M 0 0 x₀).continuousLinearMapAt ℝ y
      (evalFirst (r := 0) (s := 0) q
        (fun i => (trivializationAt E (TangentSpace I) x₀).symmL ℝ y (w i))
        ((trivAt I M 0 (0 + q) x₀).symmL ℝ y z))) β v = z β (appendIdx w v) := by
  rw [Trivialization.continuousLinearMapAt_apply, Trivialization.coe_linearMapAt_of_mem _ hx0]
  rw [TensorRSSpace.trivializationAt_apply (𝕜 := ℝ) (I := I) (x₀ := x₀) (x := y) 0 0 hy]
  have hv : (fun a : Fin 0 => (trivializationAt E (TangentSpace I) x₀).symmL ℝ y (v a)) =
      fun i => (tangentSpaceModelContinuousLinearEquiv (I := I) y).symm (v i) :=
    funext fun a => a.elim0
  have hz : z = ((trivAt I M 0 (0 + q) x₀)
      ⟨y, (trivAt I M 0 (0 + q) x₀).symmL ℝ y z⟩).2 := by
    rw [Trivialization.symmL_apply _ hxq, Trivialization.apply_mk_symm _ hxq]
  rw [hv, ← Tensor0SSpace.toModel_apply_model_vector, evalFirst_toModel]
  conv_rhs => rw [hz]
  rw [TensorRSSpace.trivializationAt_apply (𝕜 := ℝ) (I := I) (x₀ := x₀) (x := y) 0 (0 + q) hy,
    ← Tensor0SSpace.toModel_apply, Tensor0SSpace.toModel_apply]
  refine (Tensor0SSpace.toModel_apply _ _).trans ?_
  congr 1
  funext a
  have ha := a.isLt
  simp only [appendIdx]
  split_ifs with h
  · rfl
  · exfalso; omega

end ShortTime
