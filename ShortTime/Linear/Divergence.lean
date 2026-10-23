import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Metric.CometricDoubleTrace
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.IntegrationByParts.Divergence

/-!
# The divergence is the metric trace of the covariant derivative

`div V = tr₁₂ (∇V)` for `V ∈ Γ(T⁰_{s+1}M)`, with `tr₁₂` the operator field
`cometricDoubleTraceField`. Combined with DG's integration by parts
`⟨∇T, V⟩ = -⟨T, div V⟩` this gives `⟨T, tr₁₂ ∇V⟩ = -⟨∇T, V⟩`, which is how derivatives are moved
across coefficients in the energy estimates.

The identity is `covDivergence_eq_cometricDoubleTrace_apply_covGrad` in the DG library
(`Analysis/Elliptic/ConnectionLaplacian/Commutation/CovariantDivergence.lean`). That module pulls in
several hundred further modules, so the short proof is repeated here on top of the two modules it
actually needs.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Spectral DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Connection.Realization
open scoped Manifold ContDiff BigOperators

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-- The model value at `x` of a covariant tensor field, read off on the unit of `T⁰_0`. -/
def unitVal (g : SmoothRiemannianMetric I M) (s : ℕ) (W : SmoothCcTensor g 0 s) (x : M) :
    Tensor0SModel s ℝ E :=
  Tensor0SSpace.toModel
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from W.toSection x)
      (unitZeroSec (I := I) (M := M) x))

theorem zeroTensor_eq_smul_unitZeroSec (x : M) (D : Tensor0SSpace 0 I x) :
    D = (Tensor0SNabla.tensor0Iso I M x D) • unitZeroSec (I := I) (M := M) x := by
  have hunit :
      Tensor0SNabla.tensor0Iso I M x (unitZeroSec (I := I) (M := M) x) = (1 : ℝ) := by
    have h := Tensor0SNabla.scalarFn_unitZero (I := I) (M := M)
    exact congrFun h x
  apply (Tensor0SNabla.tensor0Iso I M x).injective
  rw [map_smul, hunit, smul_eq_mul, mul_one]

/-- Two covariant tensor fields agree if their values on the unit of `T⁰_0` agree. -/
theorem smoothCcTensor_ext_unitVal (g : SmoothRiemannianMetric I M) {s : ℕ}
    {S S' : SmoothCcTensor g 0 s}
    (h : ∀ x : M, unitVal g s S x = unitVal g s S' x) : S = S' := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  have hval : (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S.toSection x)
      (unitZeroSec (I := I) (M := M) x) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S'.toSection x)
        (unitZeroSec (I := I) (M := M) x) :=
    Tensor0SSpace.toModel_injective (h x)
  change (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S.toSection x) =
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S'.toSection x)
  refine ContinuousLinearMap.ext fun D => ?_
  rw [zeroTensor_eq_smul_unitZeroSec (I := I) (M := M) x D, map_smul, map_smul, hval]

theorem toModel_contractCovariant_eval (s : ℕ) (b : M) (v : TangentSpace I b)
    (A : TensorRSSpace 0 (s + 1) I b) (D : Tensor0SSpace 0 I b) (m : Fin s → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace s I b from
          contractCovariant 0 s b v A) D) m =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (s + 1) I b from A) D)
        (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) b v) m) := rfl

theorem unitVal_trace_apply (g : SmoothRiemannianMetric I M) (p : ℕ)
    (W : SmoothCcTensor g 0 (p + 2)) (x : M) (v : Fin p → E) :
    unitVal g p
        (operatorFieldApply (I := I) (M := M) g (p + 2) p (cometricDoubleTraceField (I := I) g p)
          W) x v =
      ∑ k : Fin (Module.finrank ℝ E),
        unitVal g (p + 2) W x
          (Fin.cons (cometricLmodel (I := I) g x
              (modelCovectorOfCLM (𝕜 := ℝ) (E := E) ((Module.finBasis ℝ E).cDualBasis k)))
            (Fin.cons ((Module.finBasis ℝ E) k) v)) := by
  rw [unitVal, operatorFieldApplication_toSection]
  rw [show ((show Tensor0SSpace (p + 2) I x →L[ℝ] Tensor0SSpace p I x from
        (cometricDoubleTraceField (I := I) g p).toSection x).comp
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (p + 2) I x from
          W.toSection x)) (unitZeroSec (I := I) (M := M) x) =
      (show Tensor0SSpace (p + 2) I x →L[ℝ] Tensor0SSpace p I x from
        (cometricDoubleTraceField (I := I) g p).toSection x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (p + 2) I x from
          W.toSection x) (unitZeroSec (I := I) (M := M) x)) from rfl]
  rw [cometricDoubleTraceField_toSection, cometricDoubleTraceFib_toModel,
    modelDoubleTrace_apply (E := E) p (cometricLmodel (I := I) g x)]
  rfl

/-- **`div V = tr₁₂ ∇V`.** -/
theorem covDivergence_eq_trace_covGrad (g : SmoothRiemannianMetric I M) (s : ℕ)
    (V : SmoothCcTensor g 0 (s + 1)) :
    covDivergence (I := I) (M := M) g s V =
      operatorFieldApply (I := I) (M := M) g (s + 2) s (cometricDoubleTraceField (I := I) g s)
        (covGrad (I := I) (M := M) g 0 (s + 1) V) := by
  refine smoothCcTensor_ext_unitVal g (fun x => ?_)
  refine ContinuousMultilinearMap.ext (fun v => ?_)
  rw [unitVal_trace_apply g s (covGrad (I := I) (M := M) g 0 (s + 1) V) x v]
  rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g (s := s) x
    (mem_smoothOrthoFrameNeighborhood_self (I := I) (M := M) x)
    (unitVal g (s + 2) (covGrad (I := I) (M := M) g 0 (s + 1) V) x) v]
  rw [unitVal]
  have hsec : (covDivergence (I := I) (M := M) g s V).toSection x =
      ∑ i : Fin (Module.finrank ℝ E),
        covDivergenceBilinear (I := I) (M := M) g s V x
          (smoothOrthoFrame (I := I) g x i x) (smoothOrthoFrame (I := I) g x i x) := by
    rw [covDivergence_toSection_apply]
    rfl
  rw [show
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        (covDivergence (I := I) (M := M) g s V).toSection x)
        (unitZeroSec (I := I) (M := M) x) =
      ∑ i : Fin (Module.finrank ℝ E),
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          covDivergenceBilinear (I := I) (M := M) g s V x
            (smoothOrthoFrame (I := I) g x i x) (smoothOrthoFrame (I := I) g x i x))
          (unitZeroSec (I := I) (M := M) x) from by
    rw [hsec, FunLike.coe_sum, Finset.sum_apply]]
  rw [← Tensor0SSpace.toModelL_apply (s := s) (x := x), map_sum (Tensor0SSpace.toModelL s x)]
  simp only [FunLike.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Tensor0SSpace.toModelL_apply]
  have hSmooth_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun z : M => TotalSpace.mk' E (E := fun w : M => TangentSpace I w) z
        (smoothOrthoFrame (I := I) g x i z)) x :=
    (smoothOrthoFrame_smooth (I := I) g x i).contMDiffAt.mdifferentiableAt (by simp)
  rw [codiffPsi_apply (I := I) (M := M) g s V x hSmooth_at hSmooth_at]
  rw [toModel_contractCovariant_eval (I := I) (M := M) s x
    (smoothOrthoFrame (I := I) g x i x)
    ((TensorRSNabla.tensorRSCovariantDerivative I M 0 (s + 1)
        (LeviCivita (I := I) g)).toFun (fun z : M => V.toSection z) x
      (smoothOrthoFrame (I := I) g x i x))
    (unitZeroSec (I := I) (M := M) x) v]
  rw [unitVal, covGrad_toSection_apply_eval]
  rfl

end ShortTime
