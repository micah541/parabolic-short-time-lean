import ShortTime.MM.SmoothF
import ShortTime.MM.SplitSum

/-!
# The Legendre-rearranged MM equation

Paper: `rem:rewrite`. For real jets `ζ = j^{2p}u`, the MM contraction of `∇^{2p}u` equals the split
contraction of `∇^{2p}u + Q(j^{2p-1}u)` (`mmPairing_eq_productCLM_add`), `Q` smooth and independent of
the top jet component. So `F'(ζ) = P_split(ζ_{2p} + Q(ζ_{<2p})) + b` has the same values as `F` on jets of
sections, and the principal coefficient of `F'` is the split pairing `P_split`, which satisfies the Legendre
condition.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Spectral DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Elliptic DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff BigOperators

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

/-- Forget the top component of a `2p`-jet. -/
def truncJet {p : ℕ} (x : M) (ζ : CovJetFiber I 0 0 (2 * p) x) : CovJetFiber I 0 0 (2 * p - 1) x :=
  fun k => ζ ⟨k.val, by have := k.isLt; omega⟩

/-- The top component of a `2p`-jet, as a `T⁰_{0+2p}`-tensor. -/
def jtop (p : ℕ) {x : M} (ζ : CovJetFiber I 0 0 (2 * p) x) : TensorRSSpace 0 (0 + 2 * p) I x :=
  ζ (Fin.last (2 * p))

theorem truncJet_covJet {p : ℕ} (g : SmoothRiemannianMetric I M) (u : SmoothCcTensor g 0 0) (x : M) :
    truncJet (p := p) x (covJet g 0 0 (2 * p) u x) = covJet g 0 0 (2 * p - 1) u x := rfl

variable (g : SmoothRiemannianMetric I M) (p : ℕ)

/-- The smooth lower-order Ricci correction `Q` of `rem:rewrite`. -/
def ricciQ : ∀ x : M, CovJetFiber I 0 0 (2 * p - 1) x → TensorRSSpace 0 (0 + 2 * p) I x :=
  (mmPairing_eq_productCLM_add g p (2 * p - 1) (by omega)).choose

theorem ricciQ_smooth : SmoothJetMap I M 0 (2 * p - 1) (0 + 2 * p) (ricciQ g p) :=
  (mmPairing_eq_productCLM_add g p (2 * p - 1) (by omega)).choose_spec.1

theorem ricciQ_spec (u : SmoothCcTensor g 0 0) (x : M)
    (Ef : Fin p → (TangentSpace I x →L[ℝ] ℝ) →ₗ[ℝ] (TangentSpace I x →L[ℝ] ℝ) →ₗ[ℝ] ℝ) :
    mmPairing g p x Ef ((iteratedCovGrad g 0 0 (2 * p) u).toSection x) =
      productCLM g 0 0 p x Ef
          (EquationData.castIdx (show 0 + 2 * p = 0 + p + p by omega) x
            ((iteratedCovGrad g 0 0 (2 * p) u).toSection x)) +
        productCLM g 0 0 p x Ef
          (EquationData.castIdx (show 0 + 2 * p = 0 + p + p by omega) x
            (ricciQ g p x (covJet g 0 0 (2 * p - 1) u x))) :=
  (mmPairing_eq_productCLM_add g p (2 * p - 1) (by omega)).choose_spec.2 u x Ef

variable {p} (d : MMData I M p)

/-- The rearranged right side `F'`. -/
def MMData.Frearr (t : ℝ) (x : M) (ζ : CovJetFiber I 0 0 (2 * p) x) : TensorRSSpace 0 0 I x :=
  productCLM g 0 0 p x (fun l => d.Ef l t x ζ)
      (EquationData.castIdx (show 0 + 2 * p = 0 + p + p by omega) x
        (jtop p ζ + ricciQ g p x (truncJet x ζ))) +
    d.b t x ζ

/-- **Same values on jets of sections** (`rem:rewrite`): `F'[u] = F[u]`. -/
theorem MMData.Frearr_covJet (u : SmoothCcTensor g 0 0) (t : ℝ) (x : M) :
    d.Frearr g t x (covJet g 0 0 (2 * p) u x) = d.F t x (covJet g 0 0 (2 * p) u x) := by
  have hF : frameSum p x (fun l => d.Ef l t x (covJet g 0 0 (2 * p) u x)) (stdFrame (I := I) x)
      (stdCoframe (I := I) x) (jtop p (covJet g 0 0 (2 * p) u x)) =
    mmPairing g p x (fun l => d.Ef l t x (covJet g 0 0 (2 * p) u x))
      ((iteratedCovGrad g 0 0 (2 * p) u).toSection x) := by
    rw [mmPairing_apply_eq_frameSum]
    exact frameSum_eq_frameSum p x _ _ _ _ _ (stdCoframe_stdFrame (I := I) x)
      (fun i j => coframe_apply g x i j) _
  have hF' : d.F t x (covJet g 0 0 (2 * p) u x) =
      frameSum p x (fun l => d.Ef l t x (covJet g 0 0 (2 * p) u x)) (stdFrame (I := I) x)
        (stdCoframe (I := I) x) (jtop p (covJet g 0 0 (2 * p) u x)) +
      d.b t x (covJet g 0 0 (2 * p) u x) := rfl
  rw [hF', hF, MMData.Frearr, ricciQ_spec, map_add, map_add]
  rfl

end ShortTime
