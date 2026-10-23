import ShortTime.Linear.RicciPerm
import DifferentialGeometry.Geometry.Curvature.RoughLaplacian.Commutator.HomFieldJetDecomposition
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorField.Bounds.HomFieldActionJets
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Iterated.Linear

/-!
# The Ricci identity for one transposition (`lem:ricci`)

Swapping two adjacent slots of `∇^k ∇² W` (the two slots created by `∇²`) changes it only by
`∇^k (R W)`, where `R` is a zeroth-order curvature term. This is the library's Ricci identity
`exists_secondCovGrad_swap_ricciDefect_homField`, transported through `∇^k` by the explicit
naturality of `ShortTime.Linear.RicciPerm`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff BigOperators

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

/-- Swapping the first two arguments, written with `Fin.cons`. -/
theorem comp_swap_zero_one {t : ℕ} {α : Type*} (v : Fin (t + 2) → α) :
    (fun i => v (Equiv.swap (0 : Fin (t + 2)) 1 i)) =
      Fin.cons (v 1) (Fin.cons (v 0) (fun j : Fin t => v j.succ.succ)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · refine Fin.cases ?_ (fun k => ?_) j
    · simp
    · rw [Fin.cons_succ, Fin.cons_succ, Equiv.swap_apply_of_ne_of_ne]
      · exact Fin.succ_ne_zero _
      · intro h
        have := congrArg Fin.val h
        simp at this

theorem eq_cons_cons {t : ℕ} {α : Type*} (v : Fin (t + 2) → α) :
    v = Fin.cons (v 0) (Fin.cons (v 1) (fun j : Fin t => v j.succ.succ)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · refine Fin.cases ?_ (fun k => ?_) j
    · simp
    · simp

/-- **Ricci identity, one transposition.** There is a zeroth-order field `R` such that for every
`W`, swapping slots `k, k+1` of `∇^k ∇² W` changes it by `∇^k (R W)`. -/
theorem exists_swap_defect (g : SmoothRiemannianMetric I M) (t : ℕ) :
    ∃ R : HomTensorRSField (E := E) (M := M) 0 t (t + 2) I,
      ∀ (W : SmoothCcTensor g 0 t) (k : ℕ) (x : M) (d : Tensor0SSpace 0 I x),
        Tensor0SSpace.toModel
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (t + 2 + k) I x from
              (iteratedCovGrad g 0 (t + 2) k (iteratedCovGrad g 0 t 2 W)).toSection x) d) -
          ContinuousMultilinearMap.domDomCongr (liftPerm (Equiv.swap (0 : Fin (t + 2)) 1) k)
            (Tensor0SSpace.toModel
              ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (t + 2 + k) I x from
                (iteratedCovGrad g 0 (t + 2) k (iteratedCovGrad g 0 t 2 W)).toSection x) d)) =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (t + 2 + k) I x from
            (iteratedCovGrad g 0 (t + 2) k
              (homTensorRSFieldApply (I := I) (M := M) g 0 t (t + 2) R W)).toSection x) d) := by
  obtain ⟨F, R, hF, hFR⟩ := exists_secondCovGrad_swap_ricciDefect_homField (I := I) g 0 t
  refine ⟨R, fun W k x d => ?_⟩
  set Φ := iteratedCovGrad g 0 t 2 W with hΦdef
  set Φ' := homTensorRSFieldApply (I := I) (M := M) g 0 (t + 2) (t + 2) F Φ with hΦ'def
  have hrel : ∀ (y : M) (d : Tensor0SSpace 0 I y),
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (t + 2) I y from Φ'.toSection y) d) =
        ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin (t + 2)) 1)
          (Tensor0SSpace.toModel
            ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (t + 2) I y from Φ.toSection y) d)) := by
    intro y d
    apply ContinuousMultilinearMap.ext
    intro v
    rw [ContinuousMultilinearMap.domDomCongr_apply, comp_swap_zero_one]
    conv_lhs => rw [eq_cons_cons v]
    exact hF y (Φ.toSection y) d (v 0) (v 1) (fun j => v j.succ.succ)
  have hnat := toModel_iteratedCovGrad_domDomCongr g 0 (t + 2) (Equiv.swap (0 : Fin (t + 2)) 1)
    Φ Φ' hrel k x d
  have hsplit : iteratedCovGrad g 0 (t + 2) k Φ =
      iteratedCovGrad g 0 (t + 2) k Φ' +
        iteratedCovGrad g 0 (t + 2) k (homTensorRSFieldApply (I := I) (M := M) g 0 t (t + 2) R W) := by
    rw [← iteratedCovGrad_add]
    exact congrArg _ (hFR W)
  rw [← hnat]
  conv_lhs => rw [hsplit]
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]
  change Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (t + 2 + k) I x from
        (iteratedCovGrad g 0 (t + 2) k Φ').toSection x) d +
       (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (t + 2 + k) I x from
        (iteratedCovGrad g 0 (t + 2) k
          (homTensorRSFieldApply (I := I) (M := M) g 0 t (t + 2) R W)).toSection x) d) - _ = _
  rw [Tensor0SSpace.toModel_add]
  abel

end ShortTime
