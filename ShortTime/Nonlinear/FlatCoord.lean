import ShortTime.Nonlinear.FlatGrad
import ShortTime.Setting.Equation
import DifferentialGeometry.Bundle.ContinuousLinearMapSection.ParametricSmoothness
import DifferentialGeometry.Tensor.RSTensor.Coordinates.BundleBasis

/-!
# Lowering indices in local coordinates

Paper: Lemma `lem:lowering`, smoothness of `♭` and of the slot permutations.

* `contMDiffOn_flat_param`: `♭` is a smooth section of `Hom(T^r_s, T⁰_{r+s})` (with a dummy time
  parameter, as needed for jointly smooth families). It is smooth on smooth sections (`flatCc`),
  hence smooth (`contMDiffOn_clm_section_of_apply`).
* `contMDiffOn_flatCoord`: read in the trivializations at `x₀`, `♭` is a smooth function of the
  base point; so is its inverse (`contMDiffAt_flatCoord_inverse`).
* `trivAt_slotPerm`: slot permutations have constant coordinates `permModel e`.
-/

noncomputable section

open Bundle Manifold Set Filter
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-! ### Slot permutations in coordinates -/

section SlotPerm

/-- A model tensor of `T⁰_n` is determined by its value on the unit scalar. -/
theorem modelRS0_apply_eq {n : ℕ} (T : TensorRSModel 0 n ℝ E) (β : Tensor0SModel 0 ℝ E) :
    T β = scalar0M E β • T (unit0M E) := by
  conv_lhs => rw [eq_scalar0M_smul_unit0M β, map_smul]

theorem mem_trivAt_baseSet {r s : ℕ} {x₀ y : M}
    (hy : y ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    y ∈ (trivAt I M r s x₀).baseSet :=
  ⟨hy, hy⟩

/-- The `n`-form of a covariant tensor, read in the trivialization at `x₀`: the form composed with
the inverse chart map on each slot, times a factor `c` (the coordinate of the unit scalar), which
depends neither on the tensor nor on its rank. -/
theorem exists_unitEquiv_trivAt {x₀ y : M}
    (hy : y ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    ∃ c : ℝ, ∀ (n : ℕ) (W : TensorRSSpace 0 n I y),
      unitEquiv E n ((trivAt I M 0 n x₀).continuousLinearMapAt ℝ y W) =
        c • (unitEquiv E n (TensorRSSpace.toModel W)).compContinuousLinearMap
          (fun _ => (trivializationAt E (TangentSpace I) x₀).symmL ℝ y) := by
  let := tensor0SBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 0
  refine ⟨scalar0M E (Tensor0SSpace.toModel
    ((trivializationAt (Tensor0SModel 0 ℝ E) (fun x => Tensor0SSpace 0 I x) x₀).symmL ℝ y
      (unit0M E))), fun n W => ?_⟩
  refine ContinuousMultilinearMap.ext fun v => ?_
  rw [unitEquiv_apply, Trivialization.continuousLinearMapAt_apply,
    Trivialization.coe_linearMapAt_of_mem _ (mem_trivAt_baseSet hy)]
  erw [TensorRSSpace.trivializationAt_apply (𝕜 := ℝ) (I := I) (x₀ := x₀) (x := y) 0 n hy]
  rw [← Tensor0SSpace.toModel_apply, toModel_tensorRS_apply, modelRS0_apply_eq]
  rfl

/-- **Slot permutations have constant coordinates.** -/
theorem trivAt_slotPerm {a b : ℕ} (e : Fin a ≃ Fin b) {x₀ y : M}
    (hy : y ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) (W : TensorRSSpace 0 a I y) :
    (trivAt I M 0 b x₀).continuousLinearMapAt ℝ y (slotPerm I e y W) =
      permModel E e ((trivAt I M 0 a x₀).continuousLinearMapAt ℝ y W) := by
  obtain ⟨c, hc⟩ := exists_unitEquiv_trivAt (I := I) hy
  apply (unitEquiv E b).injective
  rw [unitEquiv_permModel, hc, hc, toModel_slotPerm, unitEquiv_permModel]
  rfl

end SlotPerm

/-! ### `♭` as a smooth bundle map -/

section FlatSmooth

variable (g : SmoothRiemannianMetric I M)

/-- `♭` is a smooth section of `Hom(T^r_s, T⁰_{r+s})`, constant in a dummy parameter. -/
theorem contMDiffOn_flat_param (r s : ℕ) (S : Set ℝ) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E →L[ℝ] TensorRSModel 0 (r + s) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E →L[ℝ] TensorRSModel 0 (r + s) ℝ E)
        (E := fun x : M => TensorRSSpace r s I x →L[ℝ] TensorRSSpace 0 (r + s) I x) p.1
        (flat g r s p.1 : TensorRSSpace r s I p.1 →L[ℝ] TensorRSSpace 0 (r + s) I p.1))
      ((Set.univ : Set M) ×ˢ S) := by
  apply contMDiffOn_clm_section_of_apply (I := I) (M := M)
    (F₁ := TensorRSModel r s ℝ E) (V₁ := fun x : M => TensorRSSpace r s I x)
    (F₂ := TensorRSModel 0 (r + s) ℝ E) (V₂ := fun x : M => TensorRSSpace 0 (r + s) I x)
    (φ := fun p : M × ℝ => (flat g r s p.1 : TensorRSSpace r s I p.1 →L[ℝ] TensorRSSpace 0 (r + s) I p.1))
    (S := S)
  intro Y
  have h := (flatCc g r s ⟨Y, HasCompactSupport.of_compactSpace _⟩).toSection.contMDiff.comp_contMDiffOn
    (contMDiffOn_fst : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞ (Prod.fst : M × ℝ → M)
      ((Set.univ : Set M) ×ˢ S))
  refine h.congr fun p _ => ?_
  simp only [Function.comp_apply]
  rw [flatCc_toSection]
  rfl

/-- `♭` read in the trivializations at `x₀`. -/
def flatCoord (r s : ℕ) (x₀ y : M) : TensorRSModel r s ℝ E →L[ℝ] TensorRSModel 0 (r + s) ℝ E :=
  ((trivAt I M 0 (r + s) x₀).continuousLinearMapAt ℝ y).comp
    ((flat g r s y : TensorRSSpace r s I y →L[ℝ] TensorRSSpace 0 (r + s) I y).comp
      ((trivAt I M r s x₀).symmL ℝ y))

theorem flatCoord_trivAt {r s : ℕ} {x₀ y : M} (hy : y ∈ (trivAt I M r s x₀).baseSet)
    (v : TensorRSSpace r s I y) :
    flatCoord g r s x₀ y ((trivAt I M r s x₀).continuousLinearMapAt ℝ y v) =
      (trivAt I M 0 (r + s) x₀).continuousLinearMapAt ℝ y (flat g r s y v) := by
  simp only [flatCoord, ContinuousLinearMap.comp_apply, Trivialization.symmL_continuousLinearMapAt _ hy]
  rfl

/-- **`♭` is smooth in coordinates.** -/
theorem contMDiffOn_flatCoord (r s : ℕ) (x₀ : M) :
    ContMDiffOn I 𝓘(ℝ, TensorRSModel r s ℝ E →L[ℝ] TensorRSModel 0 (r + s) ℝ E) ∞
      (flatCoord g r s x₀) ((trivAt I M r s x₀).baseSet ∩ (trivAt I M 0 (r + s) x₀).baseSet) := by
  have hp := contMDiffOn_flat_param g r s (Set.univ : Set ℝ)
  have hy : ContMDiff I (I.prod 𝓘(ℝ, ℝ)) ∞ (fun y : M => (y, (0 : ℝ))) :=
    contMDiff_id.prodMk contMDiff_const
  have h := hp.comp_contMDiff hy (fun _ => ⟨mem_univ _, mem_univ _⟩)
  have h' := h.contMDiffOn (s := (trivAt I M r s x₀).baseSet ∩ (trivAt I M 0 (r + s) x₀).baseSet)
  rw [(trivializationAt (TensorRSModel r s ℝ E →L[ℝ] TensorRSModel 0 (r + s) ℝ E)
      (fun x : M => TensorRSSpace r s I x →L[ℝ] TensorRSSpace 0 (r + s) I x) x₀).contMDiffOn_iff
    (fun y hy => by
      rw [hom_trivializationAt_source]
      exact hy)] at h'
  exact h'.2.congr fun y _ => rfl

variable [CompleteSpace E]

/-- `♭` in coordinates, as an equivalence. -/
def flatCoordEquiv (r s : ℕ) {x₀ y : M} (hr : y ∈ (trivAt I M r s x₀).baseSet)
    (h0 : y ∈ (trivAt I M 0 (r + s) x₀).baseSet) :
    TensorRSModel r s ℝ E ≃L[ℝ] TensorRSModel 0 (r + s) ℝ E :=
  (((trivAt I M r s x₀).continuousLinearEquivAt ℝ y hr).symm.trans (flat g r s y)).trans
    ((trivAt I M 0 (r + s) x₀).continuousLinearEquivAt ℝ y h0)

theorem flatCoordEquiv_coe (r s : ℕ) {x₀ y : M} (hr : y ∈ (trivAt I M r s x₀).baseSet)
    (h0 : y ∈ (trivAt I M 0 (r + s) x₀).baseSet) :
    (flatCoordEquiv g r s hr h0 : TensorRSModel r s ℝ E →L[ℝ] TensorRSModel 0 (r + s) ℝ E) =
      flatCoord g r s x₀ y := by
  refine ContinuousLinearMap.ext fun z => ?_
  change (trivAt I M 0 (r + s) x₀).continuousLinearEquivAt ℝ y h0
      (flat g r s y (((trivAt I M r s x₀).continuousLinearEquivAt ℝ y hr).symm z)) =
    flatCoord g r s x₀ y z
  rw [Trivialization.coe_continuousLinearEquivAt_eq, Trivialization.symm_continuousLinearEquivAt_eq]
  rfl

/-- **The inverse of `♭` (raising indices) is smooth in coordinates.** -/
theorem contMDiffAt_flatCoord_inverse (r s : ℕ) {x₀ y : M} (hr : y ∈ (trivAt I M r s x₀).baseSet)
    (h0 : y ∈ (trivAt I M 0 (r + s) x₀).baseSet) :
    ContMDiffAt I 𝓘(ℝ, TensorRSModel 0 (r + s) ℝ E →L[ℝ] TensorRSModel r s ℝ E) ∞
      (fun y => (flatCoord g r s x₀ y).inverse) y := by
  haveI : CompleteSpace (TensorRSModel r s ℝ E) := FiniteDimensional.complete ℝ _
  have hU : (trivAt I M r s x₀).baseSet ∩ (trivAt I M 0 (r + s) x₀).baseSet ∈ 𝓝 y :=
    ((trivAt I M r s x₀).open_baseSet.inter (trivAt I M 0 (r + s) x₀).open_baseSet).mem_nhds ⟨hr, h0⟩
  have hf := (contMDiffOn_flatCoord g r s x₀).contMDiffAt hU
  have hinv := (contDiffAt_map_inverse (n := ∞) (flatCoordEquiv g r s hr h0)).contMDiffAt
  rw [flatCoordEquiv_coe] at hinv
  exact hinv.comp y hf

end FlatSmooth

end ShortTime
