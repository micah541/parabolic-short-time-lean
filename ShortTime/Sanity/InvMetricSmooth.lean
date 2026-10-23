import ShortTime.MM.Main
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import DifferentialGeometry.Geometry.Coordinates.MetricCompatibility.Inverse

/-!
# Smoothness of the inverse metric in a fixed coordinate frame, on the whole frame set

The library proves `gInvComp_contMDiffAt` at the centre `x₀` of the chart only. The inverse-metric
components `g^{ij}` of the coordinate frame at `x₀` are smooth at every point of the frame set
`coordinateFrameSet x₀`; this is the proof of the library with the centre replaced by an arbitrary
point of the frame set. Used for the non-vacuity instance `MMData.polyharmonic`.
-/

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace ShortTime

open DifferentialGeometry DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The matrix of `g` in the coordinate frame at `x₀` is smooth in the chart at every point of the
frame set. -/
theorem metricFlatModelInChart_contDiffWithinAt_at
    (g : SmoothRiemannianMetric I M) (x₀ : M) {x₁ : M}
    (hx : x₁ ∈ coordinateFrameSet (I := I) x₀) :
    ContDiffWithinAt ℝ ∞ (metricFlatModelInChart (I := I) g x₀)
      (Set.range I) (extChartAt I x₀ x₁) := by
  have hxT : x₁ ∈ (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet := by
    simpa [coordinateFrameSet, coordinateTrivializationAt] using hx
  have hx_source : x₁ ∈ (extChartAt I x₀).source := by
    simpa [coordinateFrameSet, coordinateTrivializationAt, extChartAt_source] using hx
  let e := trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
      (fun p : M => TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ) x₀
  have hxe : x₁ ∈ e.baseSet := by
    show x₁ ∈ (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
      (fun p : M => TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ) x₀).baseSet
    rw [hom_trivializationAt_baseSet]
    refine ⟨hxT, ?_⟩
    rw [hom_trivializationAt_baseSet]
    exact ⟨hxT, by simp⟩
  have hgOn : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : M => (⟨p, g.inner p⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun p : M => TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ))) e.baseSet :=
    g.contMDiff.contMDiffOn
  have hcoordOn := ((Trivialization.contMDiffOn_iff (IM := I) (e := e)
    (f := fun p : M => (⟨p, g.inner p⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun p : M => TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ))) (s := e.baseSet)
    (fun y hy => e.mem_source.mpr hy)).1 hgOn).2
  have hcoord : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun p : M => (e ⟨p, g.inner p⟩).2) x₁ :=
    hcoordOn.contMDiffAt (e.open_baseSet.mem_nhds hxe)
  have hsymm : ContMDiffWithinAt 𝓘(ℝ, E) I ∞ (extChartAt I x₀).symm
      (Set.range I) (extChartAt I x₀ x₁) :=
    contMDiffWithinAt_extChartAt_symm_range (I := I) x₀ ((extChartAt I x₀).map_source hx_source)
  have hleft : (extChartAt I x₀).symm (extChartAt I x₀ x₁) = x₁ :=
    (extChartAt I x₀).left_inv hx_source
  have hcoord' : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun p : M => (e ⟨p, g.inner p⟩).2) ((extChartAt I x₀).symm (extChartAt I x₀ x₁)) := by
    rw [hleft]; exact hcoord
  exact (hcoord'.comp_contMDiffWithinAt (x := extChartAt I x₀ x₁) hsymm).contDiffWithinAt

theorem inverseMetricFlatModelInChart_component_contDiffWithinAt_at [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x₀ : M) {x₁ : M}
    (hx : x₁ ∈ coordinateFrameSet (I := I) x₀) (k l : CoordinateIdx (𝕜 := ℝ) E) :
    ContDiffWithinAt ℝ ∞
      (inverseMetricFlatModelInChartComponent (I := I) g x₀ k l)
      (Set.range I) (extChartAt I x₀ x₁) := by
  let εl : E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord l)
  let εk : E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord k)
  have hinv : ContDiffWithinAt ℝ ∞
      (fun y : E => ContinuousLinearMap.inverse (metricFlatModelInChart (I := I) g x₀ y))
      (Set.range I) (extChartAt I x₀ x₁) :=
    (flatChart_inv (I := I) g x₀ hx).contDiffAt_map_inverse.comp_contDiffWithinAt
      (x := extChartAt I x₀ x₁) (metricFlatModelInChart_contDiffWithinAt_at (I := I) g x₀ hx)
  have happ : ContDiffWithinAt ℝ ∞
      (fun y : E => (ContinuousLinearMap.inverse (metricFlatModelInChart (I := I) g x₀ y)) εl)
      (Set.range I) (extChartAt I x₀ x₁) := by
    simpa [εl] using hinv.clm_apply contDiffWithinAt_const
  unfold inverseMetricFlatModelInChartComponent
  exact (contDiffWithinAt_const (c := εk)).clm_apply happ

/-- The inverse-metric components in the coordinate frame at `x₀` are smooth at every point of the
frame set. -/
theorem gInvComp_contMDiffAt_at [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x₀ : M) {x₁ : M}
    (hx : x₁ ∈ coordinateFrameSet (I := I) x₀) (k l : CoordinateIdx (𝕜 := ℝ) E) :
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun y : M => inverseMetricFlatModelInChartComponent (I := I) g x₀ k l
        (extChartAt I x₀ y)) x₁ := by
  have hx_source : x₁ ∈ (extChartAt I x₀).source := by
    simpa [coordinateFrameSet, coordinateTrivializationAt, extChartAt_source] using hx
  let f : E → ℝ := inverseMetricFlatModelInChartComponent (I := I) g x₀ k l
  have hf : ContDiffWithinAt ℝ ∞ f (Set.range I) (extChartAt I x₀ x₁) :=
    inverseMetricFlatModelInChart_component_contDiffWithinAt_at (I := I) g x₀ hx k l
  have hchart : ContMDiffWithinAt I 𝓘(ℝ, E) ∞ (extChartAt I x₀)
      (extChartAt I x₀).source x₁ :=
    (contMDiffAt_extChartAt' (I := I) (x := x₀) (x' := x₁)
      (by rwa [extChartAt_source] at hx_source)).contMDiffWithinAt
  have hcomp : ContMDiffWithinAt I 𝓘(ℝ, ℝ) ∞ (f ∘ extChartAt I x₀)
      (extChartAt I x₀).source x₁ :=
    hf.comp_contMDiffWithinAt hchart (by
      intro y hy
      exact extChartAt_target_subset_range x₀ ((extChartAt I x₀).map_source hy))
  have hcompAt : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (f ∘ extChartAt I x₀) x₁ :=
    hcomp.contMDiffAt ((isOpen_extChartAt_source (I := I) x₀).mem_nhds hx_source)
  simpa [f, Function.comp_def] using hcompAt

end ShortTime
