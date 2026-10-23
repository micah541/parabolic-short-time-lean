import ShortTime.Sanity.InvMetricSmooth

/-!
# Non-vacuity of the Mantegazza–Martinazzi theorem: the polyharmonic flow

`MMData.polyharmonic g p` is the MM data with `E_ℓ = g⁻¹` for every `ℓ`, `b = 0`, `T₀ = 1` and
domain the whole jet space. The equation is the polyharmonic heat flow
`∂ₜu = (-1)^{p+1} Σ_I ∇^{2p}_{I I} u`. It shows that the hypotheses of `mantegazza_martinazzi` can
be satisfied on every closed Riemannian manifold, so the theorem is not vacuous.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set Filter
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff BigOperators Topology

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

/-- The inverse metric `g⁻¹` as a bilinear form on covectors: `(ξ, η) ↦ g(ξ♯, η♯)`. -/
def invMetricForm (g : SmoothRiemannianMetric I M) (x : M) :
    (TangentSpace I x →L[ℝ] ℝ) →ₗ[ℝ] (TangentSpace I x →L[ℝ] ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun ξ η => g.inner x (metricSharp (I := I) g x ξ.toLinearMap)
      (metricSharp (I := I) g x η.toLinearMap))
    (fun ξ ξ' η => by simp [metricSharp_def])
    (fun c ξ η => by simp [metricSharp_def])
    (fun ξ η η' => by simp [metricSharp_def])
    (fun c ξ η => by simp [metricSharp_def])

theorem invMetricForm_apply (g : SmoothRiemannianMetric I M) (x : M)
    (ξ η : TangentSpace I x →L[ℝ] ℝ) :
    invMetricForm g x ξ η =
      g.inner x (metricSharp (I := I) g x ξ.toLinearMap) (metricSharp (I := I) g x η.toLinearMap) :=
  rfl

theorem invMetricForm_symm (g : SmoothRiemannianMetric I M) (x : M)
    (ξ η : TangentSpace I x →L[ℝ] ℝ) : invMetricForm g x ξ η = invMetricForm g x η ξ := by
  rw [invMetricForm_apply, invMetricForm_apply]; exact g.symm x _ _

theorem invMetricForm_pos (g : SmoothRiemannianMetric I M) (x : M)
    {ξ : TangentSpace I x →L[ℝ] ℝ} (hξ : ξ ≠ 0) : 0 < invMetricForm g x ξ ξ := by
  rw [invMetricForm_apply]
  refine g.pos x _ fun h => hξ ?_
  ext w
  have := inner_metricSharp (I := I) g x ξ.toLinearMap w
  rw [h] at this
  simpa using this.symm

theorem coordinateFrameAt_eq_coordFrame (x₀ : M) {y : M}
    (hy : y ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) (j : Fin (Module.finrank ℝ E)) :
    coordinateFrameAt (I := I) x₀ j y = coordFrame (I := I) x₀ y j := by
  simp only [coordinateFrameAt, coordinateTrivializationAt, Trivialization.localFrame]
  rw [dif_pos hy, coordFrame, Trivialization.symmL_apply _ hy]
  simp [Trivialization.basisAt]

/-- In the coordinate coframe at `x₀`, the inverse metric has the components of the library's
`inverseMetricFlatModelInChartComponent`, on the whole frame set. -/
theorem invMetricForm_coordCoframe (g : SmoothRiemannianMetric I M) (x₀ : M) {y : M}
    (hy : y ∈ coordinateFrameSet (I := I) x₀) (i j : Fin (Module.finrank ℝ E)) :
    invMetricForm g y (coordCoframe (I := I) x₀ y i) (coordCoframe (I := I) x₀ y j) =
      inverseMetricFlatModelInChartComponent (I := I) g x₀ i j (extChartAt I x₀ y) := by
  classical
  have hyT : y ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
    simpa [coordinateFrameSet, coordinateTrivializationAt] using hy
  set B := coordinateFrameAtBasis (I := I) x₀ hy with hB
  set G : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun k l => inverseMetricFlatModelInChartComponent (I := I) g x₀ k l (extChartAt I x₀ y) with hG
  have hGB : MetricInverseInBasis (I := I) g y B G := gInvBasisAt (I := I) g x₀ hy
  have hBj : ∀ j, B j = coordFrame (I := I) x₀ y j := fun j => by
    simp only [hB, coordinateFrameAt_basis_apply]
    exact coordinateFrameAt_eq_coordFrame (I := I) x₀ hyT j
  let v : Fin (Module.finrank ℝ E) → TangentSpace I y := fun i => ∑ k, G i k • B k
  have hvB : ∀ i j, g.inner y (v i) (B j) = if i = j then 1 else 0 := fun i j => by
    simp only [v, map_sum, map_smul, sum_apply,
      smul_apply, smul_eq_mul]
    exact (hGB i j).1
  have hsharp : ∀ i, metricSharp (I := I) g y (coordCoframe (I := I) x₀ y i).toLinearMap = v i := by
    intro i
    by_contra hne
    set d := metricSharp (I := I) g y (coordCoframe (I := I) x₀ y i).toLinearMap - v i with hd
    have hd0 : ∀ w, g.inner y d w = 0 := by
      have : (g.inner y d).toLinearMap = 0 := by
        refine B.ext fun j => ?_
        simp only [hd, map_sub, sub_apply, LinearMap.zero_apply,
          ContinuousLinearMap.coe_coe]
        rw [inner_metricSharp, hvB, hBj j]
        simp only [ContinuousLinearMap.coe_coe]
        rw [coordCoframe_coordFrame (I := I) x₀ y hyT]
        simp
      intro w
      exact congrArg (fun L => L w) this
    exact (sub_ne_zero.2 hne) (by
      by_contra hne'
      have := g.pos y d hne'
      rw [hd0 d] at this
      exact lt_irrefl _ this)
  rw [invMetricForm_apply, hsharp, hsharp]
  have h1 : g.inner y (v i) (v j) = ∑ k, G i k * g.inner y (B k) (v j) := by
    change g.inner y (∑ k, G i k • B k) (v j) = _
    rw [map_sum (g.inner y) (fun k => G i k • B k) Finset.univ, sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, smul_apply, smul_eq_mul]
  have h2 : ∀ k, g.inner y (B k) (v j) = if j = k then 1 else 0 := fun k => by
    rw [g.symm y]; exact hvB j k
  rw [h1]
  simp only [h2, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  simp [hG]

/-- **The polyharmonic MM data**: `E_ℓ = g⁻¹` for all `ℓ`, `b = 0`, `T₀ = 1`, domain the whole jet
space. The equation is `∂ₜu = (-1)^{p+1} Σ_I ∇^{2p}_{II} u` (the polyharmonic heat flow). -/
def MMData.polyharmonic (g : SmoothRiemannianMetric I M) (p : ℕ) : MMData I M p where
  T₀ := 1
  T₀_pos := one_pos
  dom := fun _ _ => Set.univ
  Ef := fun _ _ x _ => invMetricForm g x
  b := fun _ _ _ => 0
  dom_relOpen := fun x₀ => ⟨Set.univ, isOpen_univ, by ext q; simp [localDom]⟩
  Ef_lower := fun _ _ _ _ _ _ => rfl
  b_lower := fun _ _ _ _ _ => rfl
  Ef_symm := fun _ _ x _ ξ η => invMetricForm_symm g x ξ η
  Ef_pos := fun _ _ x _ _ _ ξ hξ => invMetricForm_pos g x hξ
  Ef_smooth := fun x₀ l i j => by
    have hset : ∀ q ∈ localDom (I := I) 0 0 (2 * p) 1 (fun _ _ => Set.univ) x₀,
        q.2.1 ∈ coordinateFrameSet (I := I) x₀ := fun q hq => by
      have h := tangent_mem_of_trivAt (I := I) x₀ q.2.1 0 0 hq.1.2.1
      simpa [coordinateFrameSet, coordinateTrivializationAt] using h
    have hcomp : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun y : M => inverseMetricFlatModelInChartComponent (I := I) g x₀ i j
          (extChartAt I x₀ y)) (coordinateFrameSet (I := I) x₀) :=
      fun y hy => (gInvComp_contMDiffAt_at (I := I) g x₀ hy i j).contMDiffWithinAt
    have hproj : ContMDiff (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, JetModel E 0 0 (2 * p)))) I ∞
        (fun q : ℝ × M × JetModel E 0 0 (2 * p) => q.2.1) :=
      contMDiff_fst.comp contMDiff_snd
    exact (hcomp.comp hproj.contMDiffOn hset).congr fun q hq =>
      invMetricForm_coordCoframe g x₀ (hset q hq) i j
  b_smooth := fun x₀ => by
    have : localRep (I := I) 0 0 (2 * p)
        (fun (_ : ℝ) (x : M) (_ : CovJetFiber I 0 0 (2 * p) x) => (0 : TensorRSSpace 0 0 I x)) x₀ =
        fun _ => 0 := by
      funext q; simp [localRep]
    simp only [this]
    exact contMDiffOn_const

/-- **Non-vacuity of the Mantegazza–Martinazzi theorem.** On every closed Riemannian manifold, every
smooth initial datum has a smooth solution of the polyharmonic heat flow for short time; uniqueness
and continuous dependence hold by `mantegazza_martinazzi`. -/
theorem polyharmonic_short_time {p : ℕ} (hp : 1 ≤ p) (g : SmoothRiemannianMetric I M)
    (u₀ : SmoothCcTensor g 0 0) :
    ∃ T > 0, ∃ u : ℝ → SmoothCcTensor g 0 0,
      (MMData.polyharmonic g p).toEquationData.IsSolution g u₀ T u :=
  (mantegazza_martinazzi (MMData.polyharmonic g p) hp g).1 u₀ fun _ => Set.mem_univ _

end ShortTime
