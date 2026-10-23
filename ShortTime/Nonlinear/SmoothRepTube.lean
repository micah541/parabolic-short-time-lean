import ShortTime.Nonlinear.FibreMapTame

/-!
# The tube in the domain, in chart coordinates (for non-smooth tuples)

`exists_euclTube`: around the chart readings `valFam α W` of a smooth reference tuple `W` with values
in the domain, there is an `ε > 0` such that *every* point `z` of the model fibre within `ε` of
`valFam α W (t, y)` (for `(t, y) ∈ [0,T] × closedBall`) lies in the open Euclidean domain `Wd` of
`FibreMap.exists_euclDom`. Unlike the tube clause of `exists_tame_pointwise` it is a statement about
points, not about smooth tuples, so it applies to the continuous representative of an element of
`𝒫^m`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set Filter Topology
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2
open scoped Manifold ContDiff

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

namespace FibreMap

variable {ι : Type*} [Fintype ι] {Λ : Type*} [NormedAddCommGroup Λ] [NormedSpace ℝ Λ]
  {b : ι → ℕ} {b' : ℕ} {g : SmoothRiemannianMetric I M}

theorem exists_euclTube (Φ : FibreMap I M Λ b b') (lam : Λ) {T : ℝ} (hTT : T ≤ Φ.T₀)
    {W : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c)}
    (hW : ∀ c, JointlySmoothOn g 0 (b c) (Icc 0 T) (W c))
    (hWdom : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, valAt (fun c => W c t) x ∈ Φ.dom lam t x)
    (α : M) {r : ℝ} (hball : Metric.closedBall (extChartAt I α α) r ⊆ (extChartAt I α).target) :
    ∃ Wd : Set ((ℝ × E) × ProdModel E b), IsOpen Wd ∧
      ContDiffOn ℝ ∞ (Φ.euclRep lam α) (((Icc 0 T ×ˢ (extChartAt I α).target) ×ˢ univ) ∩ Wd) ∧
      (∀ p ∈ ((Icc 0 T ×ˢ (extChartAt I α).target) ×ˢ univ) ∩ Wd,
        prodOfModel b α ((extChartAt I α).symm p.1.2) p.2 ∈
          Φ.dom lam p.1.1 ((extChartAt I α).symm p.1.2)) ∧
      ∃ ε > 0, ∀ t ∈ Icc (0 : ℝ) T, ∀ y ∈ Metric.closedBall (extChartAt I α α) r,
        ∀ z : ProdModel E b, ‖z - valFam α W (t, y)‖ ≤ ε → ((t, y), z) ∈ Wd := by
  obtain ⟨Wd, hWdo, hsmooth, hdomW, hinW⟩ := Φ.exists_euclDom lam α hTT
  have hUW := contDiffOn_valFam α hW
  set Gr := (fun q : ℝ × E => (q, valFam α W q)) ''
    (Icc 0 T ×ˢ Metric.closedBall (extChartAt I α α) r) with hGrdef
  have hGc : IsCompact Gr :=
    (isCompact_Icc.prod (isCompact_closedBall _ _)).image_of_continuousOn
      (continuousOn_id.prodMk (hUW.continuousOn.mono (prod_mono subset_rfl hball)))
  have hGW : Gr ⊆ Wd := by
    rintro _ ⟨q, hq, rfl⟩
    refine hinW q.1 hq.1 q.2 (hball hq.2) _ ?_
    rw [prodOfModel_valFam W (hball hq.2)]
    exact hWdom q.1 hq.1 _
  obtain ⟨ε, hε, hεW⟩ := hGc.exists_cthickening_subset_open hWdo hGW
  refine ⟨Wd, hWdo, hsmooth, hdomW, ε, hε, fun t ht y hy z hz => hεW ?_⟩
  refine Metric.mem_cthickening_of_dist_le _ ((t, y), valFam α W (t, y)) ε Gr
    ⟨(t, y), ⟨ht, hy⟩, rfl⟩ ?_
  rw [Prod.dist_eq, dist_self, dist_eq_norm]
  exact max_le hε.le hz

end FibreMap

end ShortTime
