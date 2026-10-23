import ShortTime.Nonlinear.FlatLegendre

/-!
# Reduction to covariant tensor bundles

Lowering all indices with the metric identifies `T^r_s M` with `T⁰_{r+s} M` by a parallel fibrewise
isometry. It carries equation data on `T^r_s` to equation data on `T⁰_{r+s}`, (parabolic) solutions
to (parabolic) solutions, and the Legendre condition to the Legendre condition. Hence each main
theorem follows from its case `r = 0`, where the linear theory of `ShortTime.Linear` applies.

The ingredients are in `Flat.lean` (the fibrewise isometry `♭`), `FlatGrad.lean` (`♭` commutes with
covariant jets), `FlatData.lean` (the lowered equation `D^♭`) and `FlatLegendre.lean` (parabolicity).
-/

noncomputable section

open Bundle Manifold Set
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Analysis.Sobolev
open scoped Manifold ContDiff

set_option linter.unusedSectionVars false

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-- Lowering indices is injective on tensor fields. -/
theorem flatCc_injective (g : SmoothRiemannianMetric I M) {r s : ℕ} {A B : SmoothCcTensor g r s}
    (h : flatCc g r s A = flatCc g r s B) : A = B := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  have hx := congrArg (fun W : SmoothCcTensor g 0 (r + s) => W.toSection x) h
  simp only [flatCc_toSection] at hx
  exact (flat g r s x).injective hx

namespace EquationData

variable [CompleteSpace E] (g : SmoothRiemannianMetric I M) {r s p : ℕ} (D : EquationData I M r s p)

/-- **Lowering carries parabolic solutions to parabolic solutions** (`lem:lowering`). -/
theorem isParabolicSolution_flatData {u₀ : SmoothCcTensor g r s} {T : ℝ}
    {u : ℝ → SmoothCcTensor g r s} (hu : D.IsParabolicSolution g u₀ T u) :
    (D.flatData g).IsParabolicSolution g (flatCc g r s u₀) T (fun t => flatCc g r s (u t)) := by
  obtain ⟨hsol, hpar⟩ := hu
  refine ⟨⟨hsol.pos, hsol.le_T₀, jointlySmoothOn_flatCc g hsol.smooth, ?_, ?_, ?_⟩, ?_⟩
  · change flatCc g r s (u 0) = flatCc g r s u₀
    rw [hsol.initial]
  · intro t ht x
    rw [covJet_flatCc_eq]
    exact (D.mem_flatData_dom g t x _).mpr (hsol.jets_mem t ht x)
  · intro t ht x
    have h2 := (flatModel g r s x : TensorRSModel r s ℝ E →L[ℝ] TensorRSModel 0 (r + s) ℝ E).hasFDerivAt.comp_hasDerivWithinAt
      t (hsol.eqn t ht x)
    have hf : (fun τ => TensorRSSpace.toModel ((flatCc g r s (u τ)).toSection x)) =
        (flatModel g r s x : TensorRSModel r s ℝ E →L[ℝ] TensorRSModel 0 (r + s) ℝ E) ∘
          (fun τ => TensorRSSpace.toModel ((u τ).toSection x)) := by
      funext τ
      rw [Function.comp_apply, flatCc_toSection, toModel_flat]
      rfl
    have hd : TensorRSSpace.toModel
        ((D.flatData g).F t x (covJet g 0 (r + s) (2 * p) (flatCc g r s (u t)) x)) =
        (flatModel g r s x : TensorRSModel r s ℝ E →L[ℝ] TensorRSModel 0 (r + s) ℝ E)
          (TensorRSSpace.toModel (D.F t x (covJet g r s (2 * p) (u t) x))) := by
      rw [covJet_flatCc_eq, flatData_F, toModel_flat]
      rfl
    change HasDerivWithinAt (fun τ => TensorRSSpace.toModel ((flatCc g r s (u τ)).toSection x))
      (TensorRSSpace.toModel ((D.flatData g).F t x (covJet g 0 (r + s) (2 * p) (flatCc g r s (u t)) x)))
      (Icc 0 T) t
    rw [hf, hd]
    exact h2
  · intro t ht x
    rw [covJet_flatCc_eq]
    exact D.isParabolicAt_flatData g (hpar t ht x)

end EquationData

/-- **Theorem B reduces to covariant bundles.** If parabolic solutions are unique for every
equation on a covariant bundle `T⁰_{s'} M`, they are unique on every `T^r_s M`. -/
theorem solution_unique_of_covariant {p : ℕ} (g : SmoothRiemannianMetric I M)
    (hcov : ∀ (s' : ℕ) (D' : EquationData I M 0 s' p) {u₀ : SmoothCcTensor g 0 s'} {T : ℝ}
      {u v : ℝ → SmoothCcTensor g 0 s'},
      D'.IsParabolicSolution g u₀ T u → D'.IsParabolicSolution g u₀ T v →
        ∀ t ∈ Icc (0 : ℝ) T, u t = v t)
    {r s : ℕ} (D : EquationData I M r s p) {u₀ : SmoothCcTensor g r s} {T : ℝ}
    {u v : ℝ → SmoothCcTensor g r s}
    (hu : D.IsParabolicSolution g u₀ T u) (hv : D.IsParabolicSolution g u₀ T v) :
    ∀ t ∈ Icc (0 : ℝ) T, u t = v t := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  intro t ht
  exact flatCc_injective g (hcov (r + s) (D.flatData g) (D.isParabolicSolution_flatData g hu)
    (D.isParabolicSolution_flatData g hv) t ht)

end ShortTime
