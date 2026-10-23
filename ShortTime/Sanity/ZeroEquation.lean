import ShortTime.Setting.Equation

/-!
# Non-vacuity of `EquationData` and `IsSolution` (task T0, part 2)

The equation `∂ₜu = 0`, with every jet in the domain, is a valid `EquationData`. Its openness and
smoothness conditions hold. Every constant tensor field is a solution. Together with
`legendreAt_traceCLM` (part 1), this shows that the pinned definitions admit genuine instances.

What is still missing is a single equation that is both smooth in the trivializations and parabolic,
namely the heat equation. See `CLAUDE.md`, task T0.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Analysis.Sobolev
open scoped Manifold ContDiff

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

variable (I M) in
/-- The equation `∂ₜu = 0` on `(r,s)`-tensors, as equation data of order `2p`, with every jet
in the domain. -/
def zeroData (r s p : ℕ) (T₀ : ℝ) (hT₀ : 0 < T₀) : EquationData I M r s p where
  T₀ := T₀
  T₀_pos := hT₀
  dom := fun _ _ => Set.univ
  F := fun _ _ _ => 0
  dom_relOpen := fun x₀ => ⟨Set.univ, isOpen_univ, by ext q; simp [localDom]⟩
  smooth := fun x₀ => by
    have h : localRep r s (2 * p) (fun (_ : ℝ) (x : M) (_ : CovJetFiber I r s (2 * p) x) =>
        (0 : TensorRSSpace r s I x)) x₀ = fun _ => 0 := by
      funext q
      simp [localRep]
    rw [h]
    exact contMDiffOn_const

/-- Every constant tensor field is a solution of `∂ₜu = 0` on `[0,T]`, for `0 < T ≤ T₀`. -/
theorem zeroData_isSolution_const (r s p : ℕ) {T₀ : ℝ} (hT₀ : 0 < T₀)
    (g : SmoothRiemannianMetric I M) (u₀ : SmoothCcTensor g r s) {T : ℝ} (hT : 0 < T)
    (hTT₀ : T ≤ T₀) :
    (zeroData I M r s p T₀ hT₀).IsSolution g u₀ T (fun _ => u₀) where
  pos := hT
  le_T₀ := hTT₀
  smooth := (u₀.toSection.contMDiff.comp contMDiff_fst).contMDiffOn
  initial := rfl
  jets_mem := fun _ _ _ => Set.mem_univ _
  eqn := fun t _ x => by
    simpa [zeroData, TensorRSSpace.toModel_zero] using
      hasDerivWithinAt_const t (Icc 0 T) (TensorRSSpace.toModel (u₀.toSection x))

end ShortTime
