import ShortTime.Nonlinear.Linearize

/-!
# The linearization at a smooth family

For a jointly smooth family `w` whose jets lie in the domain of `F`, the linearization
`L_w h = Σ_k D_k F(t, j^{2p} w) ∇^k h` is a `LinearOp` (`EquationData.exists_linOp`). If the jets
of `w` satisfy the Legendre condition with a uniform constant, `L_w` is parabolic.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set MeasureTheory
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

/-- The average of a constant family is its value. -/
theorem avgFib_const {r a b : ℕ} {x : M}
    (P : TensorRSSpace r a I x →L[ℝ] TensorRSSpace r b I x) : avgFib (fun _ => P) = P := by
  ext w
  simp only [avgFib, intervalIntegral.integral_const, sub_zero, one_smul, modelCLM,
    ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply]

namespace EquationData

variable {s p : ℕ} (D : EquationData I M 0 s p) {g : SmoothRiemannianMetric I M}

/-- **The linearization at a smooth family** is a `LinearOp` with coefficients
`D_k F(t, j^{2p} w(t))`. -/
theorem exists_linOp {T : ℝ} (hT : 0 < T) (hTD : T ≤ D.T₀) {w : ℝ → SmoothCcTensor g 0 s}
    (hw : JointlySmoothOn g 0 s (Icc 0 T) w)
    (hdom : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, covJet g 0 s (2 * p) (w t) x ∈ D.dom t x) :
    ∃ L : LinearOp g s p T, ∀ k : Fin (2 * p + 1), ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      opFieldHom ((L.coeff k t).toSection x) = D.partialDeriv k t x (covJet g 0 s (2 * p) (w t) x) := by
  have hseg : ∀ σ : ℝ, ∀ t, w t + σ • (w t - w t) = w t := fun σ t => by
    rw [sub_self, smul_zero, add_zero]
  obtain ⟨A, hA, hAeq⟩ := D.exists_avg_coeff hw hw hTD le_rfl hT (by rw [zero_add])
    fun t ht x σ _ => by
      rw [hseg]
      exact hdom t ⟨by simpa using ht.1, by simpa using ht.2⟩ x
  refine ⟨⟨A, hA⟩, fun k t ht x => ?_⟩
  have h := hAeq k t ht x
  simp only [hseg, zero_add] at h
  rw [avgFib_const] at h
  exact h

end EquationData

end ShortTime
