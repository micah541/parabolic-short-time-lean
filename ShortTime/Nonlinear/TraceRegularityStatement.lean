import ShortTime.Nonlinear.Existence

/-!
# The trace form of the regularity statement (hypothesis for `cor:C`)

`EquationData.TraceRegularity` states the regularity of `𝒫^m` solutions in the form used by the
continuous-dependence argument. In the setting of `parabolicSpace_solution_smooth` (a smooth base
`w` with parabolic jets, `𝒩` with the properties of `exists_nonlinOp`, the parabolic linearization
`L_w`), there is a neighbourhood `V` of `w` in `𝒫^m` such that every `U ∈ V` that differs from a
smooth family `b` by an element of `𝒫^m_0` and satisfies `∂ₜU - 𝒩(U) = f` with `f` smooth, is itself a
smooth family.

It is stated as a `Prop` so that `solution_continuous_dependence` can take it as an explicit
hypothesis until the proof is wired in.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set Filter Topology MeasureTheory Metric
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Spectral
open scoped Manifold ContDiff BigOperators

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

namespace EquationData

variable {s p : ℕ}

open ParabolicSpace

/-- **Regularity in trace form** (the statement `regularity_of_time_trace`). -/
def TraceRegularity (D : EquationData I M 0 s p) (g : SmoothRiemannianMetric I M) : Prop :=
  1 ≤ p → ∀ {m : ℕ}, Module.finrank ℝ E / (2 * p) + 4 ≤ m → ∀ (hm1 : 1 ≤ m)
    {T₁ : ℝ} (hT₁ : 0 < T₁), T₁ ≤ D.T₀ → ∀ {lam : ℝ}, 0 < lam →
    ∀ {w : ℝ → SmoothCcTensor g 0 s} (hw : JointlySmoothOn g 0 s (Icc 0 T₁) w),
    (∀ t ∈ Icc (0 : ℝ) T₁, ∀ x : M, covJet g 0 s (2 * p) (w t) x ∈ D.dom t x ∧
      LegendreAt g 0 s p x (D.principal t x (covJet g 0 s (2 * p) (w t) x)) lam) →
    ∀ {δ : ℝ}, 0 < δ →
    ∀ {𝒩 : ParabolicSpace g s p m T₁ → ParabolicSpace g s p (m - 1) T₁},
    ContDiffAt ℝ ∞ 𝒩 (ofSmooth w hw) →
    (∀ u (hu : JointlySmoothOn g 0 s (Icc 0 T₁) u),
      dist (ofSmooth (p := p) (m := m) u hu) (ofSmooth w hw) < δ →
      (∀ t ∈ Icc (0 : ℝ) T₁, ∀ x : M, covJet g 0 s (2 * p) (u t) x ∈ D.dom t x) ∧
      ∃ hF, 𝒩 (ofSmooth u hu) = ofSmooth (D.nonlinFamily u) hF) →
    (∃ L : LinearOp g s p T₁, L.IsParabolic lam ∧
      (∀ k t, t ∈ Icc (0 : ℝ) T₁ → ∀ x,
        opFieldHom ((L.coeff k t).toSection x) =
          D.partialDeriv k t x (covJet g 0 s (2 * p) (w t) x)) ∧
      ∀ h (hh : JointlySmoothOn g 0 s (Icc 0 T₁) h), ∃ hL,
        fderiv ℝ 𝒩 (ofSmooth w hw) (ofSmooth h hh) =
          ofSmooth (fun t => L.apply t (h t)) hL) →
    ∃ V ∈ 𝓝 (ofSmooth (p := p) (m := m) w hw), ∀ U ∈ V,
      ∀ (f : ℝ → SmoothCcTensor g 0 s) (hf : JointlySmoothOn g 0 s (Icc 0 T₁) f)
        (b : ℝ → SmoothCcTensor g 0 s) (hb : JointlySmoothOn g 0 s (Icc 0 T₁) b),
        U - ofSmooth b hb ∈ zeroAtStart g s p m T₁ →
        timeDerivExt hT₁ hm1 U - 𝒩 U = ofSmooth f hf →
        ∃ (vt : ℝ → SmoothCcTensor g 0 s) (hvt : JointlySmoothOn g 0 s (Icc 0 T₁) vt),
          U = ofSmooth vt hvt

end EquationData

end ShortTime
