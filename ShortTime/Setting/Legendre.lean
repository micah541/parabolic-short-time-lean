import ShortTime.Setting.Jet
import DifferentialGeometry.Geometry.Metric.TensorInner.TensorRS.RiemannianBundle
import DifferentialGeometry.Tensor.RSTensor.Reindexing.CovariantSlot

/-!
# The Legendre condition

Paper: Definition `def:legendre`.

For `P : T^r_{s+2p} → T^r_s` at a point `x`, the Legendre form is
`B_P(ξ, η) = Σ_{I,J} ⟨ξ_I, P(e^I ⊗ e^J ⊗ η_J)⟩ = Σ_I ⟨ξ_I, P(e^I ⊗ η)⟩`,
where `ξ, η ∈ T^r_{s+p}`, `(e_i)` is a `g`-orthonormal basis of `T_xM`,
`ξ_I = ξ(e_{i₁}, …, e_{i_p}, ·)`, and `e^I ⊗ η` puts the covectors `g(e_{i_k}, ·)` in the
first `p` slots. The Legendre condition with constant `λ > 0` is
`(-1)^{p+1} B_P(ξ, ξ) ≥ λ |ξ|²` for all `ξ`.
-/

noncomputable section

open Bundle Manifold Set
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Analysis.Sobolev
open scoped Manifold ContDiff BigOperators

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-- `ξ ↦ ξ(v₀, …, v_{p-1}, ·)`: evaluate the first `p` slots of a `T^r_{s+p}`-tensor. -/
def evalFirst {r s : ℕ} {x : M} : ∀ p : ℕ,
    (Fin p → TangentSpace I x) → TensorRSSpace r (s + p) I x → TensorRSSpace r s I x
  | 0, _, ξ => ξ
  | p + 1, v, ξ =>
      evalFirst p (Fin.tail v) ((covGradBundleEquiv (I := I) (M := M) r (s + p) x).symm ξ (v 0))

/-- `θ₀ ⊗ ⋯ ⊗ θ_{p-1} ⊗ η`: prepend `p` covectors, occupying the first `p` slots. -/
def prependCovectors {r t : ℕ} {x : M} : ∀ p : ℕ,
    (Fin p → (TangentSpace I x →L[ℝ] ℝ)) → TensorRSSpace r t I x → TensorRSSpace r (t + p) I x
  | 0, _, η => η
  | p + 1, θ, η =>
      covGradBundleEquiv (I := I) (M := M) r (t + p) x
        ((θ 0).smulRight (prependCovectors p (Fin.tail θ) η))

/-- The fibre inner product on `T^r_s M` induced by `g`. -/
def fiberInner (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (v w : TensorRSSpace r s I x) : ℝ :=
  (Tensor.TensorRSRiemannianBundle.tensorRSRiemannianMetric (I := I) (M := M) g r s).inner x v w

/-- The fibre norm on `T^r_s M` induced by `g`. -/
def fiberNorm (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (v : TensorRSSpace r s I x) : ℝ :=
  Real.sqrt (fiberInner g r s x v v)

/-- The Legendre form `B_P(ξ, η) = Σ_I ⟨ξ_I, P(e^I ⊗ η)⟩` of `P : T^r_{s+2p} → T^r_s` at `x`,
computed in a `g`-orthonormal basis of `T_xM` (the value does not depend on the basis). -/
def legendreForm (g : SmoothRiemannianMetric I M) (r s p : ℕ) (x : M)
    (P : TensorRSSpace r (s + p + p) I x →L[ℝ] TensorRSSpace r s I x)
    (ξ η : TensorRSSpace r (s + p) I x) : ℝ := by
  classical
  let cd : InnerProductSpace.Core ℝ (TangentSpace I x) := g.toRiemannianMetric.toCore x
  have hc : ContinuousAt (fun v : TangentSpace I x => cd.inner v v) 0 :=
    g.toRiemannianMetric.continuousAt x
  have hb : Bornology.IsVonNBounded ℝ
      {v : TangentSpace I x | RCLike.re (cd.inner v v) < 1} :=
    g.toRiemannianMetric.isVonNBounded x
  letI : NormedAddCommGroup (TangentSpace I x) := cd.toNormedAddCommGroupOfTopology hc hb
  letI : InnerProductSpace ℝ (TangentSpace I x) := InnerProductSpace.ofCoreOfTopology cd hc hb
  let n : ℕ := Module.finrank ℝ (TangentSpace I x)
  let e : OrthonormalBasis (Fin n) ℝ (TangentSpace I x) := stdOrthonormalBasis ℝ _
  exact ∑ K : Fin p → Fin n,
    fiberInner g r s x (evalFirst p (fun i => e (K i)) ξ)
      (P (prependCovectors p (fun i => g.inner x (e (K i))) η))

/-- The **Legendre condition** with constant `lam` for `P : T^r_{s+2p} → T^r_s` at `x`:
`lam > 0` and `(-1)^{p+1} B_P(ξ, ξ) ≥ lam |ξ|²` for every `ξ ∈ T^r_{s+p}` (`def:legendre`). -/
def LegendreAt (g : SmoothRiemannianMetric I M) (r s p : ℕ) (x : M)
    (P : TensorRSSpace r (s + p + p) I x →L[ℝ] TensorRSSpace r s I x) (lam : ℝ) : Prop :=
  0 < lam ∧ ∀ ξ : TensorRSSpace r (s + p) I x,
    lam * fiberInner g r (s + p) x ξ ξ ≤ (-1 : ℝ) ^ (p + 1) * legendreForm g r s p x P ξ ξ

end ShortTime
