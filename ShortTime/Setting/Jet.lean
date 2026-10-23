import DifferentialGeometry.Analysis.Sobolev.Embedding.CovariantDerivative.Cm

/-!
# Covariant jets and jointly smooth families

Paper: Definition `def:jet`, and the smoothness notion used in `def:solution`.

In this formalization the bundle `V` of the paper is a tensor bundle `T^r_s M`, with fibres
`TensorRSSpace r s I x`. This family is closed under `W ↦ T*M ⊗ W`, which is all the linear
theory needs (paper, Remark "General bundles versus tensor bundles").

* The covariant `N`-jet fibre is the dependent product `∀ k : Fin (N+1), T^r_{s+k}`.
* The jet of a tensor field `u` is `(u, ∇u, …, ∇^N u)`, computed with the library's
  `iteratedCovGrad`. As in the paper, the slot created by `∇` is the *first* slot.
-/

noncomputable section

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

variable (I) in
/-- Fibre at `x` of the covariant `N`-jet bundle `J^N(T^r_s M) = ⊕_{k ≤ N} T^r_{s+k} M`. -/
abbrev CovJetFiber (r s N : ℕ) (x : M) : Type _ :=
  ∀ k : Fin (N + 1), TensorRSSpace r (s + (k : ℕ)) I x

variable (E) in
/-- Model fibre of the covariant `N`-jet bundle. -/
abbrev JetModel (r s N : ℕ) : Type _ :=
  ∀ k : Fin (N + 1), TensorRSModel r (s + (k : ℕ)) ℝ E

/-- The covariant `N`-jet `j^N u (x) = (u, ∇u, …, ∇^N u)(x)` of a tensor field (`def:jet`). -/
def covJet (g : SmoothRiemannianMetric I M) (r s N : ℕ) (u : SmoothCcTensor g r s) (x : M) :
    CovJetFiber I r s N x :=
  fun k => (iteratedCovGrad g r s k u).toSection x

/-- A time-dependent tensor field `u : ℝ → T^r_s` is smooth on `M × S`.

With `S = [0,T]` this is the paper's `u ∈ C^∞(M × [0,T]; V)`: smooth up to `t = 0` and
`t = T`. It is the same notion as the library's `RicciDeTurckPairing.JointlySmoothCcTensorFamily`,
restated here so that we do not import the Ricci-flow development. -/
def JointlySmoothOn (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : Set ℝ)
    (u : ℝ → SmoothCcTensor g r s) : Prop :=
  ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
    (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
      (E := fun x : M => TensorRSSpace r s I x) q.1 ((u q.2).toSection q.1))
    ((Set.univ : Set M) ×ˢ S)

end ShortTime
