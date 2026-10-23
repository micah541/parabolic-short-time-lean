import ShortTime.Setting.Legendre

/-!
# The equation `∂ₜu = F(t, j^{2p}u)` and its solutions

Paper: Definitions `def:data`, `def:linearization`, `def:solution`, and the parabolicity
domain of `def:legendre`.

`F` is given fibrewise, `F t x : J^{2p}_x → T^r_s|_x`, on a fibrewise domain `dom t x`.
Openness of the domain and smoothness of `F` are required in the local trivializations of the
tensor bundles. This is the standard meaning of "an open subset of `[0,T₀] × J^{2p}V`" and of
"a smooth fibre-preserving map" in the paper.
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

variable (I M) in
/-- The trivialization of `T^r_s M` at `x₀`. -/
abbrev trivAt (r s : ℕ) (x₀ : M) :=
  trivializationAt (TensorRSModel r s ℝ E) (fun x : M => TensorRSSpace r s I x) x₀

/-- A neighbourhood of `x₀` over which all bundles `T^r_{s+k}`, `k ≤ N`, are trivialized. -/
def jetBase (r s N : ℕ) (x₀ : M) : Set M :=
  (trivAt I M r s x₀).baseSet ∩ ⋂ k : Fin (N + 1), (trivAt I M r (s + k) x₀).baseSet

/-- A jet over `y` with coordinates `z` in the trivialization at `x₀`. -/
def jetOfModel (r s N : ℕ) (x₀ y : M) (z : JetModel E r s N) : CovJetFiber I r s N y :=
  fun k => (trivAt I M r (s + k) x₀).symmL ℝ y (z k)

/-- The part of `[0,T₀] × J^N` over `jetBase x₀`, in local coordinates `(t, y, z)`. -/
def localSlab (r s N : ℕ) (T₀ : ℝ) (x₀ : M) : Set (ℝ × M × JetModel E r s N) :=
  {q | q.1 ∈ Icc 0 T₀ ∧ q.2.1 ∈ jetBase (I := I) r s N x₀}

/-- The domain `dom`, read in the local coordinates at `x₀`. -/
def localDom (r s N : ℕ) (T₀ : ℝ) (dom : ℝ → (x : M) → Set (CovJetFiber I r s N x)) (x₀ : M) :
    Set (ℝ × M × JetModel E r s N) :=
  {q | q ∈ localSlab (I := I) r s N T₀ x₀ ∧ jetOfModel r s N x₀ q.2.1 q.2.2 ∈ dom q.1 q.2.1}

/-- `F` read in the local coordinates at `x₀`. -/
def localRep (r s N : ℕ) (F : ℝ → (x : M) → CovJetFiber I r s N x → TensorRSSpace r s I x)
    (x₀ : M) : ℝ × M × JetModel E r s N → TensorRSModel r s ℝ E :=
  fun q => (trivAt I M r s x₀).continuousLinearMapAt ℝ q.2.1
    (F q.1 q.2.1 (jetOfModel r s N x₀ q.2.1 q.2.2))

variable (I M) in
/-- **Equation data** (`def:data`): a final time `T₀ > 0`, an open domain
`𝒟 ⊆ [0,T₀] × J^{2p}(T^r_s M)`, and a smooth fibre-preserving `F : 𝒟 → T^r_s M`. -/
structure EquationData (r s p : ℕ) where
  /-- The final time `T₀`. -/
  T₀ : ℝ
  T₀_pos : 0 < T₀
  /-- The domain `𝒟`, fibrewise: `dom t x ⊆ J^{2p}_x`. -/
  dom : ℝ → (x : M) → Set (CovJetFiber I r s (2 * p) x)
  /-- The nonlinearity `F(t, ζ) ∈ (T^r_s)_x` for `ζ ∈ J^{2p}_x`. -/
  F : ℝ → (x : M) → CovJetFiber I r s (2 * p) x → TensorRSSpace r s I x
  /-- `𝒟` is relatively open in `[0,T₀] × J^{2p}`. -/
  dom_relOpen : ∀ x₀ : M, ∃ U : Set (ℝ × M × JetModel E r s (2 * p)),
    IsOpen U ∧ localDom r s (2 * p) T₀ dom x₀ = U ∩ localSlab (I := I) r s (2 * p) T₀ x₀
  /-- `F` is smooth on `𝒟`, jointly in `(t, x, ζ)`. -/
  smooth : ∀ x₀ : M,
    ContMDiffOn (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, JetModel E r s (2 * p))))
      𝓘(ℝ, TensorRSModel r s ℝ E) ∞
      (localRep r s (2 * p) F x₀) (localDom r s (2 * p) T₀ dom x₀)

namespace EquationData

variable {r s p : ℕ} (D : EquationData I M r s p)

/-- `D_k F(t, ζ)`: the derivative of `F` along the `k`-th jet component (`def:linearization`). -/
def partialDeriv (k : Fin (2 * p + 1)) (t : ℝ) (x : M) (ζ : CovJetFiber I r s (2 * p) x) :
    TensorRSSpace r (s + k) I x →L[ℝ] TensorRSSpace r s I x :=
  (fderiv ℝ (D.F t x) ζ).comp
    (ContinuousLinearMap.single ℝ (fun k : Fin (2 * p + 1) => TensorRSSpace r (s + k) I x) k)

/-- Reindex `T^r_a ≃ T^r_b` along a proof `a = b`. -/
def castIdx {r a b : ℕ} (h : a = b) (x : M) : TensorRSSpace r a I x ≃L[ℝ] TensorRSSpace r b I x := by
  subst h
  exact ContinuousLinearEquiv.refl ℝ _

/-- The principal coefficient `P = D_{2p} F(t, ζ) : T^r_{s+2p} → T^r_s` (`def:linearization`). -/
def principal (t : ℝ) (x : M) (ζ : CovJetFiber I r s (2 * p) x) :
    TensorRSSpace r (s + p + p) I x →L[ℝ] TensorRSSpace r s I x :=
  (D.partialDeriv (Fin.last (2 * p)) t x ζ).comp
    (castIdx (r := r) (by simp only [Fin.val_last]; omega) x).toContinuousLinearMap

/-- `(t, ζ)` lies in the parabolicity domain `𝒪` (`def:legendre`): `ζ ∈ 𝒟` and the principal
coefficient satisfies the Legendre condition with some positive constant. -/
def IsParabolicAt (g : SmoothRiemannianMetric I M) (t : ℝ) (x : M)
    (ζ : CovJetFiber I r s (2 * p) x) : Prop :=
  ζ ∈ D.dom t x ∧ ∃ lam : ℝ, LegendreAt g r s p x (D.principal t x ζ) lam

/-- A **solution on `[0,T]` with initial datum `u₀`** (`def:solution`).

The time derivative in `eqn` is taken in the model fibre `TensorRSModel r s ℝ E`, through the
canonical linear identification `TensorRSSpace.toModel` of the fibre over `x`. For a curve in a
fixed finite-dimensional fibre this is the usual derivative. Working in the model avoids the two
non-definitionally-equal topologies that the library puts on tensor fibres. -/
structure IsSolution (g : SmoothRiemannianMetric I M) (u₀ : SmoothCcTensor g r s) (T : ℝ)
    (u : ℝ → SmoothCcTensor g r s) : Prop where
  pos : 0 < T
  le_T₀ : T ≤ D.T₀
  smooth : JointlySmoothOn g r s (Icc 0 T) u
  initial : u 0 = u₀
  jets_mem : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, covJet g r s (2 * p) (u t) x ∈ D.dom t x
  eqn : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
    HasDerivWithinAt (fun τ => TensorRSSpace.toModel ((u τ).toSection x))
      (TensorRSSpace.toModel (D.F t x (covJet g r s (2 * p) (u t) x))) (Icc 0 T) t

/-- A **parabolic solution**: a solution whose jets stay in the parabolicity domain `𝒪`. -/
def IsParabolicSolution (g : SmoothRiemannianMetric I M) (u₀ : SmoothCcTensor g r s) (T : ℝ)
    (u : ℝ → SmoothCcTensor g r s) : Prop :=
  D.IsSolution g u₀ T u ∧
    ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, D.IsParabolicAt g t x (covJet g r s (2 * p) (u t) x)

end EquationData

end ShortTime
