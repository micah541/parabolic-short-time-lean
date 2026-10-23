import ShortTime.Linear.Basic
import ShortTime.Linear.PrincipalIBP

/-!
# Linear parabolic operators on covariant tensor bundles (`def:class`)

`L(t) u = ∑_{k ≤ 2p} A_k(t) (∇^k u)` on `V = T⁰_s M`, with coefficients `A_k(t)` smooth operator
fields `T⁰_{s+k} → T⁰_s` that depend smoothly on `(x, t) ∈ M × [0, T]`.

We work with covariant tensor bundles: this family is closed under `W ↦ T*M ⊗ W`, which is all
the energy method needs, and the library's calculus of operator fields (Leibniz rule, integration
by parts, joint smoothness in parameters) is available there. The general bundle `T^r_s M` reduces
to this case by lowering all indices with the metric.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set MeasureTheory
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open scoped Manifold ContDiff BigOperators

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-- A linear differential operator `L(t) = ∑_{k ≤ 2p} A_k(t) ∇^k` of order `2p` on `T⁰_s M`, with
coefficients jointly smooth on `M × [0, T]`. -/
structure LinearOp (g : SmoothRiemannianMetric I M) (s p : ℕ) (T : ℝ) where
  /-- The coefficient `A_k(t)` of `∇^k`, an operator field `T⁰_{s+k} → T⁰_s`. -/
  coeff : ∀ k : Fin (2 * p + 1), ℝ → SmoothCcTensor g (s + k) s
  smooth : ∀ k : Fin (2 * p + 1), JointlySmoothOn g (s + k) s (Icc 0 T) (coeff k)

namespace LinearOp

variable {g : SmoothRiemannianMetric I M} {s p : ℕ} {T : ℝ} (L : LinearOp g s p T)

/-- `L(t) u = ∑_k A_k(t) ∇^k u`. -/
def apply (t : ℝ) (u : SmoothCcTensor g 0 s) : SmoothCcTensor g 0 s :=
  ∑ k : Fin (2 * p + 1),
    operatorFieldApply (I := I) (M := M) g (s + k) s (L.coeff k t) (iteratedCovGrad g 0 s k u)

/-- `u` solves `∂ₜu = L u + f` on `[0, T]` (time derivatives of the model values, one fibre at a
time, as in `EquationData.IsSolution`). -/
def Solves (u f : ℝ → SmoothCcTensor g 0 s) : Prop :=
  ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
    HasDerivWithinAt (fun τ => (u τ).toFun x) ((L.apply t (u t) + f t).toFun x) (Icc 0 T) t

end LinearOp

/-! ### Parabolicity -/

/-- The value `Φ(x) : T⁰_a → T⁰_b` of an operator field, acting on the fibres `T⁰_a = Hom(T⁰_0, T⁰_a)`
used by the nonlinear setting (`ξ ↦ Φ(x) ∘ ξ`). -/
def opFieldHom {a b : ℕ} {x : M} (Φ : TensorRSSpace a b I x) :
    TensorRSSpace 0 a I x →L[ℝ] TensorRSSpace 0 b I x :=
  LinearMap.toContinuousLinearMap
    { toFun := fun ξ => (show TensorRSSpace 0 b I x from
        (show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from Φ).comp
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace a I x from ξ))
      map_add' := fun ξ η => ContinuousLinearMap.comp_add _ _ _
      map_smul' := fun c ξ => ContinuousLinearMap.comp_smul _ _ _ }

namespace LinearOp

variable {g : SmoothRiemannianMetric I M} {s p : ℕ} {T : ℝ} (L : LinearOp g s p T)

/-- The principal coefficient `A_{2p}(t, x)`, as a map `T⁰_{s+p+p} → T⁰_s` of the nonlinear
setting. -/
def principal (t : ℝ) (x : M) : TensorRSSpace 0 (s + p + p) I x →L[ℝ] TensorRSSpace 0 s I x :=
  (opFieldHom ((L.coeff ⟨2 * p, Nat.lt_succ_self _⟩ t).toSection x)).comp
    (EquationData.castIdx (r := 0) (by simp only; omega) x).toContinuousLinearMap

/-- `L` is parabolic on `[0, T]` with Legendre constant `lam` (the class `𝓛` of the paper): the
principal coefficient satisfies the Legendre condition (`def:legendre`) at every `(x, t)`. -/
def IsParabolic (lam : ℝ) : Prop :=
  0 < lam ∧ ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, LegendreAt g 0 s p x (L.principal t x) lam

end LinearOp

/-! ### Parabolicity for second-order operators -/

/-- The pointwise inner product of two covariant tensor fields at `x`. -/
abbrev ptInner (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M) (S T : TensorRSSpace 0 s I x) :
    ℝ :=
  tensorInnerPointwise (I := I) (M := M) g 0 s x (TensorRSSpace.toModel S)
    (TensorRSSpace.toModel T)

/-- For `p = 1`: the flipped principal coefficient `Ǎ₂(t)` is uniformly coercive,
`⟨ξ, Ǎ₂ ξ⟩ ≥ λ |ξ|²`. This is the Legendre condition for second-order operators. -/
def LinearOp.FlipCoercive {g : SmoothRiemannianMetric I M} {s : ℕ} {T : ℝ}
    [CompleteSpace E] (L : LinearOp g s 1 T) (lam : ℝ) : Prop :=
  0 < lam ∧ ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, ∀ ξ : TensorRSSpace 0 (s + 1) I x,
    lam * ptInner g (s + 1) x ξ ξ ≤
      ptInner g (s + 1) x ξ
        (show TensorRSSpace 0 (s + 1) I x from
          (show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from
            (flipField g (s + 1) s (L.coeff 2 t)).toSection x).comp
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from ξ))

end ShortTime
