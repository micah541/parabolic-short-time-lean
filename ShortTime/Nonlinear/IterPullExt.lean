import ShortTime.Nonlinear.FlowsParabolicExt
import ShortTime.Nonlinear.FlowsNaturalParamChart

/-!
# The composite horizontal pullback on the parabolic spaces

For vector fields `B 0, …, B (n-1)` and `σ ∈ ℝⁿ`, `Π_σ = Π^{B 0}_{σ 0} ∘ ⋯ ∘ Π^{B (n-1)}_{σ (n-1)}`
on `𝒫^m` (`iterPullExt`), extending the composite pullback `iterPull` of smooth families.
-/

noncomputable section

open Bundle Manifold Set Filter
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

namespace ShortTime

namespace HFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

open ParabolicSpace

/-- **The composite pullback `Π_σ : 𝒫^m → 𝒫^m`**. -/
def iterPullExt (g : SmoothRiemannianMetric I M) (s p m : ℕ) (T : ℝ) :
    {n : ℕ} → (B : Fin n → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) → (σ : Fin n → ℝ) →
    ParabolicSpace g s p m T →L[ℝ] ParabolicSpace g s p m T
  | 0, _, _ => ContinuousLinearMap.id ℝ _
  | _ + 1, B, σ => (hpullExt (B 0) g s p m T (σ 0)).comp
      (iterPullExt g s p m T (fun i => B i.succ) (fun i => σ i.succ))

theorem iterPullExt_ofSmooth (g : SmoothRiemannianMetric I M) (s p m : ℕ) {T : ℝ} (hT : 0 < T) :
    ∀ {n : ℕ} (B : Fin n → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (σ : Fin n → ℝ)
      {u : ℝ → SmoothCcTensor g 0 s} (hu : JointlySmoothOn g 0 s (Icc 0 T) u),
      iterPullExt g s p m T B σ (ofSmooth u hu) =
        ofSmooth (fun t => iterPull B g s σ (u t)) (jointlySmoothOn_iterPull g s B σ hu)
  | 0, _, _, _, _ => rfl
  | n + 1, B, σ, u, hu => by
    change hpullExt (B 0) g s p m T (σ 0)
      (iterPullExt g s p m T (fun i => B i.succ) (fun i => σ i.succ) (ofSmooth u hu)) = _
    rw [iterPullExt_ofSmooth g s p m hT (fun i => B i.succ) (fun i => σ i.succ) hu,
      hpullExt_ofSmooth (B 0) g s hT]
    rfl

end HFlow

end ShortTime
