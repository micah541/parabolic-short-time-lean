import ShortTime.Linear.LegendreGeneral
import ShortTime.Sanity.LegendreTrace

/-!
# Non-vacuity of the Legendre condition in every order

Paper: Lemma `lem:legendre-examples` (b), the algebraic part `κ(P₀) = 1`.

`polyTrace g r s p x` is the principal coefficient `P₀(X) = (-1)^{p+1} Σ_I X(e_I, e_I, ·)` of the
polyharmonic heat equation `∂ₜu = -(Δ)^p u`, written with a `g`-orthonormal frame. It undoes
prepending frame covectors up to sign (`polyTrace_prepend`), so its Legendre form is
`(-1)^{p+1} |ξ|²` and it satisfies the Legendre condition with constant `1`
(`legendreAt_polyTrace`). This complements `legendreAt_traceCLM` (`p = 1`): `LegendreAt` is
satisfiable in every order `2p`.

The identity `-(Δ)^p u = P₀(∇^{2p}u) + (lower order)` of the paper, which needs the Ricci identities,
is not formalized here.
-/

noncomputable section

open Bundle Manifold Set
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff BigOperators

set_option linter.unusedSectionVars false

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-- Evaluation of the first `p` slots, as a continuous linear map. -/
def evalFirstCLM {r s : ℕ} {x : M} : ∀ p : ℕ, (Fin p → TangentSpace I x) →
    TensorRSSpace r (s + p) I x →L[ℝ] TensorRSSpace r s I x
  | 0, _ => ContinuousLinearMap.id ℝ _
  | p + 1, v => (evalFirstCLM p (Fin.tail v)).comp (evalSlot r (s + p) x (v 0))

theorem evalFirstCLM_apply {r s : ℕ} {x : M} (p : ℕ) :
    ∀ (v : Fin p → TangentSpace I x) (ξ : TensorRSSpace r (s + p) I x),
      evalFirstCLM p v ξ = evalFirst p v ξ := by
  induction p with
  | zero => intro v ξ; rfl
  | succ p ih =>
    intro v ξ
    rw [evalFirstCLM, ContinuousLinearMap.comp_apply, ih]
    rfl

/-- Evaluating the first `p` slots of `θ ⊗ η` on `v` gives `θ(v) η`. -/
theorem evalFirst_prependCovectors {r t : ℕ} {x : M} (p : ℕ) :
    ∀ (v : Fin p → TangentSpace I x) (θ : Fin p → (TangentSpace I x →L[ℝ] ℝ))
      (η : TensorRSSpace r t I x),
      evalFirst p v (prependCovectors p θ η) = (∏ i, θ i (v i)) • η := by
  induction p with
  | zero => intro v θ η; simp [evalFirst, prependCovectors]
  | succ p ih =>
    intro v θ η
    change evalFirst p (Fin.tail v) ((covGradBundleEquiv (I := I) (M := M) r (t + p) x).symm
      (covGradBundleEquiv (I := I) (M := M) r (t + p) x
        ((θ 0).smulRight (prependCovectors p (Fin.tail θ) η))) (v 0)) = _
    rw [ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearMap.smulRight_apply,
      ← evalFirstCLM_apply, map_smul, evalFirstCLM_apply, ih, smul_smul, Fin.prod_univ_succ]
    rfl

variable (g : SmoothRiemannianMetric I M)

/-- The principal coefficient `P₀(X) = (-1)^{p+1} Σ_I X(e_I, e_I, ·)` of `∂ₜu = -(Δ)^p u`. -/
def polyTrace (r s p : ℕ) (x : M) : TensorRSSpace r (s + p + p) I x →L[ℝ] TensorRSSpace r s I x :=
  (-1 : ℝ) ^ (p + 1) • ∑ K : Fin p → Fin (Module.finrank ℝ (TangentSpace I x)),
    (evalFirstCLM (s := s) p (fun i => tangentFrame g x (K i))).comp
      (evalFirstCLM (s := s + p) p (fun i => tangentFrame g x (K i)))

/-- `P₀` undoes prepending frame covectors: `P₀(e^K ⊗ η) = (-1)^{p+1} η(e_K, ·)`. -/
theorem polyTrace_prepend {r s p : ℕ} {x : M}
    (K' : Fin p → Fin (Module.finrank ℝ (TangentSpace I x))) (η : TensorRSSpace r (s + p) I x) :
    polyTrace g r s p x (prependCovectors p (fun i => g.inner x (tangentFrame g x (K' i))) η) =
      (-1 : ℝ) ^ (p + 1) • evalFirst p (fun i => tangentFrame g x (K' i)) η := by
  classical
  have h : ∀ K : Fin p → Fin (Module.finrank ℝ (TangentSpace I x)),
      (∏ i, g.inner x (tangentFrame g x (K' i)) (tangentFrame g x (K i))) =
        if K' = K then 1 else 0 := by
    intro K
    simp only [tangentFrame_inner]
    rw [Finset.prod_boole]
    simp [funext_iff]
  simp only [polyTrace, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, evalFirstCLM_apply, evalFirst_prependCovectors, h, ite_smul,
    one_smul, zero_smul]
  congr 1
  rw [Finset.sum_eq_single K']
  · rw [if_pos rfl]
  · intro K _ hK
    rw [if_neg (Ne.symm hK), ← evalFirstCLM_apply, map_zero]
  · intro hK
    exact absurd (Finset.mem_univ K') hK

/-- **Non-vacuity of the Legendre condition in every order.** The polyharmonic principal
coefficient satisfies `LegendreAt` with constant `1`. -/
theorem legendreAt_polyTrace (s p : ℕ) (x : M) : LegendreAt g 0 s p x (polyTrace g 0 s p x) 1 := by
  refine ⟨one_pos, fun ξ => ?_⟩
  rw [legendreForm_eq]
  simp only [polyTrace_prepend, fiberInner_smul_right]
  rw [← Finset.mul_sum, ← fiberInner_eq_sum_evalFirst g s x p ξ ξ, ← mul_assoc, ← mul_pow]
  norm_num

end ShortTime
