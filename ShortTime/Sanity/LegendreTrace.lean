import ShortTime.Setting.Legendre
import DifferentialGeometry.Geometry.Connection.TensorNabla.FiberNorm.FrameSum

/-!
# Non-vacuity of the Legendre condition (task T0, part 1)

The `g`-trace of the first two slots, `P(Y) = Σⱼ Y(eⱼ, eⱼ, ·)`, is the principal coefficient of the
heat equation `∂ₜu = Δu` (`p = 1`). On `(0,s)`-tensors it satisfies the pinned Legendre condition
with constant `1`: its Legendre form is exactly `|ξ|²`. Hence `legendreForm` and `LegendreAt` are not
vacuous.

Along the way we expose the orthonormal frame used inside `legendreForm` (`tangentFrame`) and
prove that it is `g`-orthonormal.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Elliptic
open scoped Manifold ContDiff BigOperators

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-- A `g_x`-orthonormal basis of `T_xM`, as a family of tangent vectors. This is the frame used
inside `legendreForm` (see `legendreForm_eq`). -/
def tangentFrame (g : SmoothRiemannianMetric I M) (x : M) :
    Fin (Module.finrank ℝ (TangentSpace I x)) → TangentSpace I x := by
  classical
  let cd : InnerProductSpace.Core ℝ (TangentSpace I x) := g.toRiemannianMetric.toCore x
  have hc : ContinuousAt (fun v : TangentSpace I x => cd.inner v v) 0 :=
    g.toRiemannianMetric.continuousAt x
  have hb : Bornology.IsVonNBounded ℝ
      {v : TangentSpace I x | RCLike.re (cd.inner v v) < 1} :=
    g.toRiemannianMetric.isVonNBounded x
  letI : NormedAddCommGroup (TangentSpace I x) := cd.toNormedAddCommGroupOfTopology hc hb
  letI : InnerProductSpace ℝ (TangentSpace I x) := InnerProductSpace.ofCoreOfTopology cd hc hb
  exact fun i => stdOrthonormalBasis ℝ (TangentSpace I x) i

/-- `legendreForm`, written with `tangentFrame`. -/
theorem legendreForm_eq (g : SmoothRiemannianMetric I M) (r s p : ℕ) (x : M)
    (P : TensorRSSpace r (s + p + p) I x →L[ℝ] TensorRSSpace r s I x)
    (ξ η : TensorRSSpace r (s + p) I x) :
    legendreForm g r s p x P ξ η = ∑ K : Fin p → Fin (Module.finrank ℝ (TangentSpace I x)),
      fiberInner g r s x (evalFirst p (fun i => tangentFrame g x (K i)) ξ)
        (P (prependCovectors p (fun i => g.inner x (tangentFrame g x (K i))) η)) := rfl

/-- `tangentFrame g x` is `g_x`-orthonormal. -/
theorem tangentFrame_inner (g : SmoothRiemannianMetric I M) (x : M)
    (i j : Fin (Module.finrank ℝ (TangentSpace I x))) :
    g.inner x (tangentFrame g x i) (tangentFrame g x j) = if i = j then 1 else 0 := by
  classical
  let cd : InnerProductSpace.Core ℝ (TangentSpace I x) := g.toRiemannianMetric.toCore x
  have hc : ContinuousAt (fun v : TangentSpace I x => cd.inner v v) 0 :=
    g.toRiemannianMetric.continuousAt x
  have hb : Bornology.IsVonNBounded ℝ
      {v : TangentSpace I x | RCLike.re (cd.inner v v) < 1} :=
    g.toRiemannianMetric.isVonNBounded x
  let _ : NormedAddCommGroup (TangentSpace I x) := cd.toNormedAddCommGroupOfTopology hc hb
  let _ : InnerProductSpace ℝ (TangentSpace I x) := InnerProductSpace.ofCoreOfTopology cd hc hb
  exact orthonormal_iff_ite.mp (stdOrthonormalBasis ℝ (TangentSpace I x)).orthonormal i j

/-- Evaluation of the first slot on `v`, as a continuous linear map. -/
def evalSlot (r s : ℕ) (x : M) (v : TangentSpace I x) :
    TensorRSSpace r (s + 1) I x →L[ℝ] TensorRSSpace r s I x where
  toFun ξ := (covGradBundleEquiv (I := I) (M := M) r s x).symm ξ v
  map_add' a b := by simp
  map_smul' c a := by simp
  cont := (continuous_eval_const v).comp
    (covGradBundleEquiv (I := I) (M := M) r s x).symm.continuous

theorem evalFirst_one {r s : ℕ} {x : M} (v : Fin 1 → TangentSpace I x)
    (ξ : TensorRSSpace r (s + 1) I x) :
    evalFirst 1 v ξ = evalSlot r s x (v 0) ξ := rfl

/-- Evaluating the first slot of `θ ⊗ η` on `v` gives `θ(v) η`. -/
theorem evalSlot_prependCovectors_one {r t : ℕ} {x : M} (v : TangentSpace I x)
    (θ : Fin 1 → (TangentSpace I x →L[ℝ] ℝ)) (η : TensorRSSpace r t I x) :
    evalSlot r t x v (prependCovectors 1 θ η) = θ 0 v • η := by
  change (covGradBundleEquiv (I := I) (M := M) r t x).symm
      (covGradBundleEquiv (I := I) (M := M) r t x ((θ 0).smulRight η)) v = θ 0 v • η
  rw [ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearMap.smulRight_apply]

variable (I M) in
/-- The `g`-trace of the first two slots: `P(Y) = Σⱼ Y(eⱼ, eⱼ, ·)`. -/
def traceCLM (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) :
    TensorRSSpace r (s + 1 + 1) I x →L[ℝ] TensorRSSpace r s I x :=
  ∑ j, (evalSlot r s x (tangentFrame g x j)).comp (evalSlot r (s + 1) x (tangentFrame g x j))

/-- The trace undoes prepending a frame covector: `tr (g(e_k, ·) ⊗ ξ) = ξ(e_k, ·)`. -/
theorem traceCLM_prependCovectors (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (k : Fin (Module.finrank ℝ (TangentSpace I x))) (ξ : TensorRSSpace r (s + 1) I x) :
    traceCLM I M g r s x (prependCovectors 1 (fun _ => g.inner x (tangentFrame g x k)) ξ) =
      evalSlot r s x (tangentFrame g x k) ξ := by
  classical
  simp only [traceCLM, FunLike.coe_sum, Finset.sum_apply,
    ContinuousLinearMap.comp_apply, evalSlot_prependCovectors_one, tangentFrame_inner]
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hjk
    simp [Ne.symm hjk]
  · simp

/-- The Legendre form of the trace is the sum over the frame of `|ξ(e_a, ·)|²`. -/
theorem legendreForm_traceCLM_eq_sum (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (ξ : TensorRSSpace r (s + 1) I x) :
    legendreForm g r s 1 x (traceCLM I M g r s x) ξ ξ =
      ∑ a : Fin (Module.finrank ℝ (TangentSpace I x)),
        fiberInner g r s x (evalSlot r s x (tangentFrame g x a) ξ)
          (evalSlot r s x (tangentFrame g x a) ξ) := by
  classical
  rw [legendreForm_eq]
  refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) _) _ _ (fun K => ?_)
  have hK : (fun i : Fin 1 => g.inner x (tangentFrame g x (K i))) =
      fun _ => g.inner x (tangentFrame g x (K 0)) := by
    funext i; rw [Subsingleton.elim i 0]
  rw [evalFirst_one, hK, traceCLM_prependCovectors]
  rfl

/-- For `(0, s)`-tensors, `|ξ|² = Σ_a |ξ(e_a, ·)|²` in the orthonormal frame. -/
theorem fiberInner_self_eq_sum_evalSlot (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (ξ : TensorRSSpace 0 (s + 1) I x) :
    fiberInner g 0 (s + 1) x ξ ξ =
      ∑ a : Fin (Module.finrank ℝ (TangentSpace I x)),
        fiberInner g 0 s x (evalSlot 0 s x (tangentFrame g x a) ξ)
          (evalSlot 0 s x (tangentFrame g x a) ξ) := by
  classical
  have horth := tangentFrame_inner g x
  have hrepr : ∀ t (S : TensorRSSpace 0 t I x),
      riemannianFiberNormSq (I := I) (M := M) g 0 t x S =
        ∑ K : Fin 0 → Fin (Module.finrank ℝ (TangentSpace I x)),
          ∑ J : Fin t → Fin (Module.finrank ℝ (TangentSpace I x)),
            fiberNormSqSummand (I := I) (M := M) g x 0 t S _ (tangentFrame g x) K J :=
    fun t S => riemannianFiberNormSq_eq_sum_fiberNormSqSummand_of_orthoFrame
      (I := I) (M := M) g t x S (tangentFrame g x) rfl horth
  have hinner : ∀ t (S : TensorRSSpace 0 t I x),
      fiberInner g 0 t x S S = riemannianFiberNormSq (I := I) (M := M) g 0 t x S :=
    fun t S => (riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 t x S).symm
  obtain ⟨Φ, rfl⟩ : ∃ Φ, covGradBundleEquiv (I := I) (M := M) 0 s x Φ = ξ :=
    (covGradBundleEquiv (I := I) (M := M) 0 s x).surjective ξ
  rw [hinner, riemannianFiberNormSq_covGradBundleEquiv_eq_sum_frame (I := I) (M := M) g s x Φ
    (tangentFrame g x) (fun k => k.elim0) (hrepr s) (hrepr (s + 1))]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [hinner]
  simp [evalSlot]

/-- **Non-vacuity of the Legendre condition.** The trace operator (principal coefficient of the
heat equation on `(0,s)`-tensors) satisfies `LegendreAt` with constant `1`. -/
theorem legendreAt_traceCLM (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M) :
    LegendreAt g 0 s 1 x (traceCLM I M g 0 s x) 1 := by
  refine ⟨one_pos, fun ξ => ?_⟩
  rw [legendreForm_traceCLM_eq_sum, ← fiberInner_self_eq_sum_evalSlot]
  norm_num

end ShortTime
