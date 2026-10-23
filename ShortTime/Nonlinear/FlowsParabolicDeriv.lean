import ShortTime.Nonlinear.FlowsParabolicJet
import ShortTime.Nonlinear.FlowsDeriv
import ShortTime.Linear.TimeCalc

/-!
# Derivatives of the horizontal pullback in the flow parameter and in time

Paper: Lemma `lem:flows` (a), (b): the calculus of `Π_σ` on smooth families.

* `hasDerivAt_hpull`: `d/dσ (Π_σ v)(x) = (Π_σ ∇_X v)(x)` at every `σ` (group law and
  `hasDerivAt_hpull_zero`).
* `hasDerivAt_iteratedCovGrad_hpull`: the same for `∇^i Π_σ v`; the `σ`-derivative commutes with
  `∇^i` (`timeDeriv_iteratedCovGrad`, with `σ` as the time variable).
* `timeDerivIter_hpull`: `∂ₜ^j (Π_σ u) = Π_σ ∂ₜ^j u` on `[0,T]`, since `Π_σ` acts slice-wise by a
  fixed linear map at each point.
* `timeDerivIter_covAlong`: `∂ₜ^j ∇_X u = ∇_X ∂ₜ^j u`.
-/

noncomputable section

open Bundle Manifold Set Filter
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Analysis.ODE
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
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

variable (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
variable (g : SmoothRiemannianMetric I M) (s : ℕ)

/-! ### `P_σ(x)⁻¹` in the model fibre -/

/-- The model reading of `P_σ(x)⁻¹ : T⁰_s|_{φ_σ x} → T⁰_s|_x`. -/
def ptInvL (σ : ℝ) (x : M) : TensorRSModel 0 s ℝ E →L[ℝ] TensorRSModel 0 s ℝ E :=
  LinearMap.toContinuousLinearMap
    ((tensorRSSpaceContinuousLinearEquiv (I := I) 0 s x).toLinearEquiv.toLinearMap ∘ₗ
      (pt X g s σ x).symm.toLinearEquiv.toLinearMap ∘ₗ
      (tensorRSSpaceContinuousLinearEquiv (I := I) 0 s (flow X σ x)).symm.toLinearEquiv.toLinearMap)

theorem ptInvL_apply (σ : ℝ) (x : M) (w : TensorRSSpace 0 s I (flow X σ x)) :
    ptInvL X g s σ x (TensorRSSpace.toModel w) = TensorRSSpace.toModel ((pt X g s σ x).symm w) := by
  change tensorRSSpaceContinuousLinearEquiv (I := I) 0 s x ((pt X g s σ x).symm
      ((tensorRSSpaceContinuousLinearEquiv (I := I) 0 s (flow X σ x)).symm
        (tensorRSSpaceContinuousLinearEquiv (I := I) 0 s (flow X σ x) w))) =
    tensorRSSpaceContinuousLinearEquiv (I := I) 0 s x ((pt X g s σ x).symm w)
  rw [ContinuousLinearEquiv.symm_apply_apply]

theorem toModel_hpull (σ : ℝ) (w : SmoothCcTensor g 0 s) (x : M) :
    TensorRSSpace.toModel ((hpull X g s σ w).toSection x) =
      ptInvL X g s σ x (TensorRSSpace.toModel (w.toSection (flow X σ x))) :=
  (ptInvL_apply X g s σ x _).symm

/-! ### The derivative in `σ` -/

/-- **`d/dσ (Π_σ v)(x) = (Π_σ ∇_X v)(x)`**, at every `σ`. -/
theorem hasDerivAt_hpull (v : SmoothCcTensor g 0 s) (x : M) (σ₀ : ℝ) :
    HasDerivAt (fun σ => TensorRSSpace.toModel ((hpull X g s σ v).toSection x))
      (TensorRSSpace.toModel ((hpull X g s σ₀ (covAlong X g s v)).toSection x)) σ₀ := by
  have h0 := hasDerivAt_hpull_zero X g s v (flow X σ₀ x)
  have h1 := (ptInvL X g s σ₀ x).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h0
  have h2 : HasDerivAt (fun h => TensorRSSpace.toModel ((hpull X g s (σ₀ + h) v).toSection x))
      (TensorRSSpace.toModel ((hpull X g s σ₀ (covAlong X g s v)).toSection x)) 0 := by
    rw [toModel_hpull X g s σ₀ (covAlong X g s v) x]
    refine h1.congr_of_eventuallyEq (Eventually.of_forall fun h => ?_)
    simp only [Function.comp_apply]
    rw [← hpull_hpull, toModel_hpull X g s σ₀ (hpull X g s h v) x]
  have h3 : HasDerivAt (fun h => TensorRSSpace.toModel ((hpull X g s (σ₀ + h) v).toSection x))
      (TensorRSSpace.toModel ((hpull X g s σ₀ (covAlong X g s v)).toSection x)) (σ₀ - σ₀) := by
    rw [sub_self]; exact h2
  refine (h3.comp_sub_const σ₀ σ₀).congr_of_eventuallyEq (Eventually.of_forall fun σ => ?_)
  simp only [add_sub_cancel]

/-- A jointly smooth family on `ℝ`, shifted. -/
theorem jointlySmoothOn_shift {a b : ℕ} {u : ℝ → SmoothCcTensor g a b}
    (hu : JointlySmoothOn g a b univ u) (c : ℝ) (S : Set ℝ) :
    JointlySmoothOn g a b S (fun t => u (t + c)) := by
  have hφ : ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun q : M × ℝ => (q.1, q.2 + c)) :=
    contMDiff_fst.prodMk ((contDiff_id.add contDiff_const).contMDiff.comp contMDiff_snd)
  exact hu.comp hφ.contMDiffOn fun q _ => ⟨mem_univ _, mem_univ _⟩

/-- **`d/dσ ∇^i (Π_σ v)(x) = ∇^i (Π_σ ∇_X v)(x)`**. -/
theorem hasDerivAt_iteratedCovGrad_hpull (v : SmoothCcTensor g 0 s) (i : ℕ) (x : M) (σ₀ : ℝ) :
    HasDerivAt (fun σ => TensorRSSpace.toModel
        ((iteratedCovGrad g 0 s i (hpull X g s σ v)).toSection x))
      (TensorRSSpace.toModel
        ((iteratedCovGrad g 0 s i (hpull X g s σ₀ (covAlong X g s v))).toSection x)) σ₀ := by
  have hT : (0 : ℝ) < 2 := two_pos
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 2 := ⟨zero_le_one, one_le_two⟩
  obtain ⟨F, hF⟩ : ∃ F : ℝ → SmoothCcTensor g 0 s, F = fun t => hpull X g s (t + (σ₀ - 1)) v :=
    ⟨_, rfl⟩
  obtain ⟨F', hF'⟩ : ∃ F' : ℝ → SmoothCcTensor g 0 s,
      F' = fun t => hpull X g s (t + (σ₀ - 1)) (covAlong X g s v) := ⟨_, rfl⟩
  have hFs : JointlySmoothOn g 0 s (Icc 0 2) F := by
    rw [hF]; exact jointlySmoothOn_shift g (jointlySmoothOn_hpull_param X g s v) _ _
  have hd : ∀ t ∈ Icc (0 : ℝ) 2, timeDeriv 2 F t = F' t := fun t ht =>
    timeDeriv_eq hT hFs ht fun y => by
      rw [hF, hF']
      exact ((hasDerivAt_hpull X g s v y (t + (σ₀ - 1))).comp_add_const t (σ₀ - 1)).hasDerivWithinAt
  have hiter := timeDeriv_iteratedCovGrad hT hFs i h1
  have hD := hasDerivWithinAt_timeDeriv hT (jointlySmoothOn_iteratedCovGrad hFs i) h1 x
  rw [hiter, hd 1 h1] at hD
  have hD' := hD.hasDerivAt (Icc_mem_nhds zero_lt_one one_lt_two)
  have h3 : HasDerivAt (fun τ => TensorRSSpace.toModel ((iteratedCovGrad g 0 s i (F τ)).toSection x))
      (TensorRSSpace.toModel ((iteratedCovGrad g 0 s i (F' 1)).toSection x)) (σ₀ - (σ₀ - 1)) := by
    rw [sub_sub_cancel]; exact hD'
  have e1 : (1 : ℝ) + (σ₀ - 1) = σ₀ := by ring
  refine ((h3.comp_sub_const σ₀ (σ₀ - 1)).congr_of_eventuallyEq
    (Eventually.of_forall fun σ => ?_)).congr_deriv ?_
  · simp only [hF, sub_add_cancel]
  · simp only [hF', e1]

/-! ### Time derivatives -/

theorem timeDeriv_hpull {T : ℝ} (hT : 0 < T) {u : ℝ → SmoothCcTensor g 0 s}
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u) (σ : ℝ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    timeDeriv T (fun τ => hpull X g s σ (u τ)) t = hpull X g s σ (timeDeriv T u t) :=
  timeDeriv_eq hT (jointlySmoothOn_hpull X g s σ hu) ht fun x => by
    have h := (ptInvL X g s σ x).hasFDerivAt.comp_hasDerivWithinAt t
      (hasDerivWithinAt_timeDeriv hT hu ht (flow X σ x))
    simp only [SmoothCcTensor.toFun_apply, toModel_hpull]
    exact h

/-- **`∂ₜ^j (Π_σ u) = Π_σ ∂ₜ^j u`** on `[0,T]`. -/
theorem timeDerivIter_hpull {T : ℝ} (hT : 0 < T) {u : ℝ → SmoothCcTensor g 0 s}
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u) (σ : ℝ) :
    ∀ (j : ℕ) {t : ℝ}, t ∈ Icc 0 T →
      timeDerivIter T (fun τ => hpull X g s σ (u τ)) j t = hpull X g s σ (timeDerivIter T u j t)
  | 0, _, _ => rfl
  | j + 1, t, ht => by
    change timeDeriv T (timeDerivIter T (fun τ => hpull X g s σ (u τ)) j) t =
      hpull X g s σ (timeDeriv T (timeDerivIter T u j) t)
    have hj := jointlySmoothOn_timeDerivIter hT hu j
    rw [timeDeriv_congr hT (jointlySmoothOn_timeDerivIter hT (jointlySmoothOn_hpull X g s σ hu) j)
      (jointlySmoothOn_hpull X g s σ hj) (fun τ hτ => timeDerivIter_hpull hT hu σ j hτ) ht,
      timeDeriv_hpull X g s hT hj σ ht]

theorem jointlySmoothOn_covAlong {S : Set ℝ} {u : ℝ → SmoothCcTensor g 0 s}
    (hu : JointlySmoothOn g 0 s S u) :
    JointlySmoothOn g 0 s S (fun t => covAlong X g s (u t)) :=
  jointlySmoothOn_operatorFieldApply (_root_.ShortTime.jointlySmoothOn_const g S (insField g X))
    (jointlySmoothOn_covGrad hu)

theorem timeDeriv_covAlong {T : ℝ} (hT : 0 < T) {u : ℝ → SmoothCcTensor g 0 s}
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u) {t : ℝ} (ht : t ∈ Icc 0 T) :
    timeDeriv T (fun τ => covAlong X g s (u τ)) t = covAlong X g s (timeDeriv T u t) :=
  timeDeriv_eq hT (jointlySmoothOn_covAlong X g s hu) ht fun x => by
    have h := (hasDerivWithinAt_const t (Icc 0 T) ((insField g X).toFun x)).clm_comp
      (hasDerivWithinAt_timeDeriv hT (jointlySmoothOn_covGrad hu) ht x)
    rw [timeDeriv_covGrad hT hu ht, ContinuousLinearMap.zero_comp, zero_add] at h
    exact h

/-- **`∂ₜ^j ∇_X u = ∇_X ∂ₜ^j u`** on `[0,T]`. -/
theorem timeDerivIter_covAlong {T : ℝ} (hT : 0 < T) {u : ℝ → SmoothCcTensor g 0 s}
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u) :
    ∀ (j : ℕ) {t : ℝ}, t ∈ Icc 0 T →
      timeDerivIter T (fun τ => covAlong X g s (u τ)) j t = covAlong X g s (timeDerivIter T u j t)
  | 0, _, _ => rfl
  | j + 1, t, ht => by
    change timeDeriv T (timeDerivIter T (fun τ => covAlong X g s (u τ)) j) t =
      covAlong X g s (timeDeriv T (timeDerivIter T u j) t)
    have hj := jointlySmoothOn_timeDerivIter hT hu j
    rw [timeDeriv_congr hT (jointlySmoothOn_timeDerivIter hT (jointlySmoothOn_covAlong X g s hu) j)
      (jointlySmoothOn_covAlong X g s hj) (fun τ hτ => timeDerivIter_covAlong hT hu j hτ) ht,
      timeDeriv_covAlong X g s hT hj ht]

end HFlow

end ShortTime
