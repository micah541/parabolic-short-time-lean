import ShortTime.Linear.ParabolicOp
import ShortTime.Linear.Continuity

/-!
# The linear theorem in parabolic spaces (`thm:linear` (i))

* `LinearOp.heatExt`: the continuous extension of `∂ₜ - L` (`LinearOp.heatOp`) from smooth families
  to `𝒫^m → 𝒫^{m-1}`, through the bound `parabolicInner_heatOp_le`.
* `LinearOp.norm_le_heatExt_lerp`: the a priori estimate (`prop:apriori`) passes to `𝒫^m_0`, uniformly
  along a segment `L_θ = (1-θ)L₀ + θL₁`.
* `LinearOp.surjective_heatExt_of_approx`: if `∂ₜ - L₀` has dense range on smooth families vanishing
  at `t = 0`, it maps `𝒫^m_0` onto `𝒫^{m-1}` (its range is closed by the a priori estimate).
* `LinearOp.isomorphism_of_base`: the method of continuity (`lem:continuity`) transports this from a
  base operator `L₀` to any parabolic `L`.
`LinearOp.isomorphism` (`thm:linear` (i)) combines this with the polyharmonic base operator of
`prop:model`, in `ShortTime.Linear.ModelSolve`.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev DifferentialGeometry.Analysis.Spectral
open scoped Manifold ContDiff BigOperators

set_option linter.unusedSectionVars false

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

variable {g : SmoothRiemannianMetric I M}

theorem le_sqrt_mul_of_sq {x y C : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hC : 0 ≤ C)
    (h : x ^ 2 ≤ C * y ^ 2) : x ≤ √C * y := by
  rw [← Real.sqrt_sq hx, ← Real.sqrt_sq hy, ← Real.sqrt_mul hC]
  exact Real.sqrt_le_sqrt h

theorem timeDerivIter_zero_family {a b : ℕ} {T : ℝ} (hT : 0 < T) :
    ∀ j, timeDerivIter T (fun _ => (0 : SmoothCcTensor g a b)) j = fun _ => 0
  | 0 => rfl
  | j + 1 => by
    change timeDeriv T (timeDerivIter T (fun _ => (0 : SmoothCcTensor g a b)) j) = _
    rw [timeDerivIter_zero_family hT j]
    exact funext fun t => timeDeriv_const_zero hT t

section Lemmas

variable [CompleteSpace E]

namespace ParabolicPre

variable {s p m : ℕ} {T : ℝ}

theorem norm_sq_eq (u : ParabolicPre g s p m T) :
    ‖u‖ ^ 2 = parabolicInner g s p m T u.family u.family := by
  rw [← real_inner_self_eq_norm_sq]
  rfl

/-- A smooth family as an element of `ParabolicPre`. -/
def mk (u : ℝ → SmoothCcTensor g 0 s) (hu : JointlySmoothOn g 0 s (Icc 0 T) u) :
    ParabolicPre g s p m T := ⟨u, hu⟩

end ParabolicPre

namespace ParabolicSpace

variable {s p m : ℕ} {T : ℝ}

/-- Two smooth families that agree on `[0,T]` are the same element of `𝒫^m`. -/
theorem ofSmooth_congr (hT : 0 < T) {u v : ℝ → SmoothCcTensor g 0 s}
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u) (hv : JointlySmoothOn g 0 s (Icc 0 T) v)
    (h : EqOn u v (Icc 0 T)) :
    ofSmooth (p := p) (m := m) u hu = ofSmooth v hv := by
  rw [← dist_eq_zero]
  unfold ofSmooth
  rw [UniformSpace.Completion.dist_eq, dist_eq_norm]
  set w : ParabolicPre g s p m T := ParabolicPre.mk u hu - ParabolicPre.mk v hv with hw
  change ‖w‖ = 0
  have hws : JointlySmoothOn g 0 s (Icc 0 T) w.family := w.2
  have hzero : EqOn w.family (fun _ => 0) (Icc 0 T) := fun t ht => by
    change u t - v t = 0
    rw [h ht, sub_self]
  have hsq : ‖w‖ ^ 2 = 0 := by
    rw [ParabolicPre.norm_sq_eq, parabolicInner_self_eq hT hws]
    refine Finset.sum_eq_zero fun j _ => ?_
    refine (intervalIntegral.integral_congr fun t ht => ?_).trans intervalIntegral.integral_zero
    rw [uIcc_of_le hT.le] at ht
    have h1 := timeDerivIter_congr hT hws (jointlySmoothOn_const g _ 0) hzero j ht
    rw [h1, timeDerivIter_zero_family hT j]
    dsimp only
    rw [← zero_smul ℝ (0 : SmoothCcTensor g 0 s), sobolevNormSq_smul]
    ring
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq

end ParabolicSpace

namespace LinearOp

variable {s p : ℕ} {T : ℝ}

theorem apply_add (L : LinearOp g s p T) (t : ℝ) (u w : SmoothCcTensor g 0 s) :
    L.apply t (u + w) = L.apply t u + L.apply t w := by
  simp only [apply, iteratedCovGrad_add, operatorFieldApplication_add_right, Finset.sum_add_distrib]

theorem apply_smul (L : LinearOp g s p T) (t c : ℝ) (u : SmoothCcTensor g 0 s) :
    L.apply t (c • u) = c • L.apply t u := by
  simp only [apply, iteratedCovGrad_smul, operatorFieldApplication_smul_right, Finset.smul_sum]

theorem heatOp_add (hT : 0 < T) (L : LinearOp g s p T) {u v : ℝ → SmoothCcTensor g 0 s}
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u) (hv : JointlySmoothOn g 0 s (Icc 0 T) v) :
    L.heatOp (fun τ => u τ + v τ) = fun t => L.heatOp u t + L.heatOp v t := by
  funext t
  simp only [heatOp, timeDeriv_add hT hu hv, L.apply_add]
  abel

theorem heatOp_smul (hT : 0 < T) (L : LinearOp g s p T) (c : ℝ) {u : ℝ → SmoothCcTensor g 0 s}
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u) :
    L.heatOp (fun τ => c • u τ) = fun t => c • L.heatOp u t := by
  funext t
  simp only [heatOp, timeDeriv_smul hT c hu, L.apply_smul, smul_sub]

theorem heatOp_lerp (θ : ℝ) (L₀ L₁ : LinearOp g s p T) (u : ℝ → SmoothCcTensor g 0 s) :
    (lerp θ L₀ L₁).heatOp u = fun t => (1 - θ) • L₀.heatOp u t + θ • L₁.heatOp u t := by
  funext t
  simp only [heatOp, apply_lerp]
  module

/-- A smooth family solves `∂ₜu = Lu + (∂ₜ - L)u`. -/
theorem solves_heatOp (hT : 0 < T) (L : LinearOp g s p T) {u : ℝ → SmoothCcTensor g 0 s}
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u) : L.Solves u (L.heatOp u) := by
  intro t ht x
  have h := hasDerivWithinAt_timeDeriv hT hu ht x
  rw [show L.apply t (u t) + L.heatOp u t = timeDeriv T u t by
    simp only [heatOp]
    abel]
  exact h

/-- If `∂ₜu = Lu + w` on `[0,T]`, then `(∂ₜ - L)u = w` there. -/
theorem heatOp_eqOn_of_solves (hT : 0 < T) (L : LinearOp g s p T) {u w : ℝ → SmoothCcTensor g 0 s}
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u) (h : L.Solves u w) : EqOn (L.heatOp u) w (Icc 0 T) :=
  fun t ht => by
    simp only [heatOp]
    rw [timeDeriv_eq hT hu ht (h t ht), add_sub_cancel_left]

theorem IsParabolic.mono {L : LinearOp g s p T} {lam lam' : ℝ} (h : L.IsParabolic lam)
    (hlam' : 0 < lam') (hle : lam' ≤ lam) : L.IsParabolic lam' := by
  refine ⟨hlam', fun t ht x => ⟨hlam', fun ξ => le_trans ?_ ((h.2 t ht x).2 ξ)⟩⟩
  have h0 : 0 ≤ fiberInner g 0 (s + p) x ξ ξ := by
    by_cases hξ : ξ = 0
    · subst hξ
      simp [fiberInner]
    · exact ((Tensor.TensorRSRiemannianBundle.tensorRSRiemannianMetric (I := I) (M := M) g 0
        (s + p)).pos x ξ hξ).le
  exact mul_le_mul_of_nonneg_right hle h0

/-! ### `∂ₜ - L` on parabolic spaces -/

/-- `∂ₜ - L` on smooth families, as a linear map `ParabolicPre m → ParabolicPre n`. -/
def heatPre (hT : 0 < T) (L : LinearOp g s p T) (m n : ℕ) :
    ParabolicPre g s p m T →ₗ[ℝ] ParabolicPre g s p n T where
  toFun u := ParabolicPre.mk (L.heatOp u.family) (L.jointlySmoothOn_heatOp hT u.2)
  map_add' u v := Subtype.ext (L.heatOp_add hT u.2 v.2)
  map_smul' c u := Subtype.ext (L.heatOp_smul hT c u.2)

theorem heatPre_family (hT : 0 < T) (L : LinearOp g s p T) (m n : ℕ) (u : ParabolicPre g s p m T) :
    (L.heatPre hT m n u).family = L.heatOp u.family := rfl

theorem exists_heatPre_bound (hT : 0 < T) (L : LinearOp g s p T) {m : ℕ} (hm : 1 ≤ m) :
    ∃ C, ∀ u : ParabolicPre g s p m T, ‖L.heatPre hT m (m - 1) u‖ ≤ C * ‖u‖ := by
  obtain ⟨C, hC0, hC⟩ := L.parabolicInner_heatOp_le hT hm
  refine ⟨√C, fun u => le_sqrt_mul_of_sq (norm_nonneg _) (norm_nonneg _) hC0 ?_⟩
  rw [ParabolicPre.norm_sq_eq, ParabolicPre.norm_sq_eq, heatPre_family]
  exact hC u.family u.2

/-- `∂ₜ - L : ParabolicPre m → ParabolicPre (m-1)`, continuous. -/
def heatCLM (hT : 0 < T) (L : LinearOp g s p T) {m : ℕ} (hm : 1 ≤ m) :
    ParabolicPre g s p m T →L[ℝ] ParabolicPre g s p (m - 1) T :=
  (L.heatPre hT m (m - 1)).mkContinuousOfExistsBound (L.exists_heatPre_bound hT hm)

/-- **`∂ₜ - L : 𝒫^m → 𝒫^{m-1}`**, the continuous extension from smooth families. -/
def heatExt (hT : 0 < T) (L : LinearOp g s p T) {m : ℕ} (hm : 1 ≤ m) :
    ParabolicSpace g s p m T →L[ℝ] ParabolicSpace g s p (m - 1) T :=
  (UniformSpace.Completion.toComplL.comp (L.heatCLM hT hm)).extend UniformSpace.Completion.toComplL

theorem heatExt_coe (hT : 0 < T) (L : LinearOp g s p T) {m : ℕ} (hm : 1 ≤ m)
    (u : ParabolicPre g s p m T) :
    L.heatExt hT hm (u : ParabolicSpace g s p m T) =
      ((L.heatPre hT m (m - 1) u : ParabolicPre g s p (m - 1) T) : ParabolicSpace g s p (m - 1) T) := by
  have hd : DenseRange (UniformSpace.Completion.toComplL (𝕜 := ℝ) (E := ParabolicPre g s p m T)) := by
    rw [UniformSpace.Completion.coe_toComplL]
    exact UniformSpace.Completion.denseRange_coe
  have hi : IsUniformInducing
      (UniformSpace.Completion.toComplL (𝕜 := ℝ) (E := ParabolicPre g s p m T)) := by
    rw [UniformSpace.Completion.coe_toComplL]
    exact UniformSpace.Completion.isUniformInducing_coe _
  have h := ContinuousLinearMap.extend_eq
    (UniformSpace.Completion.toComplL.comp (L.heatCLM hT hm)) hd hi u
  rw [UniformSpace.Completion.coe_toComplL] at h
  exact h

theorem heatExt_ofSmooth (hT : 0 < T) (L : LinearOp g s p T) {m : ℕ} (hm : 1 ≤ m)
    {u : ℝ → SmoothCcTensor g 0 s} (hu : JointlySmoothOn g 0 s (Icc 0 T) u) :
    L.heatExt hT hm (ParabolicSpace.ofSmooth u hu) =
      ParabolicSpace.ofSmooth (L.heatOp u) (L.jointlySmoothOn_heatOp hT hu) :=
  L.heatExt_coe hT hm (ParabolicPre.mk u hu)

/-- **The a priori estimate on `𝒫^m_0`** (`prop:apriori`), uniformly along a segment. -/
theorem norm_le_heatExt_lerp (hT : 0 < T) (hp : 1 ≤ p) {m : ℕ} (hm : 1 ≤ m)
    (L₀ L₁ : LinearOp g s p T) {lam : ℝ} (h₀ : L₀.IsParabolic lam) (h₁ : L₁.IsParabolic lam) :
    ∃ C, 0 ≤ C ∧ ∀ θ ∈ Icc (0 : ℝ) 1, ∀ x ∈ ParabolicSpace.zeroAtStart g s p m T,
      ‖x‖ ≤ C * ‖((1 - θ) • L₀.heatExt hT hm + θ • L₁.heatExt hT hm) x‖ := by
  obtain ⟨C, hC0, hC⟩ := apriori_estimate hT hp hm L₀ L₁ h₀ h₁
  refine ⟨√C, Real.sqrt_nonneg _, fun θ hθ x hx => ?_⟩
  set A := (1 - θ) • L₀.heatExt hT hm + θ • L₁.heatExt hT hm with hA
  have hclosed : IsClosed {y : ParabolicSpace g s p m T | ‖y‖ ≤ √C * ‖A y‖} :=
    isClosed_le continuous_norm (continuous_const.mul (continuous_norm.comp A.continuous))
  have hx' : x ∈ closure ((ParabolicPre.zeroAtStart.map
      (UniformSpace.Completion.toComplL (𝕜 := ℝ) (E := ParabolicPre g s p m T)).toLinearMap :
        Submodule ℝ (ParabolicSpace g s p m T)) : Set (ParabolicSpace g s p m T)) := by
    rw [← Submodule.topologicalClosure_coe]
    exact hx
  refine closure_minimal ?_ hclosed hx'
  rintro _ ⟨u, hu0, rfl⟩
  change ‖(u : ParabolicSpace g s p m T)‖ ≤ √C * ‖A (u : ParabolicSpace g s p m T)‖
  have hAu : A (u : ParabolicSpace g s p m T) =
      (((1 - θ) • L₀.heatPre hT m (m - 1) u + θ • L₁.heatPre hT m (m - 1) u :
        ParabolicPre g s p (m - 1) T) : ParabolicSpace g s p (m - 1) T) := by
    change (1 - θ) • L₀.heatExt hT hm (u : ParabolicSpace g s p m T) +
      θ • L₁.heatExt hT hm (u : ParabolicSpace g s p m T) = _
    rw [heatExt_coe, heatExt_coe, UniformSpace.Completion.coe_add,
      UniformSpace.Completion.coe_smul, UniformSpace.Completion.coe_smul]
  rw [hAu, UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe]
  refine le_sqrt_mul_of_sq (norm_nonneg _) (norm_nonneg _) hC0 ?_
  rw [ParabolicPre.norm_sq_eq, ParabolicPre.norm_sq_eq]
  have key := hC θ hθ u.family ((lerp θ L₀ L₁).heatOp u.family) u.2
    ((lerp θ L₀ L₁).jointlySmoothOn_heatOp hT u.2) hu0 ((lerp θ L₀ L₁).solves_heatOp hT u.2)
  rw [heatOp_lerp] at key
  exact key

/-- **Dense range and the a priori estimate give surjectivity** (the last step of `prop:model`). If
`∂ₜ - L₀` has dense range on smooth families vanishing at `t = 0`, it maps `𝒫^m_0` onto
`𝒫^{m-1}`: its range is closed by the a priori estimate. -/
theorem surjective_heatExt_of_approx (hT : 0 < T) (hp : 1 ≤ p) {m : ℕ} (hm : 1 ≤ m)
    (L₀ : LinearOp g s p T) {lam : ℝ} (h₀ : L₀.IsParabolic lam)
    (happrox : ∀ f : ℝ → SmoothCcTensor g 0 s, JointlySmoothOn g 0 s (Icc 0 T) f → ∀ ε > 0,
      ∃ u : ℝ → SmoothCcTensor g 0 s, JointlySmoothOn g 0 s (Icc 0 T) u ∧ u 0 = 0 ∧
        parabolicInner g s p (m - 1) T (fun t => L₀.heatOp u t - f t)
          (fun t => L₀.heatOp u t - f t) < ε) :
    Function.Surjective
      ((L₀.heatExt hT hm).comp (ParabolicSpace.zeroAtStart g s p m T).subtypeL) := by
  set Z := ParabolicSpace.zeroAtStart g s p m T
  have : IsClosed (Z : Set (ParabolicSpace g s p m T)) := Submodule.isClosed_topologicalClosure _
  have : CompleteSpace Z := IsClosed.completeSpace_coe
  set B := (L₀.heatExt hT hm).comp Z.subtypeL with hB
  obtain ⟨C, hC0, hC⟩ := norm_le_heatExt_lerp hT hp hm L₀ L₀ h₀ h₀
  have hbound : ∀ x : Z, ‖x‖ ≤ C * ‖B x‖ := fun x => by
    have h := hC 0 ⟨le_refl _, zero_le_one⟩ x x.2
    simpa [hB] using h
  have hanti : AntilipschitzWith (Real.toNNReal C) B :=
    AddMonoidHomClass.antilipschitz_of_bound B fun x => by
      rw [Real.coe_toNNReal _ hC0]
      exact hbound x
  have hclosed : IsClosed (range B) := hanti.isClosed_range B.uniformContinuous
  have hdense : DenseRange B := by
    rw [Metric.denseRange_iff]
    intro y r hr
    obtain ⟨f, hf⟩ := Metric.denseRange_iff.mp UniformSpace.Completion.denseRange_coe y (r / 2)
      (by positivity)
    obtain ⟨u, hu, hu0, hlt⟩ := happrox f.family f.2 ((r / 2) ^ 2) (by positivity)
    refine ⟨⟨ParabolicSpace.ofSmooth u hu, ParabolicSpace.ofSmooth_mem_zeroAtStart u hu hu0⟩, ?_⟩
    have hBu : B ⟨ParabolicSpace.ofSmooth u hu, ParabolicSpace.ofSmooth_mem_zeroAtStart u hu hu0⟩ =
        ((L₀.heatPre hT m (m - 1) (ParabolicPre.mk u hu) : ParabolicPre g s p (m - 1) T) :
          ParabolicSpace g s p (m - 1) T) :=
      L₀.heatExt_coe hT hm (ParabolicPre.mk u hu)
    rw [hBu]
    have hd : dist (f : ParabolicSpace g s p (m - 1) T)
        (L₀.heatPre hT m (m - 1) (ParabolicPre.mk u hu) : ParabolicSpace g s p (m - 1) T) < r / 2 := by
      rw [UniformSpace.Completion.dist_eq, dist_comm, dist_eq_norm]
      have hsq : ‖L₀.heatPre hT m (m - 1) (ParabolicPre.mk u hu) - f‖ ^ 2 < (r / 2) ^ 2 := by
        rw [ParabolicPre.norm_sq_eq]
        exact hlt
      exact lt_of_pow_lt_pow_left₀ 2 (by positivity) hsq
    calc dist y _ ≤ dist y (f : ParabolicSpace g s p (m - 1) T) +
          dist (f : ParabolicSpace g s p (m - 1) T) _ := dist_triangle _ _ _
      _ < r / 2 + r / 2 := add_lt_add hf hd
      _ = r := by ring
  intro y
  have hy : y ∈ range B := by
    rw [← hclosed.closure_eq, hdense.closure_range]
    trivial
  exact hy

/-- **The method of continuity in parabolic spaces.** If `∂ₜ - L₀` has dense range on smooth
families vanishing at `t = 0`, then for every parabolic `L`, `∂ₜ - L : 𝒫^m_0 → 𝒫^{m-1}` is a linear
homeomorphism extending `∂ₜ - L` on smooth families. -/
theorem isomorphism_of_base (hT : 0 < T) (hp : 1 ≤ p) {m : ℕ} (hm : 1 ≤ m)
    (L₀ L : LinearOp g s p T) {lam₀ lam : ℝ} (h₀ : L₀.IsParabolic lam₀) (hL : L.IsParabolic lam)
    (happrox : ∀ f : ℝ → SmoothCcTensor g 0 s, JointlySmoothOn g 0 s (Icc 0 T) f → ∀ ε > 0,
      ∃ u : ℝ → SmoothCcTensor g 0 s, JointlySmoothOn g 0 s (Icc 0 T) u ∧ u 0 = 0 ∧
        parabolicInner g s p (m - 1) T (fun t => L₀.heatOp u t - f t)
          (fun t => L₀.heatOp u t - f t) < ε) :
    ∃ Φ : ParabolicSpace.zeroAtStart g s p m T ≃L[ℝ] ParabolicSpace g s p (m - 1) T,
      ∀ (u w : ℝ → SmoothCcTensor g 0 s) (hu : JointlySmoothOn g 0 s (Icc 0 T) u)
        (hw : JointlySmoothOn g 0 s (Icc 0 T) w) (h0 : u 0 = 0), L.Solves u w →
        (Φ ⟨ParabolicSpace.ofSmooth u hu, ParabolicSpace.ofSmooth_mem_zeroAtStart u hu h0⟩ :
          ParabolicSpace g s p (m - 1) T) = ParabolicSpace.ofSmooth w hw := by
  set Z := ParabolicSpace.zeroAtStart g s p m T
  have : IsClosed (Z : Set (ParabolicSpace g s p m T)) := Submodule.isClosed_topologicalClosure _
  have : CompleteSpace Z := IsClosed.completeSpace_coe
  have hlam : 0 < min lam₀ lam := lt_min h₀.1 hL.1
  obtain ⟨C, hC0, hC⟩ := norm_le_heatExt_lerp hT hp hm L₀ L (h₀.mono hlam (min_le_left _ _))
    (hL.mono hlam (min_le_right _ _))
  set A := (L₀.heatExt hT hm).comp Z.subtypeL with hA
  set B := (L.heatExt hT hm).comp Z.subtypeL with hB
  have hAs : Function.Surjective A := surjective_heatExt_of_approx hT hp hm L₀ h₀ happrox
  have hBs : Function.Surjective B := surjective_of_continuity A B C (fun θ hθ x => by
      have h := hC θ hθ x x.2
      simpa [hA, hB] using h) hAs
  have hker : LinearMap.ker (B : Z →ₗ[ℝ] ParabolicSpace g s p (m - 1) T) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    have h := hC 1 ⟨zero_le_one, le_refl _⟩ x x.2
    have hBx : ((1 - 1 : ℝ) • L₀.heatExt hT hm + (1 : ℝ) • L.heatExt hT hm)
        (x : ParabolicSpace g s p m T) = 0 := by
      simpa [hB] using hx
    rw [hBx, norm_zero, mul_zero] at h
    exact Subtype.ext (norm_le_zero_iff.mp h)
  have hrange : LinearMap.range (B : Z →ₗ[ℝ] ParabolicSpace g s p (m - 1) T) = ⊤ :=
    LinearMap.range_eq_top.mpr hBs
  refine ⟨ContinuousLinearEquiv.ofBijective B hker hrange, fun u w hu hw h0 hsol => ?_⟩
  change L.heatExt hT hm (ParabolicSpace.ofSmooth u hu) = _
  rw [heatExt_ofSmooth]
  exact ParabolicSpace.ofSmooth_congr hT _ hw (L.heatOp_eqOn_of_solves hT hu hsol)

end LinearOp

end Lemmas

end ShortTime
