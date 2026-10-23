import ShortTime.Linear.SmoothSolve

/-!
# Continuous representatives: point evaluation of jets on `𝒫^m` (`lem:embedding`)

For `j < m` and `n/2 + 1 + i ≤ 2p(m - j - 1)`, the jet `∂ₜ^j ∇^i u(t, x)` of a smooth family is
bounded by `‖u‖_{𝒫^m}` (`exists_fiberNormSq_le_parabolicInner`), so it extends to elements of `𝒫^m`.

* `ParabolicSpace.evalJet g s p m T j i t x : 𝒫^m →L[ℝ] T⁰_{s+i}`-model: the continuous extension of
  `u ↦ ∂ₜ^j ∇^i u(t, x)` (read in the model fibre, `TensorRSSpace.toModel`), defined through
  `LinearMap.extendOfNorm`. `evalJet_ofSmooth`: on smooth families it is the jet.
* `exists_norm_evalJet_le`: `‖evalJet j i t x v‖ ≤ C ‖v‖`, uniformly in `t ∈ [0,T]` (for fixed `x`);
  `exists_fiberNormSq_evalJet_le`: the Riemannian fibre norm is bounded uniformly in `(t, x)`;
  `exists_norm_twist_evalJet_le`: the readings in the chart at `α` are bounded uniformly on
  compact subsets of the chart.
* `continuousOn_evalJet_chart`, `continuousOn_evalJet_chart_target` (**joint continuity**): in the
  chart and trivialization at any `α`, `(t, y) ↦ evalJet j i t y v` is continuous on
  `[0,T] × (chart target)`. `continuousOn_evalJet_time`: `t ↦ evalJet j i t x v` is continuous.
  `continuousOn_evalJet_bundle`: as a section of `T⁰_{s+i}M` over `M × [0,T]` it is continuous.
  (The model value `x ↦ toModel (·)` is read in the chart at `x`, which is not continuous in `x`,
  so joint continuity is stated in trivializations or in the bundle.)
* `evalJet_eq_zero_of_mem_zeroAtStart`: elements of `𝒫^m_0` vanish at `t = 0`.
* `eq_zero_of_ofSmooth_eq_zero`: for `m ≥ 1`, a smooth family that is `0` in `𝒫^m` vanishes on
  `[0,T]`.
* `levelIncl`: the inclusion `𝒫^n → 𝒫^m` for `m ≤ n` (`lem:parabolic-basic` (ii)), and
  `evalJet_levelIncl`: evaluation commutes with it.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral DifferentialGeometry.Analysis.Elliptic
open scoped Manifold ContDiff BigOperators Uniformity

set_option linter.unusedSectionVars false

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

variable {g : SmoothRiemannianMetric I M}

/-! ### Model norms and fibre norms at a point -/

theorem norm_comp_comp_le_aux {F₁ F₂ F₃ F₄ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
    [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [NormedAddCommGroup F₃] [NormedSpace ℝ F₃]
    [NormedAddCommGroup F₄] [NormedSpace ℝ F₄]
    (A : F₃ →L[ℝ] F₄) (X : F₁ →L[ℝ] F₂) (Z : F₂ →L[ℝ] F₃) :
    ‖A.comp (Z.comp X)‖ ≤ ‖A‖ * ‖X‖ * ‖Z‖ :=
  calc ‖A.comp (Z.comp X)‖ ≤ ‖A‖ * ‖Z.comp X‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖A‖ * (‖Z‖ * ‖X‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
    _ = ‖A‖ * ‖X‖ * ‖Z‖ := by ring

/-- At a fixed point, the model norm is bounded by the Riemannian fibre norm. -/
theorem exists_norm_toModel_sq_le (y : M) (a : ℕ) :
    ∃ K, 0 ≤ K ∧ ∀ w : TensorRSSpace 0 a I y,
      ‖TensorRSSpace.toModel w‖ ^ 2 ≤ K * riemannianFiberNormSq (I := I) (M := M) g 0 a y w := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_twist_le (g := g) y a isCompact_singleton
    (Set.singleton_subset_iff.2 (mem_chart_source H y))
  have hb : y ∈ (trivializationAt E (TangentSpace I) y).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact mem_chart_source H y
  obtain ⟨A, hA0, hA⟩ : ∃ A, 0 ≤ A ∧ ∀ Z : TensorRSModel 0 a ℝ E,
      ‖chartRSTwist (I := I) (M := M) y y 0 a Z‖ ≤ A * ‖Z‖ := by
    unfold chartRSTwist
    exact ⟨_, mul_nonneg (norm_nonneg _) (norm_nonneg _), fun Z => norm_comp_comp_le_aux _ _ Z⟩
  refine ⟨A ^ 2 * C, by positivity, fun w => ?_⟩
  have e : TensorRSSpace.toModel w = chartRSTwist (I := I) (M := M) y y 0 a
      (chartRSTwistInv (I := I) (M := M) y y 0 a (TensorRSSpace.toModel w)) :=
    (chartRSTwist_chartRSTwistInv (I := I) (M := M) y hb 0 a _).symm
  have h1 := hC y (Set.mem_singleton y) w
  have h2 : ‖TensorRSSpace.toModel w‖ ≤
      A * ‖chartRSTwistInv (I := I) (M := M) y y 0 a (TensorRSSpace.toModel w)‖ := by
    conv_lhs => rw [e]
    exact hA _
  calc ‖TensorRSSpace.toModel w‖ ^ 2
      ≤ (A * ‖chartRSTwistInv (I := I) (M := M) y y 0 a (TensorRSSpace.toModel w)‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h2 2
    _ = A ^ 2 * ‖chartRSTwistInv (I := I) (M := M) y y 0 a (TensorRSSpace.toModel w)‖ ^ 2 := by
        ring
    _ ≤ A ^ 2 * (C * riemannianFiberNormSq (I := I) (M := M) g 0 a y w) :=
        mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
    _ = A ^ 2 * C * riemannianFiberNormSq (I := I) (M := M) g 0 a y w := by ring

theorem chartRSTwistInv_sub_model (α b : M) (a : ℕ) (P Q : TensorRSModel 0 a ℝ E) :
    chartRSTwistInv (I := I) (M := M) α b 0 a (P - Q) =
      chartRSTwistInv (I := I) (M := M) α b 0 a P - chartRSTwistInv (I := I) (M := M) α b 0 a Q := by
  unfold chartRSTwistInv
  rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]

theorem mul_lt_of_lt_div_succ_aux {C d ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) (hd : d < ε / (C + 1)) :
    C * d < ε := by
  have h1 : C * d ≤ C * (ε / (C + 1)) := mul_le_mul_of_nonneg_left hd.le hC
  have h2 : C * (ε / (C + 1)) < ε := by
    rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
    nlinarith
  linarith

/-! ### Time derivatives for nonpositive `T` -/

section Linear

variable {s : ℕ} {T : ℝ}

theorem timeDerivIter_succ_of_not_pos (hT : ¬ 0 < T) (u : ℝ → SmoothCcTensor g 0 s) (j : ℕ)
    (t : ℝ) : timeDerivIter T u (j + 1) t = 0 := by
  change timeDeriv T (timeDerivIter T u j) t = 0
  rw [timeDeriv, dif_neg fun h => hT h.1]

theorem timeDerivIter_add_apply {u v : ℝ → SmoothCcTensor g 0 s}
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u) (hv : JointlySmoothOn g 0 s (Icc 0 T) v) (j : ℕ)
    (t : ℝ) :
    timeDerivIter T (fun τ => u τ + v τ) j t = timeDerivIter T u j t + timeDerivIter T v j t := by
  by_cases hT : 0 < T
  · exact congrFun (timeDerivIter_add hT hu hv j) t
  · cases j with
    | zero => rfl
    | succ j =>
      rw [timeDerivIter_succ_of_not_pos hT, timeDerivIter_succ_of_not_pos hT,
        timeDerivIter_succ_of_not_pos hT, add_zero]

theorem timeDerivIter_smul_apply {u : ℝ → SmoothCcTensor g 0 s} (c : ℝ)
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u) (j : ℕ) (t : ℝ) :
    timeDerivIter T (fun τ => c • u τ) j t = c • timeDerivIter T u j t := by
  by_cases hT : 0 < T
  · exact congrFun (timeDerivIter_smul hT c hu j) t
  · cases j with
    | zero => rfl
    | succ j =>
      rw [timeDerivIter_succ_of_not_pos hT, timeDerivIter_succ_of_not_pos hT, smul_zero]

end Linear

namespace ParabolicSpace

variable {s p m : ℕ} {T : ℝ}

/-! ### The evaluation functional -/

variable (g s p m T) in
/-- `u ↦ ∂ₜ^j ∇^i u(t, x)` on smooth families, in the model fibre. -/
def evalPre (j i : ℕ) (t : ℝ) (x : M) :
    ParabolicPre g s p m T →ₗ[ℝ] TensorRSModel 0 (s + i) ℝ E where
  toFun u := TensorRSSpace.toModel
    ((iteratedCovGrad g 0 s i (timeDerivIter T u.family j t)).toSection x)
  map_add' u v := by
    change TensorRSSpace.toModel ((iteratedCovGrad g 0 s i
        (timeDerivIter T (fun τ => u.family τ + v.family τ) j t)).toSection x) = _
    rw [timeDerivIter_add_apply (u := u.family) (v := v.family) u.2 v.2,
      Analysis.Spectral.iteratedCovGrad_add (I := I) (M := M) g 0 s i, SmoothCcTensor.toSection_add,
      ContMDiffSection.coe_add, Pi.add_apply, TensorRSSpace.toModel_add]
  map_smul' c u := by
    change TensorRSSpace.toModel ((iteratedCovGrad g 0 s i
        (timeDerivIter T (fun τ => c • u.family τ) j t)).toSection x) = _
    rw [timeDerivIter_smul_apply (u := u.family) c u.2,
      Analysis.Spectral.iteratedCovGrad_smul (I := I) (M := M) g 0 s i, SmoothCcTensor.toSection_smul,
      ContMDiffSection.coe_smul, Pi.smul_apply, TensorRSSpace.toModel_smul]
    rfl

theorem evalPre_apply (j i : ℕ) (t : ℝ) (x : M) (u : ParabolicPre g s p m T) :
    evalPre g s p m T j i t x u = TensorRSSpace.toModel
      ((iteratedCovGrad g 0 s i (timeDerivIter T u.family j t)).toSection x) := rfl

variable (g s p m T) in
/-- **Evaluation of the jet `∂ₜ^j ∇^i` at `(t, x)`** on `𝒫^m`: the continuous extension of `evalPre`
(meaningful for `j < m`, `n/2 + 1 + i ≤ 2p(m - j - 1)` and `t ∈ [0,T]`). -/
def evalJet (j i : ℕ) (t : ℝ) (x : M) :
    ParabolicSpace g s p m T →L[ℝ] TensorRSModel 0 (s + i) ℝ E :=
  (evalPre g s p m T j i t x).extendOfNorm
    (UniformSpace.Completion.toComplL (𝕜 := ℝ) (E := ParabolicPre g s p m T)).toLinearMap

theorem denseRange_toComplL :
    DenseRange (UniformSpace.Completion.toComplL (𝕜 := ℝ)
      (E := ParabolicPre g s p m T)).toLinearMap :=
  UniformSpace.Completion.denseRange_coe

theorem norm_toComplL (u : ParabolicPre g s p m T) :
    ‖(UniformSpace.Completion.toComplL (𝕜 := ℝ) (E := ParabolicPre g s p m T)).toLinearMap u‖ =
      ‖u‖ :=
  UniformSpace.Completion.norm_coe u

theorem norm_ofSmooth_sq {u : ℝ → SmoothCcTensor g 0 s} (hu : JointlySmoothOn g 0 s (Icc 0 T) u) :
    ‖ofSmooth (p := p) (m := m) u hu‖ ^ 2 = parabolicInner g s p m T u u := by
  unfold ofSmooth
  rw [UniformSpace.Completion.norm_coe, ParabolicPre.norm_sq_eq]
  rfl

/-- The bound on smooth families, uniform in `t ∈ [0,T]`, at a fixed point `x`. -/
theorem exists_evalPre_le (hT : 0 < T) {j i : ℕ} (hj : j < m)
    (hk : Module.finrank ℝ E / 2 + 1 + i ≤ 2 * p * (m - j - 1)) (x : M) :
    ∃ C, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) T, ∀ u : ParabolicPre g s p m T,
      ‖evalPre g s p m T j i t x u‖ ≤ C * ‖u‖ := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_fiberNormSq_le_parabolicInner (g := g) (s := s) hT p hj hk
  obtain ⟨K, hK, h₂⟩ := exists_norm_toModel_sq_le (g := g) x (s + i)
  refine ⟨√(K * C₁), Real.sqrt_nonneg _, fun t ht u => ?_⟩
  refine le_sqrt_mul_of_sq (norm_nonneg _) (norm_nonneg _) (mul_nonneg hK hC₁) ?_
  rw [ParabolicPre.norm_sq_eq, evalPre_apply]
  calc _ ≤ K * riemannianFiberNormSq (I := I) (M := M) g 0 (s + i) x
        ((iteratedCovGrad g 0 s i (timeDerivIter T u.family j t)).toSection x) := h₂ _
    _ ≤ K * (C₁ * parabolicInner g s p m T u.family u.family) :=
        mul_le_mul_of_nonneg_left (h₁ u.family u.2 t ht x) hK
    _ = K * C₁ * parabolicInner g s p m T u.family u.family := by ring

theorem evalJet_coe (hT : 0 < T) {j i : ℕ} (hj : j < m)
    (hk : Module.finrank ℝ E / 2 + 1 + i ≤ 2 * p * (m - j - 1)) {t : ℝ} (ht : t ∈ Icc 0 T)
    (x : M) (u : ParabolicPre g s p m T) :
    evalJet g s p m T j i t x (u : ParabolicSpace g s p m T) = evalPre g s p m T j i t x u := by
  obtain ⟨C, -, hC⟩ := exists_evalPre_le (g := g) (s := s) hT hj hk x
  exact LinearMap.extendOfNorm_eq denseRange_toComplL
    ⟨C, fun u => by rw [norm_toComplL]; exact hC t ht u⟩ u

/-- **Evaluation of smooth families**: `evalJet j i t x u = ∂ₜ^j ∇^i u(t, x)`. -/
theorem evalJet_ofSmooth (hT : 0 < T) {j i : ℕ} (hj : j < m)
    (hk : Module.finrank ℝ E / 2 + 1 + i ≤ 2 * p * (m - j - 1)) {t : ℝ} (ht : t ∈ Icc 0 T)
    (x : M) {u : ℝ → SmoothCcTensor g 0 s} (hu : JointlySmoothOn g 0 s (Icc 0 T) u) :
    evalJet g s p m T j i t x (ofSmooth u hu) =
      TensorRSSpace.toModel ((iteratedCovGrad g 0 s i (timeDerivIter T u j t)).toSection x) :=
  evalJet_coe hT hj hk ht x _

/-- The same, with the time derivatives of `∇^i u` (`mixedDeriv`). -/
theorem evalJet_ofSmooth' (hT : 0 < T) {j i : ℕ} (hj : j < m)
    (hk : Module.finrank ℝ E / 2 + 1 + i ≤ 2 * p * (m - j - 1)) {t : ℝ} (ht : t ∈ Icc 0 T)
    (x : M) {u : ℝ → SmoothCcTensor g 0 s} (hu : JointlySmoothOn g 0 s (Icc 0 T) u) :
    evalJet g s p m T j i t x (ofSmooth u hu) =
      (timeDerivIter T (fun τ => iteratedCovGrad g 0 s i (u τ)) j t).toFun x := by
  rw [evalJet_ofSmooth hT hj hk ht x hu, timeDerivIter_iteratedCovGrad hT hu i j ht]
  rfl

theorem evalJet_ofSmooth_eq_mixedDeriv (hT : 0 < T) {j i : ℕ} (hj : j < m)
    (hk : Module.finrank ℝ E / 2 + 1 + i ≤ 2 * p * (m - j - 1)) {t : ℝ} (ht : t ∈ Icc 0 T)
    (x : M) {u : ℝ → SmoothCcTensor g 0 s} (hu : JointlySmoothOn g 0 s (Icc 0 T) u) :
    evalJet g s p m T j i t x (ofSmooth u hu) = mixedDeriv g s T u j i x t := by
  rw [evalJet_ofSmooth' hT hj hk ht x hu, mixedDeriv_eq hT hu j i ht x]

/-- **The bound** `‖evalJet j i t x v‖ ≤ C ‖v‖`, uniformly in `t ∈ [0,T]`. -/
theorem exists_norm_evalJet_le (hT : 0 < T) {j i : ℕ} (hj : j < m)
    (hk : Module.finrank ℝ E / 2 + 1 + i ≤ 2 * p * (m - j - 1)) (x : M) :
    ∃ C, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) T, ∀ v : ParabolicSpace g s p m T,
      ‖evalJet g s p m T j i t x v‖ ≤ C * ‖v‖ := by
  obtain ⟨C, hC0, hC⟩ := exists_evalPre_le (g := g) (s := s) hT hj hk x
  exact ⟨C, hC0, fun t ht v => LinearMap.norm_extendOfNorm_apply_le denseRange_toComplL C
    (fun u => by rw [norm_toComplL]; exact hC t ht u) v⟩

/-- **The fibre-norm bound**, uniform in `(t, x) ∈ [0,T] × M`. -/
theorem exists_fiberNormSq_evalJet_le (hT : 0 < T) {j i : ℕ} (hj : j < m)
    (hk : Module.finrank ℝ E / 2 + 1 + i ≤ 2 * p * (m - j - 1)) :
    ∃ C, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, ∀ v : ParabolicSpace g s p m T,
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + i) x
        (TensorRSSpace.ofModel (evalJet g s p m T j i t x v)) ≤ C * ‖v‖ ^ 2 := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_fiberNormSq_le_parabolicInner (g := g) (s := s) hT p hj hk
  refine ⟨C₁, hC₁, fun t ht x v => ?_⟩
  -- the fibre norm, read in the model, is a continuous function
  have hcont : Continuous fun w : TensorRSModel 0 (s + i) ℝ E =>
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + i) x (TensorRSSpace.ofModel w) := by
    let B : TensorRSModel 0 (s + i) ℝ E →ₗ[ℝ] TensorRSModel 0 (s + i) ℝ E →ₗ[ℝ] ℝ :=
      LinearMap.mk₂ ℝ (fun w w' => tensorInnerPointwise (I := I) (M := M) g 0 (s + i) x w w')
        (fun w₁ w₂ w' => tensorInnerPointwise_add_left g 0 (s + i) x w₁ w₂ w')
        (fun c w w' => by rw [tensorInnerPointwise_smul_left, smul_eq_mul])
        (fun w w₁ w₂ => by
          rw [tensorInnerPointwise_symm g 0 (s + i) x w, tensorInnerPointwise_add_left,
            tensorInnerPointwise_symm g 0 (s + i) x w₁, tensorInnerPointwise_symm g 0 (s + i) x w₂])
        (fun c w w' => by
          rw [tensorInnerPointwise_symm g 0 (s + i) x w, tensorInnerPointwise_smul_left,
            tensorInnerPointwise_symm g 0 (s + i) x w', smul_eq_mul])
    let B' : TensorRSModel 0 (s + i) ℝ E →L[ℝ] TensorRSModel 0 (s + i) ℝ E →L[ℝ] ℝ :=
      LinearMap.toContinuousLinearMap
        ((LinearMap.toContinuousLinearMap : (TensorRSModel 0 (s + i) ℝ E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] _).toLinearMap ∘ₗ B)
    have e : (fun w : TensorRSModel 0 (s + i) ℝ E =>
        riemannianFiberNormSq (I := I) (M := M) g 0 (s + i) x (TensorRSSpace.ofModel w)) =
        fun w => B' w w := by
      funext w
      rw [riemannianFiberNormSq_eq_tensorInnerPointwise, TensorRSSpace.toModel_ofModel]
      rfl
    rw [e]
    exact (B'.continuous.clm_apply continuous_id)
  refine UniformSpace.Completion.induction_on v
    (isClosed_le (hcont.comp (evalJet g s p m T j i t x).continuous)
      (continuous_const.mul (continuous_norm.pow 2))) fun u => ?_
  rw [evalJet_coe hT hj hk ht x u, evalPre_apply, TensorRSSpace.ofModel_toModel,
    UniformSpace.Completion.norm_coe, ParabolicPre.norm_sq_eq]
  exact h₁ u.family u.2 t ht x

/-- **Locally uniform bound in charts**: on a compact set of chart points, the readings of
`evalJet j i t y v` in the trivialization at `α` are bounded by `C ‖v‖`. -/
theorem exists_norm_twist_evalJet_le (hT : 0 < T) {j i : ℕ} (hj : j < m)
    (hk : Module.finrank ℝ E / 2 + 1 + i ≤ 2 * p * (m - j - 1)) (α : M) {Ky : Set E}
    (hK : IsCompact Ky) (hKt : Ky ⊆ (extChartAt I α).target) :
    ∃ C, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) T, ∀ y ∈ Ky, ∀ v : ParabolicSpace g s p m T,
      ‖chartRSTwistInv (I := I) (M := M) α ((extChartAt I α).symm y) 0 (s + i)
        (evalJet g s p m T j i t ((extChartAt I α).symm y) v)‖ ≤ C * ‖v‖ := by
  set K := (extChartAt I α).symm '' Ky
  have hKc : IsCompact K := hK.image_of_continuousOn ((continuousOn_extChartAt_symm α).mono hKt)
  have hKs : K ⊆ (chartAt H α).source := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← extChartAt_source (I := I)]
    exact (extChartAt I α).map_target (hKt hy)
  obtain ⟨Ctw, hCtw, htw⟩ := exists_norm_twist_le (g := g) α (s + i) hKc hKs
  obtain ⟨C₁, hC₁, h₁⟩ := exists_fiberNormSq_le_parabolicInner (g := g) (s := s) hT p hj hk
  refine ⟨√(Ctw * C₁), Real.sqrt_nonneg _, fun t ht y hy v => ?_⟩
  refine UniformSpace.Completion.induction_on v
    (isClosed_le ((continuous_chartRSTwistInv (I := I) (M := M) α ((extChartAt I α).symm y) 0
      (s + i)).comp (evalJet g s p m T j i t ((extChartAt I α).symm y)).continuous).norm
      (continuous_const.mul continuous_norm)) fun u => ?_
  rw [evalJet_coe hT hj hk ht _ u, UniformSpace.Completion.norm_coe, evalPre_apply]
  refine le_sqrt_mul_of_sq (norm_nonneg _) (norm_nonneg _) (mul_nonneg hCtw hC₁) ?_
  rw [ParabolicPre.norm_sq_eq]
  calc _ ≤ Ctw * riemannianFiberNormSq (I := I) (M := M) g 0 (s + i) ((extChartAt I α).symm y)
        ((iteratedCovGrad g 0 s i (timeDerivIter T u.family j t)).toSection
          ((extChartAt I α).symm y)) := htw _ ⟨y, hy, rfl⟩ _
    _ ≤ Ctw * (C₁ * parabolicInner g s p m T u.family u.family) :=
        mul_le_mul_of_nonneg_left (h₁ u.family u.2 t ht _) hCtw
    _ = Ctw * C₁ * parabolicInner g s p m T u.family u.family := by ring

/-! ### Joint continuity -/

/-- **Joint continuity in charts**: in the chart and trivialization at `α`, the evaluation
`(t, y) ↦ evalJet j i t y v` is continuous on `[0,T] × Ky` for compact `Ky` in the chart target. -/
theorem continuousOn_evalJet_chart (hT : 0 < T) {j i : ℕ} (hj : j < m)
    (hk : Module.finrank ℝ E / 2 + 1 + i ≤ 2 * p * (m - j - 1)) (α : M) {Ky : Set E}
    (hK : IsCompact Ky) (hKt : Ky ⊆ (extChartAt I α).target) (v : ParabolicSpace g s p m T) :
    ContinuousOn (fun q : ℝ × E => chartRSTwistInv (I := I) (M := M) α ((extChartAt I α).symm q.2)
      0 (s + i) (evalJet g s p m T j i q.1 ((extChartAt I α).symm q.2) v)) (Icc 0 T ×ˢ Ky) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_twist_evalJet_le (g := g) (s := s) hT hj hk α hK hKt
  refine continuousOn_of_uniform_approx_of_continuousOn fun U hU => ?_
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_uniformity_dist.1 hU
  obtain ⟨u, hu⟩ := (UniformSpace.Completion.denseRange_coe (α := ParabolicPre g s p m T)).exists_dist_lt
    v (show 0 < ε / (C + 1) by positivity)
  refine ⟨fun q : ℝ × E => chartRSTwistInv (I := I) (M := M) α ((extChartAt I α).symm q.2) 0 (s + i)
      (evalJet g s p m T j i q.1 ((extChartAt I α).symm q.2) (u : ParabolicSpace g s p m T)),
    fun q hq => ?_, fun q hq => hεU ?_⟩
  · have hW := jointlySmoothOn_iteratedCovGrad (jointlySmoothOn_timeDerivIter hT u.2 j) i
    have h := (Vendor.chartRepr_euclid_jointContDiffWithinAt (I := I) g 0 (s + i)
      (fun τ => iteratedCovGrad g 0 s i (timeDerivIter T u.family j τ)) (Icc 0 T) α hW hq.1
      (hKt hq.2)).continuousWithinAt.mono (prod_mono subset_rfl hKt)
    have hval : ∀ q' ∈ Icc 0 T ×ˢ Ky,
        chartRSTwistInv (I := I) (M := M) α ((extChartAt I α).symm q'.2) 0 (s + i)
          (evalJet g s p m T j i q'.1 ((extChartAt I α).symm q'.2) (u : ParabolicSpace g s p m T)) =
        chartRd g α (iteratedCovGrad g 0 s i (timeDerivIter T u.family j q'.1)) q'.2 := by
      intro q' hq'
      rw [evalJet_coe hT hj hk hq'.1, evalPre_apply, chartRd_eq_twist α _ (hKt hq'.2)]
    exact h.congr hval (hval q hq)
  · rw [dist_eq_norm, ← chartRSTwistInv_sub_model, ← map_sub]
    refine (hC q.1 hq.1 q.2 hq.2 _).trans_lt (mul_lt_of_lt_div_succ_aux hC0 hε ?_)
    rw [← dist_eq_norm]
    exact hu

/-- **Joint continuity in charts**, on the whole chart target. -/
theorem continuousOn_evalJet_chart_target (hT : 0 < T) {j i : ℕ} (hj : j < m)
    (hk : Module.finrank ℝ E / 2 + 1 + i ≤ 2 * p * (m - j - 1)) (α : M)
    (v : ParabolicSpace g s p m T) :
    ContinuousOn (fun q : ℝ × E => chartRSTwistInv (I := I) (M := M) α ((extChartAt I α).symm q.2)
      0 (s + i) (evalJet g s p m T j i q.1 ((extChartAt I α).symm q.2) v))
      (Icc 0 T ×ˢ (extChartAt I α).target) := by
  intro q hq
  obtain ⟨r, hr, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.1
    ((isOpen_extChartAt_target (I := I) α).mem_nhds hq.2)
  have h := continuousOn_evalJet_chart hT hj hk α (isCompact_closedBall q.2 r) hsub v q
    ⟨hq.1, Metric.mem_closedBall_self hr.le⟩
  refine h.mono_of_mem_nhdsWithin (mem_nhdsWithin.2 ⟨univ ×ˢ Metric.ball q.2 r,
    isOpen_univ.prod Metric.isOpen_ball, ⟨trivial, Metric.mem_ball_self hr⟩, fun z hz =>
      ⟨hz.2.1, Metric.ball_subset_closedBall hz.1.2⟩⟩)

/-- **Continuity in time** at a fixed point (in the model fibre). -/
theorem continuousOn_evalJet_time (hT : 0 < T) {j i : ℕ} (hj : j < m)
    (hk : Module.finrank ℝ E / 2 + 1 + i ≤ 2 * p * (m - j - 1)) (x : M)
    (v : ParabolicSpace g s p m T) :
    ContinuousOn (fun t => evalJet g s p m T j i t x v) (Icc 0 T) := by
  have hb : x ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact mem_chart_source H x
  have h := (continuousOn_evalJet_chart_target hT hj hk x v).comp
    (continuousOn_id.prodMk continuousOn_const)
    (fun t ht => (⟨ht, mem_extChartAt_target (I := I) x⟩ :
      (t, extChartAt I x x) ∈ Icc 0 T ×ˢ (extChartAt I x).target))
  have h2 := (continuous_chartRSTwist (I := I) (M := M) x x 0 (s + i)).comp_continuousOn h
  refine h2.congr fun t _ => ?_
  simp only [Function.comp_apply, id, extChartAt_to_inv]
  exact (chartRSTwist_chartRSTwistInv (I := I) (M := M) x hb 0 (s + i) _).symm

/-- **Joint continuity as a section**: `(x, t) ↦ evalJet j i t x v` is a continuous section of
`T⁰_{s+i}M` over `M × [0,T]` (the continuous representative of `∂ₜ^j ∇^i v`). -/
theorem continuousOn_evalJet_bundle (hT : 0 < T) {j i : ℕ} (hj : j < m)
    (hk : Module.finrank ℝ E / 2 + 1 + i ≤ 2 * p * (m - j - 1)) (v : ParabolicSpace g s p m T) :
    ContinuousOn (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel 0 (s + i) ℝ E)
      (E := fun x : M => TensorRSSpace 0 (s + i) I x) q.1
      (TensorRSSpace.ofModel (evalJet g s p m T j i q.2 q.1 v))) (univ ×ˢ Icc 0 T) := by
  intro q₀ hq₀
  rw [FiberBundle.continuousWithinAt_totalSpace]
  refine ⟨continuousWithinAt_fst, ?_⟩
  have hbase : ∀ y ∈ (chartAt H q₀.1).source, y ∈ (trivializationAt (TensorRSModel 0 (s + i) ℝ E)
      (fun y : M => TensorRSSpace 0 (s + i) I y) q₀.1).baseSet := by
    intro y hy
    change y ∈ ((trivializationAt (Tensor0SBundle.Tensor0SModel 0 ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace 0 I y) q₀.1).baseSet) ∩
        ((trivializationAt (Tensor0SBundle.Tensor0SModel (s + i) ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace (s + i) I y) q₀.1).baseSet)
    refine ⟨?_, ?_⟩ <;>
      · change y ∈ (trivializationAt E (TangentSpace I) q₀.1).baseSet
        rw [TangentBundle.trivializationAt_baseSet]
        exact hy
  have hFc := continuousOn_evalJet_chart_target hT hj hk q₀.1 v
  have hmove : ContinuousOn (fun q : M × ℝ => (q.2, extChartAt I q₀.1 q.1))
      ((chartAt H q₀.1).source ×ˢ Icc 0 T) :=
    continuousOn_snd.prodMk ((continuousOn_extChartAt (I := I) q₀.1).comp continuousOn_fst
      (fun q hq => by rw [extChartAt_source]; exact hq.1))
  have hψ := (hFc.comp hmove (fun q hq => (⟨hq.2, (extChartAt I q₀.1).map_source
    (by rw [extChartAt_source]; exact hq.1)⟩ : (q.2, extChartAt I q₀.1 q.1) ∈
      Icc 0 T ×ˢ (extChartAt I q₀.1).target))) q₀ ⟨mem_chart_source H q₀.1, hq₀.2⟩
  have hval : ∀ q ∈ (chartAt H q₀.1).source ×ˢ Icc 0 T,
      ((trivializationAt (TensorRSModel 0 (s + i) ℝ E) (fun y : M => TensorRSSpace 0 (s + i) I y)
        q₀.1) ⟨q.1, TensorRSSpace.ofModel (evalJet g s p m T j i q.2 q.1 v)⟩).2 =
      chartRSTwistInv (I := I) (M := M) q₀.1
        ((extChartAt I q₀.1).symm (extChartAt I q₀.1 q.1)) 0 (s + i)
        (evalJet g s p m T j i q.2 ((extChartAt I q₀.1).symm (extChartAt I q₀.1 q.1)) v) := by
    intro q hq
    have hs : q.1 ∈ (extChartAt I q₀.1).source := by rw [extChartAt_source]; exact hq.1
    have e1 : ((trivializationAt (TensorRSModel 0 (s + i) ℝ E)
        (fun y : M => TensorRSSpace 0 (s + i) I y) q₀.1)
          ⟨q.1, TensorRSSpace.ofModel (evalJet g s p m T j i q.2 q.1 v)⟩).2 =
        (trivializationAt (TensorRSModel 0 (s + i) ℝ E) (fun y : M => TensorRSSpace 0 (s + i) I y)
          q₀.1).continuousLinearMapAt ℝ q.1
          (TensorRSSpace.ofModel (evalJet g s p m T j i q.2 q.1 v)) := by
      rw [Bundle.Trivialization.continuousLinearMapAt_apply,
        Bundle.Trivialization.coe_linearMapAt_of_mem _ (hbase q.1 hq.1)]
    rw [e1, triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel 0 (s + i) q₀.1 hq.1,
      TensorRSSpace.toModel_ofModel, (extChartAt I q₀.1).left_inv hs]
  have hU : (chartAt H q₀.1).source ×ˢ (univ : Set ℝ) ∈ 𝓝 q₀ :=
    ((chartAt H q₀.1).open_source.prod isOpen_univ).mem_nhds ⟨mem_chart_source H q₀.1, trivial⟩
  have hset : (chartAt H q₀.1).source ×ˢ Icc 0 T =
      ((univ : Set M) ×ˢ Icc 0 T) ∩ ((chartAt H q₀.1).source ×ˢ (univ : Set ℝ)) := by
    ext q; simp only [mem_prod, mem_inter_iff, mem_univ, true_and, and_true]; tauto
  rw [hset] at hψ
  refine ((continuousWithinAt_inter hU).mp hψ).congr_of_eventuallyEq ?_
    (hval q₀ ⟨mem_chart_source H q₀.1, hq₀.2⟩)
  filter_upwards [inter_mem_nhdsWithin ((univ : Set M) ×ˢ Icc 0 T) hU] with q hq
  exact hval q ⟨hq.2.1, hq.1.2⟩

/-! ### Zero initial values -/

theorem toModel_iteratedCovGrad_eq_zero {S : SmoothCcTensor g 0 s} (hS : S = 0) (i : ℕ) (x : M) :
    TensorRSSpace.toModel ((iteratedCovGrad g 0 s i S).toSection x) = 0 := by
  rw [show S = (0 : ℝ) • S by rw [zero_smul]; exact hS,
    Analysis.Spectral.iteratedCovGrad_smul (I := I) (M := M) g 0 s i, SmoothCcTensor.toSection_smul,
    ContMDiffSection.coe_smul, Pi.smul_apply, TensorRSSpace.toModel_smul, zero_smul]

/-- **Elements of `𝒫^m_0` vanish at `t = 0`.** -/
theorem evalJet_eq_zero_of_mem_zeroAtStart (hT : 0 < T) {i : ℕ} (hm : 0 < m)
    (hk : Module.finrank ℝ E / 2 + 1 + i ≤ 2 * p * (m - 1)) (x : M)
    {v : ParabolicSpace g s p m T} (hv : v ∈ zeroAtStart g s p m T) :
    evalJet g s p m T 0 i 0 x v = 0 := by
  have hk' : Module.finrank ℝ E / 2 + 1 + i ≤ 2 * p * (m - 0 - 1) := by rwa [Nat.sub_zero]
  have hle : ParabolicPre.zeroAtStart.map
      (UniformSpace.Completion.toComplL (𝕜 := ℝ) (E := ParabolicPre g s p m T)).toLinearMap ≤
      LinearMap.ker (evalJet g s p m T 0 i 0 x).toLinearMap := by
    rintro _ ⟨u, hu, rfl⟩
    rw [LinearMap.mem_ker]
    change evalJet g s p m T 0 i 0 x (u : ParabolicSpace g s p m T) = 0
    rw [evalJet_coe hT hm hk' ⟨le_rfl, hT.le⟩, evalPre_apply]
    exact toModel_iteratedCovGrad_eq_zero (show u.family 0 = 0 from hu) i x
  exact Submodule.topologicalClosure_minimal _ hle
    (evalJet g s p m T 0 i 0 x).isClosed_ker hv

/-! ### Injectivity on smooth families -/

/-- **A smooth family that is `0` in `𝒫^m`, `m ≥ 1`, vanishes on `[0,T]`.** -/
theorem eq_zero_of_ofSmooth_eq_zero (hT : 0 < T) (hm : 1 ≤ m) {u : ℝ → SmoothCcTensor g 0 s}
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u) (h : ofSmooth (p := p) (m := m) u hu = 0) {t : ℝ}
    (ht : t ∈ Icc 0 T) : u t = 0 := by
  have hP : parabolicInner g s p m T u u = 0 := by
    rw [← norm_ofSmooth_sq hu, h, norm_zero]
    norm_num
  have h1 := sobolevNormSq_timeDerivIter_le_parabolicInner (p := p) (m := m) (j := 0) (k := 0) hT hu
    (by omega) (Nat.zero_le _) ht
  rw [hP, mul_zero, sobolevNormSq_zero_eq] at h1
  have h2 : ‖u t‖ = 0 := by
    have e : ‖u t‖ = jetNorm g s 0 (timeDerivIter T u 0 t) := by
      rw [SmoothCcTensor.norm_def]; rfl
    rw [e]
    exact pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm h1 (sq_nonneg _))
  refine SmoothCcTensor.smoothCcTensor_eq_of_toL2_eq (u t) 0 ?_
  rw [map_zero, ← norm_eq_zero, SmoothCcTensor.norm_toL2, h2]

/-! ### Compatibility with the level inclusions -/

variable (g s p T) in
/-- A smooth family of `ParabolicPre` at another level. -/
def preCast (m n : ℕ) : ParabolicPre g s p n T →ₗ[ℝ] ParabolicPre g s p m T where
  toFun u := u
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem preCast_family {n : ℕ} (u : ParabolicPre g s p n T) :
    (preCast g s p T m n u).family = u.family := rfl

variable (g s p T) in
/-- **The inclusion `𝒫^n → 𝒫^m`** for `m ≤ n` (`lem:parabolic-basic` (ii)): the continuous
extension of the identity of smooth families. -/
def levelIncl (m n : ℕ) : ParabolicSpace g s p n T →L[ℝ] ParabolicSpace g s p m T :=
  ((UniformSpace.Completion.toComplL (𝕜 := ℝ) (E := ParabolicPre g s p m T)).toLinearMap ∘ₗ
    preCast g s p T m n).extendOfNorm
    (UniformSpace.Completion.toComplL (𝕜 := ℝ) (E := ParabolicPre g s p n T)).toLinearMap

theorem norm_preCast_le (hT : 0 < T) {n : ℕ} (hmn : m ≤ n) (u : ParabolicPre g s p n T) :
    ‖preCast g s p T m n u‖ ≤ ‖u‖ := by
  refine pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (two_ne_zero) |>.mp ?_
  rw [ParabolicPre.norm_sq_eq, ParabolicPre.norm_sq_eq, preCast_family]
  exact parabolicInner_mono_level hT u.2 hmn

theorem levelIncl_coe (hT : 0 < T) {n : ℕ} (hmn : m ≤ n) (u : ParabolicPre g s p n T) :
    levelIncl g s p T m n (u : ParabolicSpace g s p n T) =
      ((preCast g s p T m n u : ParabolicPre g s p m T) : ParabolicSpace g s p m T) :=
  LinearMap.extendOfNorm_eq denseRange_toComplL ⟨1, fun u => by
    rw [norm_toComplL, one_mul]
    exact (norm_toComplL _).trans_le (norm_preCast_le hT hmn u)⟩ u

theorem levelIncl_ofSmooth (hT : 0 < T) {n : ℕ} (hmn : m ≤ n) {u : ℝ → SmoothCcTensor g 0 s}
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u) :
    levelIncl g s p T m n (ofSmooth u hu) = ofSmooth u hu :=
  levelIncl_coe hT hmn _

theorem norm_levelIncl_le (hT : 0 < T) {n : ℕ} (hmn : m ≤ n) (v : ParabolicSpace g s p n T) :
    ‖levelIncl g s p T m n v‖ ≤ ‖v‖ := by
  have h := LinearMap.norm_extendOfNorm_apply_le
    (f := (UniformSpace.Completion.toComplL (𝕜 := ℝ) (E := ParabolicPre g s p m T)).toLinearMap ∘ₗ
      preCast g s p T m n) denseRange_toComplL 1 (fun u => by
        rw [norm_toComplL, one_mul]
        exact (norm_toComplL _).trans_le (norm_preCast_le hT hmn u)) v
  rwa [one_mul] at h

/-- **Evaluation commutes with the level inclusions.** -/
theorem evalJet_levelIncl (hT : 0 < T) {n j i : ℕ} (hmn : m ≤ n) (hj : j < m)
    (hk : Module.finrank ℝ E / 2 + 1 + i ≤ 2 * p * (m - j - 1)) {t : ℝ} (ht : t ∈ Icc 0 T)
    (x : M) (v : ParabolicSpace g s p n T) :
    evalJet g s p m T j i t x (levelIncl g s p T m n v) = evalJet g s p n T j i t x v := by
  have hj' : j < n := lt_of_lt_of_le hj hmn
  have hk' : Module.finrank ℝ E / 2 + 1 + i ≤ 2 * p * (n - j - 1) :=
    hk.trans (Nat.mul_le_mul_left _ (by omega))
  refine UniformSpace.Completion.induction_on v
    (isClosed_eq ((evalJet g s p m T j i t x).continuous.comp (levelIncl g s p T m n).continuous)
      (evalJet g s p n T j i t x).continuous) fun u => ?_
  rw [levelIncl_coe hT hmn, evalJet_coe hT hj hk ht, evalJet_coe hT hj' hk' ht, evalPre_apply,
    evalPre_apply, preCast_family]

end ParabolicSpace

end ShortTime
