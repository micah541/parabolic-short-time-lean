import ShortTime.Nonlinear.Evaluation
import ShortTime.Nonlinear.ParabolicBound
import ShortTime.Nonlinear.Cutoff
import ShortTime.Linear.Divergence

/-!
# `L²(M × [0,T])` pairings of smooth families (for the closability of `𝒫^m`)

* `Closable.pair T A B = ∫₀ᵀ ⟨A(t), B(t)⟩_{L²} dt`; `parabolicInner_zero_eq`: it is the inner
  product of `𝒫^0`. `mixedInner_eq_pair`: the pairings of `𝒫^m` are `pair`s of the jet families
  `jetFam T j i u = ∇^i ∂ₜ^j u`.
* `pair_timeDeriv` (**integration by parts in time**): if `ψ(0) = ψ(T) = 0`, then
  `pair (∂ₜA) ψ = - pair A (∂ₜψ)`.
* `pair_covGrad` (**integration by parts in space**): `pair (∇A) Ψ = - pair A (div Ψ)`.
* `pair_cutoff_le`: with the cutoff `bump T δ` (`0` at `t = 0, T`, `1` on `[δ, T-δ]`),
  `pair ((1 - bump) f) ((1 - bump) f) ≤ C δ`.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral DifferentialGeometry.Analysis.Elliptic
open scoped Manifold ContDiff BigOperators

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

namespace Closable

/-! ### Real arithmetic -/

theorem le_zero_of_forall_le_mul {a K δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (h : ∀ δ : ℝ, 0 < δ → δ < δ₀ → a ≤ K * δ) : a ≤ 0 := by
  have ht : Tendsto (fun δ : ℝ => K * δ) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun δ : ℝ => K * δ) (𝓝 0) (𝓝 (K * 0)) :=
      (continuous_const_mul K).tendsto 0
    rw [mul_zero] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsGT hδ₀] with δ hδ using h δ hδ.1 hδ.2

theorem cut_arith {b F K : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hF : 0 ≤ F) (hFK : F ≤ K) :
    (1 - b) * ((1 - b) * F) ≤ K := by
  have h1 : 0 ≤ 1 - b := by linarith
  have h2 : 1 - b ≤ 1 := by linarith
  have h3 : (1 - b) * F ≤ F := by nlinarith
  have h4 : 0 ≤ (1 - b) * F := mul_nonneg h1 hF
  nlinarith

theorem mul_le_one_aux {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (_hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    x * y ≤ 1 := by nlinarith

/-! ### The pairing -/

variable (T : ℝ) in
/-- `∫₀ᵀ ⟨A(t), B(t)⟩_{L²} dt`. -/
def pair {a : ℕ} (A B : ℝ → SmoothCcTensor g 0 a) : ℝ :=
  ∫ t in Icc 0 T, inner ℝ (A t) (B t)

variable {T : ℝ}

theorem pair_congr_left {a : ℕ} {A A' : ℝ → SmoothCcTensor g 0 a} (h : EqOn A A' (Icc 0 T))
    (B : ℝ → SmoothCcTensor g 0 a) : pair T A B = pair T A' B :=
  setIntegral_congr_fun measurableSet_Icc fun t ht => by simp only [h ht]

/-- The inner product of `𝒫^0` is `pair`. -/
theorem parabolicInner_zero_eq (hT : 0 < T) {a p : ℕ} {A B : ℝ → SmoothCcTensor g 0 a}
    (hA : JointlySmoothOn g 0 a (Icc 0 T) A) (hB : JointlySmoothOn g 0 a (Icc 0 T) B) :
    parabolicInner g a p 0 T A B = pair T A B := by
  have e : parabolicInner g a p 0 T A B = mixedInner g a T A B 0 0 := by
    simp only [parabolicInner, zero_add, Nat.sub_self, mul_zero, Finset.sum_range_one]
  rw [e, mixedInner_eq hT hA hB]
  rfl

variable (T) in
/-- The jet family `∇^i ∂ₜ^j u`. -/
def jetFam {s : ℕ} (j i : ℕ) (u : ℝ → SmoothCcTensor g 0 s) : ℝ → SmoothCcTensor g 0 (s + i) :=
  fun t => iteratedCovGrad g 0 s i (timeDerivIter T u j t)

theorem jointlySmoothOn_jetFam (hT : 0 < T) {s : ℕ} {u : ℝ → SmoothCcTensor g 0 s}
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u) (j i : ℕ) :
    JointlySmoothOn g 0 (s + i) (Icc 0 T) (jetFam T j i u) :=
  jointlySmoothOn_iteratedCovGrad (jointlySmoothOn_timeDerivIter hT hu j) i

theorem mixedInner_eq_pair (hT : 0 < T) {s : ℕ} {u v : ℝ → SmoothCcTensor g 0 s}
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u) (hv : JointlySmoothOn g 0 s (Icc 0 T) v) (j i : ℕ) :
    mixedInner g s T u v j i = pair T (jetFam T j i u) (jetFam T j i v) := by
  rw [mixedInner_eq hT hu hv]
  refine setIntegral_congr_fun measurableSet_Icc fun t ht => ?_
  rw [timeDerivIter_iteratedCovGrad hT hu i j ht, timeDerivIter_iteratedCovGrad hT hv i j ht]
  rfl

/-- `∇^i ∂ₜ^{j+1} u = ∂ₜ (∇^i ∂ₜ^j u)` on `[0,T]`. -/
theorem jetFam_succ_time (hT : 0 < T) {s : ℕ} {u : ℝ → SmoothCcTensor g 0 s}
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u) (j i : ℕ) :
    EqOn (jetFam T (j + 1) i u) (timeDeriv T (jetFam T j i u)) (Icc 0 T) := fun _ ht =>
  (timeDeriv_iteratedCovGrad hT (jointlySmoothOn_timeDerivIter hT hu j) i ht).symm

/-- `∇^{i+1} ∂ₜ^j u = ∇ (∇^i ∂ₜ^j u)`. -/
theorem jetFam_succ_space {s : ℕ} (u : ℝ → SmoothCcTensor g 0 s) (j i : ℕ) (t : ℝ) :
    jetFam T j (i + 1) u t = covGrad (I := I) (M := M) g 0 (s + i) (jetFam T j i u t) := rfl

/-! ### Integration by parts in time -/

/-- **Integration by parts in time** against families vanishing at `t = 0` and `t = T`. -/
theorem pair_timeDeriv (hT : 0 < T) {a : ℕ} {A ψ : ℝ → SmoothCcTensor g 0 a}
    (hA : JointlySmoothOn g 0 a (Icc 0 T) A) (hψ : JointlySmoothOn g 0 a (Icc 0 T) ψ)
    (h0 : ψ 0 = 0) (hTz : ψ T = 0) :
    pair T (timeDeriv T A) ψ = - pair T A (timeDeriv T ψ) := by
  have hA' := jointlySmoothOn_timeDeriv hT hA
  have hψ' := jointlySmoothOn_timeDeriv hT hψ
  have hdA : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      HasDerivWithinAt (fun τ => (A τ).toFun x) ((timeDeriv T A t).toFun x) (Icc 0 T) t :=
    fun t ht x => hasDerivWithinAt_timeDeriv hT hA ht x
  have hdψ : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      HasDerivWithinAt (fun τ => (ψ τ).toFun x) ((timeDeriv T ψ t).toFun x) (Icc 0 T) t :=
    fun t ht x => hasDerivWithinAt_timeDeriv hT hψ ht x
  have hderiv : ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt (fun τ => inner ℝ (A τ) (ψ τ))
      (inner ℝ (timeDeriv T A t) (ψ t) + inner ℝ (A t) (timeDeriv T ψ t)) t := by
    intro t ht
    have hAψ := jointlySmoothOn_add hA hψ
    have h₁ := hasDerivAt_normSq g (u := fun τ => A τ + ψ τ)
      (v := timeDeriv T (fun τ => A τ + ψ τ)) hAψ (jointlySmoothOn_timeDeriv hT hAψ)
      (fun t ht x => hasDerivWithinAt_timeDeriv hT hAψ ht x) ht
    rw [timeDeriv_add hT hA hψ] at h₁
    have h₂ := hasDerivAt_normSq g hA hA' hdA ht
    have h₃ := hasDerivAt_normSq g hψ hψ' hdψ ht
    simp only [← SmoothCcTensor.inner_def] at h₁ h₂ h₃
    have key : (fun τ => inner ℝ (A τ) (ψ τ)) = fun τ =>
        (inner ℝ (A τ + ψ τ) (A τ + ψ τ) - inner ℝ (A τ) (A τ) - inner ℝ (ψ τ) (ψ τ)) / 2 := by
      funext τ
      rw [inner_add_left, inner_add_right, inner_add_right, real_inner_comm (A τ) (ψ τ)]
      ring
    rw [key]
    refine (((h₁.sub h₂).sub h₃).div_const 2).congr_deriv ?_
    rw [inner_add_left, inner_add_right, inner_add_right,
      real_inner_comm (timeDeriv T A t) (ψ t)]
    ring
  have hc1 : ContinuousOn (fun t => inner ℝ (timeDeriv T A t) (ψ t)) (Icc 0 T) := by
    simp only [SmoothCcTensor.inner_def]
    exact continuousOn_l2Pairing hT hA' hψ
  have hc2 : ContinuousOn (fun t => inner ℝ (A t) (timeDeriv T ψ t)) (Icc 0 T) := by
    simp only [SmoothCcTensor.inner_def]
    exact continuousOn_l2Pairing hT hA hψ'
  have hcont : ContinuousOn (fun τ => inner ℝ (A τ) (ψ τ)) (Icc 0 T) := by
    simp only [SmoothCcTensor.inner_def]
    exact continuousOn_l2Pairing hT hA hψ
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT.le hcont hderiv
    ((hc1.add hc2).intervalIntegrable_of_Icc hT.le)
  rw [intervalIntegral.integral_add (hc1.intervalIntegrable_of_Icc hT.le)
    (hc2.intervalIntegrable_of_Icc hT.le)] at hftc
  simp only [h0, hTz, inner_zero_right, sub_zero] at hftc
  unfold pair
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hT.le, ← intervalIntegral.integral_of_le hT.le]
  linarith

/-! ### Integration by parts in space -/

theorem jointlySmoothOn_covDivergence {a : ℕ} {S : Set ℝ} {Ψ : ℝ → SmoothCcTensor g 0 (a + 1)}
    (hΨ : JointlySmoothOn g 0 (a + 1) S Ψ) :
    JointlySmoothOn g 0 a S (fun t => covDivergence (I := I) (M := M) g a (Ψ t)) := by
  simp only [covDivergence_eq_trace_covGrad]
  exact jointlySmoothOn_operatorFieldApply (jointlySmoothOn_const g S _) (jointlySmoothOn_covGrad hΨ)

/-- **Integration by parts in space**: `pair (∇A) Ψ = - pair A (div Ψ)`. -/
theorem pair_covGrad {a : ℕ} (A : ℝ → SmoothCcTensor g 0 a)
    (Ψ : ℝ → SmoothCcTensor g 0 (a + 1)) :
    pair T (fun t => covGrad (I := I) (M := M) g 0 a (A t)) Ψ =
      - pair T A (fun t => covDivergence (I := I) (M := M) g a (Ψ t)) := by
  unfold pair
  rw [← integral_neg]
  congr 1
  funext t
  simp only [SmoothCcTensor.inner_def]
  exact tensorL2Inner_covGrad_eq_neg_tensorL2Inner_covDivergence g a (A t) (Ψ t)

/-! ### Cutoff in time near `0` and `T` -/

variable (T) in
/-- A smooth cutoff, `0` at `t = 0` and `t = T`, `1` on `[δ, T - δ]`, with values in `[0,1]`. -/
def bump (δ t : ℝ) : ℝ := Real.smoothTransition (t / δ) * Real.smoothTransition ((T - t) / δ)

theorem contDiff_bump (δ : ℝ) : ContDiff ℝ ∞ (bump T δ) :=
  (Real.smoothTransition.contDiff.comp (contDiff_id.div_const δ)).mul
    (Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const δ))

theorem bump_nonneg (δ t : ℝ) : 0 ≤ bump T δ t :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem bump_le_one (δ t : ℝ) : bump T δ t ≤ 1 :=
  mul_le_one_aux (Real.smoothTransition.nonneg _) (Real.smoothTransition.le_one _)
    (Real.smoothTransition.nonneg _) (Real.smoothTransition.le_one _)

theorem bump_zero (δ : ℝ) : bump T δ 0 = 0 := by
  unfold bump
  rw [zero_div, Real.smoothTransition.zero, zero_mul]

theorem bump_self (δ : ℝ) : bump T δ T = 0 := by
  unfold bump
  rw [sub_self, zero_div, Real.smoothTransition.zero, mul_zero]

theorem bump_eq_one {δ t : ℝ} (hδ : 0 < δ) (ht : t ∈ Icc δ (T - δ)) : bump T δ t = 1 := by
  unfold bump
  rw [Real.smoothTransition.one_of_one_le ((one_le_div hδ).mpr ht.1),
    Real.smoothTransition.one_of_one_le ((one_le_div hδ).mpr (by linarith [ht.2])), mul_one]

/-- `bump • f` is jointly smooth. -/
theorem jointlySmoothOn_bump_smul {a : ℕ} {f : ℝ → SmoothCcTensor g 0 a}
    (hf : JointlySmoothOn g 0 a (Icc 0 T) f) (δ : ℝ) :
    JointlySmoothOn g 0 a (Icc 0 T) (fun t => bump T δ t • f t) :=
  Cutoff.jointlySmoothOn_fun_smul (contDiff_bump δ).contDiffOn hf

/-- `(1 - bump) • f` is jointly smooth. -/
theorem jointlySmoothOn_one_sub_bump_smul {a : ℕ} {f : ℝ → SmoothCcTensor g 0 a}
    (hf : JointlySmoothOn g 0 a (Icc 0 T) f) (δ : ℝ) :
    JointlySmoothOn g 0 a (Icc 0 T) (fun t => (1 - bump T δ t) • f t) :=
  Cutoff.jointlySmoothOn_fun_smul (contDiff_const.sub (contDiff_bump δ)).contDiffOn hf

theorem setIntegral_le_of_cut {φ : ℝ → ℝ} {K δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ ≤ T)
    (hφ : ContinuousOn φ (Icc 0 T)) (hK : ∀ t ∈ Icc 0 T, φ t ≤ K)
    (hz : ∀ t ∈ Icc δ (T - δ), φ t = 0) :
    ∫ t in Icc 0 T, φ t ≤ 2 * K * δ := by
  have hT : 0 ≤ T := by linarith
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT]
  have i1 : IntervalIntegrable φ volume 0 δ :=
    (hφ.mono (Icc_subset_Icc le_rfl (by linarith))).intervalIntegrable_of_Icc hδ.le
  have i2 : IntervalIntegrable φ volume δ (T - δ) :=
    (hφ.mono (Icc_subset_Icc hδ.le (by linarith))).intervalIntegrable_of_Icc (by linarith)
  have i3 : IntervalIntegrable φ volume (T - δ) T :=
    (hφ.mono (Icc_subset_Icc (by linarith) le_rfl)).intervalIntegrable_of_Icc (by linarith)
  rw [← intervalIntegral.integral_add_adjacent_intervals (i1.trans i2) i3,
    ← intervalIntegral.integral_add_adjacent_intervals i1 i2]
  have e2 : ∫ t in δ..(T - δ), φ t = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun t ht => by
      rw [uIcc_of_le (by linarith)] at ht
      exact hz t ht)]
    simp
  have e1 : ∫ t in (0 : ℝ)..δ, φ t ≤ ∫ _t in (0 : ℝ)..δ, K :=
    intervalIntegral.integral_mono_on hδ.le i1 intervalIntegrable_const fun t ht =>
      hK t ⟨ht.1, by linarith [ht.2]⟩
  have e3 : ∫ t in (T - δ)..T, φ t ≤ ∫ _t in (T - δ)..T, K :=
    intervalIntegral.integral_mono_on (by linarith) i3 intervalIntegrable_const fun t ht =>
      hK t ⟨by linarith [ht.1], ht.2⟩
  rw [intervalIntegral.integral_const, smul_eq_mul] at e1 e3
  rw [e2]
  nlinarith

/-- **The cutoff error**: `pair ((1 - bump) f) ((1 - bump) f) ≤ C δ` for `0 < δ ≤ T/2`. -/
theorem exists_pair_cutoff_le (hT : 0 < T) {a : ℕ} {f : ℝ → SmoothCcTensor g 0 a}
    (hf : JointlySmoothOn g 0 a (Icc 0 T) f) :
    ∃ C, ∀ δ : ℝ, 0 < δ → 2 * δ ≤ T →
      pair T (fun t => (1 - bump T δ t) • f t) (fun t => (1 - bump T δ t) • f t) ≤ C * δ := by
  have hF : ContinuousOn (fun t => inner ℝ (f t) (f t)) (Icc 0 T) := by
    simp only [SmoothCcTensor.inner_def]
    exact continuousOn_l2Pairing hT hf hf
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hF
  refine ⟨2 * K, fun δ hδ hδT => ?_⟩
  unfold pair
  simp only [real_inner_smul_left, real_inner_smul_right]
  have hb : Continuous (bump T δ) := (contDiff_bump δ).continuous
  refine setIntegral_le_of_cut hδ hδT
    (((continuous_const.sub hb).continuousOn).mul (((continuous_const.sub hb).continuousOn).mul hF))
    (fun t ht => ?_) (fun t ht => ?_)
  · have h1 := hK t ht
    rw [Real.norm_eq_abs] at h1
    exact cut_arith (bump_nonneg δ t) (bump_le_one δ t) real_inner_self_nonneg
      ((le_abs_self _).trans h1)
  · rw [bump_eq_one hδ ht, sub_self, zero_mul]

end Closable

end ShortTime
