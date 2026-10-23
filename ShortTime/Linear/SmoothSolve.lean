import ShortTime.Linear.ModelSolve
import ShortTime.Linear.LimitFamily

/-!
# Smooth solutions of linear parabolic equations (`thm:linear` (ii))

For smooth forcing `f`, the isomorphism `∂ₜ - L : 𝒫^{n+1}_0 → 𝒫^n` (`LinearOp.isomorphism`) and the
density of smooth families give smooth `uₙ` with `uₙ(0) = 0` and `‖(∂ₜ - L)uₙ - f‖²_{𝒫^n} < 1/(n+1)`
(`LinearOp.exists_approx`). By the a priori estimate the `uₙ` are Cauchy in every `𝒫^q`, so by the
Sobolev embedding (`exists_fiberNormSq_le_parabolicInner`) every jet `∇^i ∂ₜ^j uₙ` is uniformly Cauchy
(`good_of_parabolic`). The limit `limFam T u` is jointly smooth, its jets are the limits of the jets
(`ShortTime.Linear.LimitFamily`), and passing to the limit in `∂ₜuₙ = Luₙ + (∂ₜ - L)uₙ` gives
`∂ₜu = Lu + f` (`LinearOp.exists_smooth_zero`). Shifting by the initial datum gives
`LinearOp.exists_smooth`.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
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

variable {g : SmoothRiemannianMetric I M} {s p : ℕ} {T : ℝ}

/-! ### Arithmetic -/

theorem sq_le_two_mul_add_aux {x a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : 0 ≤ x)
    (h : x ≤ a + b) : x ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

theorem mul_div_succ_le_aux {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) : C * (ε / (C + 1)) ≤ ε := by
  rw [mul_div_assoc', div_le_iff₀ (by linarith)]
  nlinarith

theorem cauchy_arith_aux {x a b C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε)
    (hx : x ≤ C * (2 * a + 2 * b)) (ha : a ≤ ε / (4 * (C + 1))) (hb : b ≤ ε / (4 * (C + 1))) :
    x ≤ ε := by
  have hC1 : 0 < C + 1 := by linarith
  have h4 : 2 * a + 2 * b ≤ ε / (C + 1) := by
    have e : ε / (C + 1) = 2 * (ε / (4 * (C + 1))) + 2 * (ε / (4 * (C + 1))) := by
      field_simp
      ring
    rw [e]
    linarith
  calc x ≤ C * (2 * a + 2 * b) := hx
    _ ≤ C * (ε / (C + 1)) := mul_le_mul_of_nonneg_left h4 hC
    _ ≤ ε := mul_div_succ_le_aux hC hε

theorem norm_lt_of_sq_le_aux {v C r ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε)
    (h1 : v ^ 2 ≤ C * r) (h2 : r ≤ ε ^ 2 / (C + 1)) : v < ε := by
  have h3 : C * r ≤ C * (ε ^ 2 / (C + 1)) := mul_le_mul_of_nonneg_left h2 hC
  have h4 : C * (ε ^ 2 / (C + 1)) < ε ^ 2 := by
    rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
    nlinarith [sq_pos_of_pos hε]
  exact lt_of_pow_lt_pow_left₀ 2 hε.le (by linarith)

/-- Eventually `1/(n+1) < ε`, for all later `n`. -/
theorem exists_one_div_succ_le {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, 1 / ((n : ℝ) + 1) ≤ ε := by
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  exact ⟨N, fun n hn => (Nat.one_div_le_one_div hn).trans hN.le⟩

/-! ### Parabolic norms -/

/-- `‖v‖_{𝒫^q} ≤ ‖v‖_{𝒫^n}` for `q ≤ n`. -/
theorem parabolicInner_mono_level (hT : 0 < T) {v : ℝ → SmoothCcTensor g 0 s}
    (hv : JointlySmoothOn g 0 s (Icc 0 T) v) {q n : ℕ} (hqn : q ≤ n) :
    parabolicInner g s p q T v v ≤ parabolicInner g s p n T v v := by
  rw [parabolicInner_self_eq hT hv, parabolicInner_self_eq hT hv]
  calc ∑ j ∈ Finset.range (q + 1),
        ∫ t in (0 : ℝ)..T, sobolevNormSq g 0 s (2 * p * (q - j)) (timeDerivIter T v j t)
      ≤ ∑ j ∈ Finset.range (q + 1),
        ∫ t in (0 : ℝ)..T, sobolevNormSq g 0 s (2 * p * (n - j)) (timeDerivIter T v j t) :=
        Finset.sum_le_sum fun j _ => integral_sobolevNormSq_mono hT
          (jointlySmoothOn_timeDerivIter hT hv j) (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right hqn j))
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.succ_le_succ hqn))
        fun j _ _ => intervalIntegral.integral_nonneg hT.le fun t _ => sobolevNormSq_nonneg s _ _

/-- `‖u - w‖² ≤ 2‖u‖² + 2‖w‖²` in `𝒫^q`. -/
theorem parabolicInner_sub_le {u w : ℝ → SmoothCcTensor g 0 s}
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u) (hw : JointlySmoothOn g 0 s (Icc 0 T) w) (q : ℕ) :
    parabolicInner g s p q T (fun t => u t - w t) (fun t => u t - w t) ≤
      2 * parabolicInner g s p q T u u + 2 * parabolicInner g s p q T w w := by
  have h := sq_le_two_mul_add_aux (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (norm_sub_le (ParabolicPre.mk (p := p) (m := q) u hu) (ParabolicPre.mk (p := p) (m := q) w hw))
  rw [ParabolicPre.norm_sq_eq, ParabolicPre.norm_sq_eq, ParabolicPre.norm_sq_eq] at h
  exact h

theorem timeDerivIter_sub (hT : 0 < T) {a b : ℕ} {A B : ℝ → SmoothCcTensor g a b}
    (hA : JointlySmoothOn g a b (Icc 0 T) A) (hB : JointlySmoothOn g a b (Icc 0 T) B) (j : ℕ)
    (t : ℝ) :
    timeDerivIter T (fun τ => A τ - B τ) j t = timeDerivIter T A j t - timeDerivIter T B j t := by
  have h := congrFun (timeDerivIter_add hT (jointlySmoothOn_sub hA hB) hB j) t
  simp only [sub_add_cancel] at h
  exact eq_sub_of_add_eq h.symm

theorem LinearOp.heatOp_sub (hT : 0 < T) (L : LinearOp g s p T) {u v : ℝ → SmoothCcTensor g 0 s}
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u) (hv : JointlySmoothOn g 0 s (Icc 0 T) v) (t : ℝ) :
    L.heatOp (fun τ => u τ - v τ) t = L.heatOp u t - L.heatOp v t := by
  have h := congrFun (L.heatOp_add hT (jointlySmoothOn_sub hu hv) hv) t
  simp only [sub_add_cancel] at h
  exact eq_sub_of_add_eq h.symm

/-! ### From parabolic Cauchy sequences to good sequences -/

/-- A sequence that is Cauchy in every `𝒫^q` is good: all its jets are uniformly Cauchy. -/
theorem good_of_parabolic (hT : 0 < T) (hp : 1 ≤ p) {w : ℕ → ℝ → SmoothCcTensor g 0 s}
    (hw : ∀ n, JointlySmoothOn g 0 s (Icc 0 T) (w n))
    (hC : ∀ q, ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ n' ≥ N,
      parabolicInner g s p q T (fun t => w n t - w n' t) (fun t => w n t - w n' t) ≤ ε) :
    Good T w := by
  refine ⟨hw, fun i j => ?_⟩
  obtain ⟨C, hC0, hCb⟩ := exists_fiberNormSq_le_parabolicInner (g := g) (s := s) hT p
    (m := j + 1 + (Module.finrank ℝ E / 2 + 1 + i)) (j := j) (i := i) (by omega) (by
      have e : j + 1 + (Module.finrank ℝ E / 2 + 1 + i) - j - 1 = Module.finrank ℝ E / 2 + 1 + i := by
        omega
      rw [e]
      exact Nat.le_mul_of_pos_left _ (by omega))
  intro ε hε
  obtain ⟨N, hN⟩ := hC (j + 1 + (Module.finrank ℝ E / 2 + 1 + i)) (ε / (C + 1)) (by positivity)
  refine ⟨N, fun n hn n' hn' t ht x => ?_⟩
  have e : iteratedCovGrad g 0 s i (timeDerivIter T (w n) j t) -
      iteratedCovGrad g 0 s i (timeDerivIter T (w n') j t) =
      iteratedCovGrad g 0 s i (timeDerivIter T (fun τ => w n τ - w n' τ) j t) := by
    rw [timeDerivIter_sub hT (hw n) (hw n') j t, iteratedCovGrad_sub]
  dsimp only
  rw [e]
  calc _ ≤ C * parabolicInner g s p (j + 1 + (Module.finrank ℝ E / 2 + 1 + i)) T
        (fun t => w n t - w n' t) (fun t => w n t - w n' t) :=
        hCb _ (jointlySmoothOn_sub (hw n) (hw n')) t ht x
    _ ≤ C * (ε / (C + 1)) := mul_le_mul_of_nonneg_left (hN n hn n' hn') hC0
    _ ≤ ε := mul_div_succ_le_aux hC0 hε

/-! ### Pointwise limits -/

theorem toModel_finset_sum {ι : Type*} (F : Finset ι) {a : ℕ} (v : ι → SmoothCcTensor g 0 a)
    (y : M) :
    TensorRSSpace.toModel ((∑ i ∈ F, v i).toSection y) =
      ∑ i ∈ F, TensorRSSpace.toModel ((v i).toSection y) := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | insert i F hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, SmoothCcTensor.toSection_add,
      ContMDiffSection.coe_add, Pi.add_apply, TensorRSSpace.toModel_add, ih]

/-- Fibre values whose fibre norms tend to zero tend to zero in the model fibre. -/
theorem tendsto_toModel_zero {a : ℕ} {y : M} {d : ℕ → TensorRSSpace 0 a I y}
    (h : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, riemannianFiberNormSq (I := I) (M := M) g 0 a y (d n) ≤ ε) :
    Tendsto (fun n => TensorRSSpace.toModel (d n)) atTop (𝓝 0) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_twist_le (g := g) y a isCompact_singleton
    (Set.singleton_subset_iff.2 (mem_chart_source H y))
  have hb : y ∈ (trivializationAt E (TangentSpace I) y).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact mem_chart_source H y
  have h0 : Tendsto (fun n => chartRSTwistInv (I := I) (M := M) y y 0 a
      (TensorRSSpace.toModel (d n))) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := h (ε ^ 2 / (C + 1)) (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    rw [dist_zero_right]
    exact norm_lt_of_sq_le_aux hC0 hε (hC y (Set.mem_singleton y) (d n)) (hN n hn)
  have h3 := ((continuous_chartRSTwist (I := I) (M := M) y y 0 a).tendsto 0).comp h0
  have hz : chartRSTwist (I := I) (M := M) y y 0 a 0 = 0 := by simp [chartRSTwist]
  rw [hz] at h3
  exact h3.congr fun n => chartRSTwist_chartRSTwistInv (I := I) (M := M) y hb 0 a _

namespace LinearOp

variable (L : LinearOp g s p T)

/-- `L` applied to the limit is the limit of `L` applied to the members. -/
theorem tendsto_apply_limFam (hT : 0 < T) {w : ℕ → ℝ → SmoothCcTensor g 0 s} (hw : Good T w)
    {t : ℝ} (ht : t ∈ Icc 0 T) (y : M) :
    Tendsto (fun n => TensorRSSpace.toModel ((L.apply t (w n t)).toSection y)) atTop
      (𝓝 (TensorRSSpace.toModel ((L.apply t (limFam T w t)).toSection y))) := by
  simp only [apply, toModel_finset_sum]
  refine tendsto_finsetSum _ fun k _ => ?_
  simp only [toModel_opField_apply]
  exact ((continuous_const.clm_comp continuous_id).tendsto _).comp
    (tendsto_jet_limFam hT hw ht k 0 y)

/-- **Approximate solutions.** Smooth `u` with `u(0) = 0` and `(∂ₜ - L)u` arbitrarily close to `f`
in `𝒫^n`. -/
theorem exists_approx (hp : 1 ≤ p) (hT : 0 < T) {lam : ℝ} (hL : L.IsParabolic lam)
    {f : ℝ → SmoothCcTensor g 0 s} (hf : JointlySmoothOn g 0 s (Icc 0 T) f) (n : ℕ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ u : ℝ → SmoothCcTensor g 0 s, JointlySmoothOn g 0 s (Icc 0 T) u ∧ u 0 = 0 ∧
      parabolicInner g s p n T (fun t => L.heatOp u t - f t) (fun t => L.heatOp u t - f t) < ε := by
  obtain ⟨Φ, hΦ⟩ := L.isomorphism hp hT hL (n + 1) (by omega)
  obtain ⟨δ, hδ, hδΦ⟩ := Metric.continuous_iff.mp Φ.continuous
    (Φ.symm (ParabolicSpace.ofSmooth f hf)) √ε (Real.sqrt_pos.2 hε)
  have hU : ((Φ.symm (ParabolicSpace.ofSmooth f hf) : ParabolicSpace.zeroAtStart g s p (n + 1) T) :
      ParabolicSpace g s p (n + 1) T) ∈ closure ((ParabolicPre.zeroAtStart.map
      (UniformSpace.Completion.toComplL (𝕜 := ℝ) (E := ParabolicPre g s p (n + 1) T)).toLinearMap :
        Submodule ℝ (ParabolicSpace g s p (n + 1) T)) : Set (ParabolicSpace g s p (n + 1) T)) := by
    rw [← Submodule.topologicalClosure_coe]
    exact (Φ.symm _).2
  obtain ⟨_, ⟨v, hv0, rfl⟩, hdist⟩ := Metric.mem_closure_iff.mp hU _ hδ
  refine ⟨v.family, v.2, hv0, ?_⟩
  have hz : Φ ⟨ParabolicSpace.ofSmooth v.family v.2,
      ParabolicSpace.ofSmooth_mem_zeroAtStart _ v.2 hv0⟩ =
      ParabolicSpace.ofSmooth (L.heatOp v.family) (L.jointlySmoothOn_heatOp hT v.2) :=
    hΦ _ _ v.2 (L.jointlySmoothOn_heatOp hT v.2) hv0 (L.solves_heatOp hT v.2)
  have hd := hδΦ ⟨ParabolicSpace.ofSmooth v.family v.2,
    ParabolicSpace.ofSmooth_mem_zeroAtStart _ v.2 hv0⟩ (by rw [dist_comm]; exact hdist)
  rw [hz, Φ.apply_symm_apply, dist_eq_norm] at hd
  have hn : ‖ParabolicSpace.ofSmooth (p := p) (m := n + 1 - 1) (L.heatOp v.family)
      (L.jointlySmoothOn_heatOp hT v.2) - ParabolicSpace.ofSmooth f hf‖ ^ 2 =
      parabolicInner g s p n T (fun t => L.heatOp v.family t - f t)
        (fun t => L.heatOp v.family t - f t) := by
    unfold ParabolicSpace.ofSmooth
    rw [← UniformSpace.Completion.coe_sub, UniformSpace.Completion.norm_coe, ParabolicPre.norm_sq_eq]
    rfl
  rw [← hn]
  calc _ < (√ε) ^ 2 := pow_lt_pow_left₀ hd (norm_nonneg _) (by norm_num)
    _ = ε := Real.sq_sqrt hε.le

/-- **Smooth solutions with zero initial datum.** -/
theorem exists_smooth_zero (hp : 1 ≤ p) (hT : 0 < T) {lam : ℝ} (hL : L.IsParabolic lam)
    {f : ℝ → SmoothCcTensor g 0 s} (hf : JointlySmoothOn g 0 s (Icc 0 T) f) :
    ∃ u : ℝ → SmoothCcTensor g 0 s, JointlySmoothOn g 0 s (Icc 0 T) u ∧ u 0 = 0 ∧
      L.Solves u f := by
  choose w hw hw0 hres using fun n : ℕ =>
    L.exists_approx hp hT hL hf n (Nat.one_div_pos_of_nat (α := ℝ) (n := n))
  obtain ⟨r, hr⟩ : ∃ r : ℕ → ℝ → SmoothCcTensor g 0 s, ∀ n t, r n t = L.heatOp (w n) t - f t :=
    ⟨_, fun _ _ => rfl⟩
  have hrf : ∀ n, r n = fun t => L.heatOp (w n) t - f t := fun n => funext (hr n)
  have hrs : ∀ n, JointlySmoothOn g 0 s (Icc 0 T) (r n) := fun n => by
    rw [hrf n]; exact jointlySmoothOn_sub (L.jointlySmoothOn_heatOp hT (hw n)) hf
  have hres' : ∀ q n, q ≤ n → parabolicInner g s p q T (r n) (r n) < 1 / ((n : ℝ) + 1) :=
    fun q n hqn => (parabolicInner_mono_level hT (hrs n) hqn).trans_lt (by rw [hrf n]; exact hres n)
  -- the approximants are Cauchy in every `𝒫^q`
  have hcauchy : ∀ q, ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ n' ≥ N,
      parabolicInner g s p q T (fun t => w n t - w n' t) (fun t => w n t - w n' t) ≤ ε := by
    intro q ε hε
    obtain ⟨C, hC0, hC⟩ := apriori_estimate hT hp (m := q + 1) (by omega) L L hL hL
    obtain ⟨N₀, hN₀⟩ := exists_one_div_succ_le (show 0 < ε / (4 * (C + 1)) by positivity)
    refine ⟨max q N₀, fun n hn n' hn' => ?_⟩
    have hd := jointlySmoothOn_sub (hw n) (hw n')
    have e : (lerp 0 L L).heatOp (fun τ => w n τ - w n' τ) = fun t => r n t - r n' t := by
      rw [heatOp_lerp]
      funext t
      rw [hr n t, hr n' t, L.heatOp_sub hT (hw n) (hw n') t]
      simp only [sub_zero, one_smul, zero_smul, add_zero]
      abel
    have h1 := hC 0 ⟨le_refl _, zero_le_one⟩ _ _ hd ((lerp 0 L L).jointlySmoothOn_heatOp hT hd)
      (by simp only [hw0, sub_self]) ((lerp 0 L L).solves_heatOp hT hd)
    rw [e] at h1
    have h2 := parabolicInner_sub_le (p := p) (hrs n) (hrs n') q
    have ha := (hres' q n (le_of_max_le_left hn)).le.trans (hN₀ n (le_of_max_le_right hn))
    have hb := (hres' q n' (le_of_max_le_left hn')).le.trans (hN₀ n' (le_of_max_le_right hn'))
    refine cauchy_arith_aux hC0 hε ?_ ha hb
    calc _ ≤ parabolicInner g s p (q + 1) T (fun t => w n t - w n' t) (fun t => w n t - w n' t) :=
          parabolicInner_mono_level hT hd (Nat.le_succ q)
      _ ≤ C * parabolicInner g s p q T (fun t => r n t - r n' t) (fun t => r n t - r n' t) := h1
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 hC0
  have hgood : Good T w := good_of_parabolic hT hp hw hcauchy
  have hu := jointlySmoothOn_limFam hT hgood
  refine ⟨limFam T w, hu, ?_, fun t ht x => ?_⟩
  · -- the initial value
    refine smoothCcTensor_eq_of_toFun fun x => ?_
    have h := tendsto_limFam hT hgood (left_mem_Icc.2 hT.le) x
    simp only [hw0] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  · -- the equation
    have hD := hasDerivWithinAt_timeDeriv hT hu ht x
    suffices hk : timeDeriv T (limFam T w) t = L.apply t (limFam T w t) + f t by
      rw [hk] at hD
      exact hD
    refine smoothCcTensor_eq_of_toFun fun y => ?_
    rw [timeDeriv_limFam hT hgood ht]
    -- the residuals tend to zero
    obtain ⟨C₀, hC₀0, hC₀⟩ := exists_fiberNormSq_le_parabolicInner (g := g) (s := s) hT p
      (m := 1 + (Module.finrank ℝ E / 2 + 1)) (j := 0) (i := 0) (by omega) (by
        have e : 1 + (Module.finrank ℝ E / 2 + 1) - 0 - 1 = Module.finrank ℝ E / 2 + 1 := by omega
        rw [e]
        exact Nat.le_mul_of_pos_left _ (by omega))
    have hR : Tendsto (fun n => TensorRSSpace.toModel ((r n t).toSection y)) atTop (𝓝 0) := by
      refine tendsto_toModel_zero (g := g) fun ε hε => ?_
      obtain ⟨N₀, hN₀⟩ := exists_one_div_succ_le (show 0 < ε / (C₀ + 1) by positivity)
      refine ⟨max (1 + (Module.finrank ℝ E / 2 + 1)) N₀, fun n hn => ?_⟩
      have h1 : riemannianFiberNormSq (I := I) (M := M) g 0 s y ((r n t).toSection y) ≤
          C₀ * parabolicInner g s p (1 + (Module.finrank ℝ E / 2 + 1)) T (r n) (r n) :=
        hC₀ (r n) (hrs n) t ht y
      have h2 := (hres' _ n (le_of_max_le_left hn)).le.trans (hN₀ n (le_of_max_le_right hn))
      calc _ ≤ _ := h1
        _ ≤ C₀ * (ε / (C₀ + 1)) := mul_le_mul_of_nonneg_left h2 hC₀0
        _ ≤ ε := mul_div_succ_le_aux hC₀0 hε
    have hsum : ∀ n, TensorRSSpace.toModel ((timeDeriv T (w n) t).toSection y) =
        TensorRSSpace.toModel ((L.apply t (w n t)).toSection y) +
          TensorRSSpace.toModel ((r n t).toSection y) +
            TensorRSSpace.toModel ((f t).toSection y) := by
      intro n
      have e : timeDeriv T (w n) t = L.apply t (w n t) + r n t + f t := by
        rw [hr n t]
        simp only [heatOp]
        abel
      rw [e, SmoothCcTensor.toSection_add, SmoothCcTensor.toSection_add]
      simp only [ContMDiffSection.coe_add, Pi.add_apply, TensorRSSpace.toModel_add]
    have hlim := ((L.tendsto_apply_limFam hT hgood ht y).add hR).add
      (tendsto_const_nhds (x := TensorRSSpace.toModel ((f t).toSection y)))
    have hlim' := tendsto_limFam hT (hgood.timeDeriv hT) ht y
    have heq := tendsto_nhds_unique hlim' (hlim.congr fun n => (hsum n).symm)
    rw [add_zero] at heq
    change _ = TensorRSSpace.toModel ((L.apply t (limFam T w t) + f t).toSection y)
    rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
      TensorRSSpace.toModel_add]
    exact heq

/-- **Linear parabolic theory, smooth form** (`thm:linear` (ii)). For a parabolic operator with
smooth coefficients, smooth forcing `f` and smooth initial datum `u₀`, there is a smooth solution
of `∂ₜu = Lu + f`, `u(0) = u₀`. It is unique by `unique_of_isParabolic`. -/
theorem exists_smooth (hp : 1 ≤ p) (hT : 0 < T) {lam : ℝ} (hL : L.IsParabolic lam)
    {f : ℝ → SmoothCcTensor g 0 s} (hf : JointlySmoothOn g 0 s (Icc 0 T) f)
    (u₀ : SmoothCcTensor g 0 s) :
    ∃ u : ℝ → SmoothCcTensor g 0 s, JointlySmoothOn g 0 s (Icc 0 T) u ∧ u 0 = u₀ ∧ L.Solves u f := by
  have hc := jointlySmoothOn_const g (Icc (0 : ℝ) T) u₀
  obtain ⟨v, hv, hv0, hsol⟩ := L.exists_smooth_zero hp hT hL
    (jointlySmoothOn_add hf (L.jointlySmoothOn_apply hc))
  refine ⟨fun t => v t + u₀, jointlySmoothOn_add hv hc, by simp only [hv0, zero_add],
    fun t ht x => ?_⟩
  have h := (hsol t ht x).add_const ((u₀ : SmoothCcTensor g 0 s).toFun x)
  beta_reduce at h
  have e : (L.apply t (v t) + (f t + L.apply t u₀)).toFun x =
      (L.apply t (v t + u₀) + f t).toFun x := by
    rw [L.apply_add]
    simp only [SmoothCcTensor.toFun_add, Pi.add_apply]
    abel
  rw [e] at h
  refine h.congr (fun τ _ => ?_) ?_ <;> simp only [SmoothCcTensor.toFun_add, Pi.add_apply]

end LinearOp

end ShortTime
