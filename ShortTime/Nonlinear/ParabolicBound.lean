import ShortTime.Nonlinear.JetSq
import ShortTime.Linear.Embedding

/-!
# The integral layer of the composition estimate (`prop:nemytskii`, `lem:parabolic-basic` (i))

* `parabolicJetSq g p N T V t x = Σ_{2pj+i ≤ 2pN} |∂ₜ^j ∇^i V(t,x)|²` is the integrand of
  `‖V‖²_{𝒫^N}`: `integral_parabolicJetInt` says `∫₀ᵀ ∫_M parabolicJetSq = ‖V‖²_{𝒫^N}`.
* `parabolicInner_le_of_jetSq_le` (**integral of a pointwise bound**): if every
  `|∂ₜ^j ∇^i φ|²` with `2pj + i ≤ 2pN` is bounded on `M × [0,T]` by
  `C (1 + Σ_c parabolicJetSq (V c))`, then `‖φ‖²_{𝒫^N} ≤ C' (1 + Σ_c ‖V c‖²_{𝒫^N})` with
  `C' = C · #{(j,i)} · (T vol(M) + 1)`.
* `exists_jetSq_le_parabolicInner` (**low jets are bounded by the norm**): for
  `N ≥ N₀ = ⌊n/2p⌋ + 3` and `2 (2pj + i) ≤ 2pN`, `|∂ₜ^j ∇^i V|² ≤ C ‖V‖²_{𝒫^N}` on `M × [0,T]`
  (Step 1 of `prop:nemytskii`, from `exists_fiberNormSq_le_parabolicInner`).
* `parabolicInner_iteratedCovGrad_le`, `parabolicInner_timeDeriv_le` (`lem:parabolic-basic` (i)):
  `‖∇^k u‖_{𝒫^N} ≤ ‖u‖_{𝒫^{N+1}}` for `k ≤ 2p`, and `‖∂ₜu‖_{𝒫^N} ≤ ‖u‖_{𝒫^{N+1}}`.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory
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

/-! ### Arithmetic of the parabolic index set -/

/-- The parabolic weight condition `2pj + i ≤ 2pN` is `j ≤ N ∧ i ≤ 2p(N - j)` for `p ≥ 1`. -/
theorem weight_le_iff {p N j i : ℕ} (hp : 1 ≤ p) :
    2 * p * j + i ≤ 2 * p * N ↔ j ≤ N ∧ i ≤ 2 * p * (N - j) := by
  constructor
  · intro h
    have hj : j ≤ N := by
      by_contra hc
      have h1 : 2 * p * (N + 1) ≤ 2 * p * j := Nat.mul_le_mul_left _ (by omega)
      rw [Nat.mul_succ] at h1
      omega
    refine ⟨hj, ?_⟩
    have e : 2 * p * (N - j) + 2 * p * j = 2 * p * N := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hj]
    omega
  · rintro ⟨hj, hi⟩
    have e : 2 * p * (N - j) + 2 * p * j = 2 * p * N := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hj]
    omega

/-- The arithmetic of Step 1 of `prop:nemytskii`: for `N ≥ ⌊n/2p⌋ + 3` and `2(2pj + i) ≤ 2pN`,
the hypotheses of `exists_fiberNormSq_le_parabolicInner` hold. -/
theorem embedding_arith {n p N j i : ℕ} (hp : 1 ≤ p) (hN : n / (2 * p) + 3 ≤ N)
    (hw : 2 * (2 * p * j + i) ≤ 2 * p * N) : j < N ∧ n / 2 + 1 + i ≤ 2 * p * (N - j - 1) := by
  have hp2 : 0 < 2 * p := by omega
  have hjN : 2 * j ≤ N := by
    refine Nat.le_of_mul_le_mul_left ?_ hp2
    have e : 2 * p * (2 * j) = 2 * (2 * p * j) := by ring
    omega
  have h3 : 3 ≤ N := le_trans (Nat.le_add_left 3 _) hN
  have hj : j < N := by omega
  refine ⟨hj, ?_⟩
  have e1 : 2 * p * (N - j - 1) + (2 * p * j + 2 * p) = 2 * p * N := by
    rw [← Nat.mul_succ, ← Nat.mul_add]
    congr 1
    omega
  have e2 := Nat.div_add_mod n (2 * p)
  have e3 := Nat.mod_lt n hp2
  have e4 := Nat.mul_div_le n 2
  have e5 : 2 * p * (n / (2 * p)) + 2 * p * 3 ≤ 2 * p * N := by
    rw [← Nat.mul_add]
    exact Nat.mul_le_mul_left _ hN
  omega

theorem count_arith {K C V S : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) (hV : 0 ≤ V) (hS : 0 ≤ S) :
    K * (C * (V + S)) ≤ C * K * (V + 1) * (1 + S) := by
  have e : C * K * (V + 1) * (1 + S) - K * (C * (V + S)) = C * K * (V * S + 1) := by ring
  have h : 0 ≤ C * K * (V * S + 1) := by positivity
  linarith

/-- The number of index pairs `(j, i)` with `2pj + i ≤ 2pN`. -/
def parabolicCount (p N : ℕ) : ℕ := ∑ j ∈ Finset.range (N + 1), (2 * p * (N - j) + 1)

theorem sum_parabolic_const (p N : ℕ) (X : ℝ) :
    ∑ j ∈ Finset.range (N + 1), ∑ _i ∈ Finset.range (2 * p * (N - j) + 1), X =
      (parabolicCount p N : ℝ) * X := by
  unfold parabolicCount
  rw [Nat.cast_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-! ### Pointwise jets and their integrals -/

section Jets

variable {a : ℕ} {T : ℝ}

theorem jetSq_eq (V : ℝ → SmoothCcTensor g 0 a) (j i : ℕ) (t : ℝ) (x : M) :
    jetSq g T V j i t x = tensorInnerPointwise (I := I) (M := M) g 0 (a + i) x
      ((iteratedCovGrad g 0 a i (timeDerivIter T V j t)).toFun x)
      ((iteratedCovGrad g 0 a i (timeDerivIter T V j t)).toFun x) :=
  riemannianFiberNormSq_eq_tensorInnerPointwise g 0 (a + i) x _

theorem jetSq_nonneg (V : ℝ → SmoothCcTensor g 0 a) (j i : ℕ) (t : ℝ) (x : M) :
    0 ≤ jetSq g T V j i t x := by
  rw [jetSq_eq]
  exact tensorInnerPointwise_nonneg g 0 (a + i) x _

theorem integrable_jetSq (V : ℝ → SmoothCcTensor g 0 a) (j i : ℕ) (t : ℝ) :
    Integrable (fun x => jetSq g T V j i t x) (riemannianVolumeMeasure (I := I) (M := M) g) := by
  simp only [jetSq_eq]
  exact SmoothCcTensor.integrable_inner_cross _ _

/-- `∫_M |∂ₜ^j ∇^i V(t)|² = ‖∇^i ∂ₜ^j V(t)‖²_{L²}`. -/
theorem integral_jetSq (V : ℝ → SmoothCcTensor g 0 a) (j i : ℕ) (t : ℝ) :
    ∫ x, jetSq g T V j i t x ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      jetNorm g a i (timeDerivIter T V j t) ^ 2 := by
  simp only [jetSq_eq]
  exact tensorL2Inner_self_eq_sq_norm g (a + i) _

/-- `mixedInner` of a smooth family is the integral of `jetSq` over `[0,T] × M`. -/
theorem mixedInner_self_eq_integral_jetSq (hT : 0 < T) {V : ℝ → SmoothCcTensor g 0 a}
    (hV : JointlySmoothOn g 0 a (Icc 0 T) V) (j i : ℕ) :
    mixedInner g a T V V j i = ∫ t in (0 : ℝ)..T,
      ∫ x, jetSq g T V j i t x ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  rw [mixedInner_self_eq hT hV]
  simp only [integral_jetSq]

theorem parabolicInner_self_nonneg (p N : ℕ) (V : ℝ → SmoothCcTensor g 0 a) :
    0 ≤ parabolicInner g a p N T V V :=
  Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => mixedInner_self_nonneg _ j i

variable (g) in
/-- `Σ_{2pj+i ≤ 2pN} |∂ₜ^j ∇^i V(t, x)|²`, the integrand of `‖V‖²_{𝒫^N}`. -/
def parabolicJetSq (p N : ℕ) (T : ℝ) (V : ℝ → SmoothCcTensor g 0 a) (t : ℝ) (x : M) : ℝ :=
  ∑ j ∈ Finset.range (N + 1), ∑ i ∈ Finset.range (2 * p * (N - j) + 1), jetSq g T V j i t x

variable (g) in
/-- `Σ_{2pj+i ≤ 2pN} ‖∂ₜ^j ∇^i V(t)‖²_{L²}`, the spatial integral of `parabolicJetSq`. -/
def parabolicJetInt (p N : ℕ) (T : ℝ) (V : ℝ → SmoothCcTensor g 0 a) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (N + 1), ∑ i ∈ Finset.range (2 * p * (N - j) + 1),
    jetNorm g a i (timeDerivIter T V j t) ^ 2

theorem parabolicJetSq_nonneg (p N : ℕ) (V : ℝ → SmoothCcTensor g 0 a) (t : ℝ) (x : M) :
    0 ≤ parabolicJetSq g p N T V t x :=
  Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => jetSq_nonneg V j i t x

theorem jetSq_le_parabolicJetSq {p N j i : ℕ} (hj : j ≤ N) (hi : i ≤ 2 * p * (N - j))
    (V : ℝ → SmoothCcTensor g 0 a) (t : ℝ) (x : M) :
    jetSq g T V j i t x ≤ parabolicJetSq g p N T V t x := by
  unfold parabolicJetSq
  refine le_trans ?_ (Finset.single_le_sum
    (f := fun j => ∑ i ∈ Finset.range (2 * p * (N - j) + 1), jetSq g T V j i t x)
    (fun j _ => Finset.sum_nonneg fun i _ => jetSq_nonneg V j i t x)
    (Finset.mem_range.mpr (show j < N + 1 by omega)))
  exact Finset.single_le_sum (f := fun i => jetSq g T V j i t x)
    (fun i _ => jetSq_nonneg V j i t x) (Finset.mem_range.mpr (show i < 2 * p * (N - j) + 1 by omega))

/-- The jets of order at most `(j, i)` are bounded by `parabolicJetSq` when `2pj + i ≤ 2pN`. -/
theorem sum_jetSq_le_parabolicJetSq {p N j i : ℕ} (hj : j ≤ N) (hi : i ≤ 2 * p * (N - j))
    (V : ℝ → SmoothCcTensor g 0 a) (t : ℝ) (x : M) :
    ∑ j' ∈ Finset.range (j + 1), ∑ i' ∈ Finset.range (i + 1), jetSq g T V j' i' t x ≤
      parabolicJetSq g p N T V t x := by
  unfold parabolicJetSq
  refine (Finset.sum_le_sum fun j' hj' => ?_).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega : j + 1 ≤ N + 1))
      fun j' _ _ => Finset.sum_nonneg fun i' _ => jetSq_nonneg V j' i' t x)
  have hj'' := Finset.mem_range.mp hj'
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono ?_)
    fun i' _ _ => jetSq_nonneg V j' i' t x
  have : 2 * p * (N - j) ≤ 2 * p * (N - j') := Nat.mul_le_mul_left _ (by omega)
  omega

/-- The jets of weight at most `w ≤ 2pN` are bounded by `parabolicJetSq`, for `p ≥ 1`. -/
theorem sum_weight_jetSq_le_parabolicJetSq {p N w : ℕ} (hp : 1 ≤ p) (hw : w ≤ 2 * p * N)
    (V : ℝ → SmoothCcTensor g 0 a) (t : ℝ) (x : M) :
    ∑ j' ∈ Finset.range (N + 1), ∑ i' ∈ Finset.range (w + 1),
        (if 2 * p * j' + i' ≤ w then jetSq g T V j' i' t x else 0) ≤
      parabolicJetSq g p N T V t x := by
  unfold parabolicJetSq
  refine Finset.sum_le_sum fun j' hj' => ?_
  rw [← Finset.sum_filter]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun i' hi' => ?_)
    fun i' _ _ => jetSq_nonneg V j' i' t x
  rw [Finset.mem_filter, Finset.mem_range] at hi'
  have h := ((weight_le_iff (j := j') (i := i') (N := N) hp).mp (hi'.2.trans hw)).2
  rw [Finset.mem_range]
  omega

theorem integrable_parabolicJetSq (p N : ℕ) (V : ℝ → SmoothCcTensor g 0 a) (t : ℝ) :
    Integrable (fun x => parabolicJetSq g p N T V t x)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
  integrable_finset_sum _ fun j _ => integrable_finset_sum _ fun i _ => integrable_jetSq V j i t

theorem integral_parabolicJetSq (p N : ℕ) (V : ℝ → SmoothCcTensor g 0 a) (t : ℝ) :
    ∫ x, parabolicJetSq g p N T V t x ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      parabolicJetInt g p N T V t := by
  unfold parabolicJetSq parabolicJetInt
  rw [integral_finset_sum _ fun j _ => integrable_finset_sum _ fun i _ => integrable_jetSq V j i t]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finset_sum _ fun i _ => integrable_jetSq V j i t]
  exact Finset.sum_congr rfl fun i _ => integral_jetSq V j i t

theorem continuousOn_parabolicJetInt (hT : 0 < T) {V : ℝ → SmoothCcTensor g 0 a}
    (hV : JointlySmoothOn g 0 a (Icc 0 T) V) (p N : ℕ) :
    ContinuousOn (fun t => parabolicJetInt g p N T V t) (Icc 0 T) := by
  unfold parabolicJetInt
  exact continuousOn_finsetSum _ fun j _ => continuousOn_finsetSum _ fun i _ =>
    continuousOn_jetNorm_sq hT (jointlySmoothOn_timeDerivIter hT hV j) i

/-- `∫₀ᵀ Σ_{2pj+i ≤ 2pN} ‖∂ₜ^j ∇^i V‖²_{L²} = ‖V‖²_{𝒫^N}`. -/
theorem integral_parabolicJetInt (hT : 0 < T) {V : ℝ → SmoothCcTensor g 0 a}
    (hV : JointlySmoothOn g 0 a (Icc 0 T) V) (p N : ℕ) :
    ∫ t in (0 : ℝ)..T, parabolicJetInt g p N T V t = parabolicInner g a p N T V V := by
  unfold parabolicJetInt parabolicInner
  rw [intervalIntegral.integral_finsetSum fun j _ =>
    (continuousOn_finsetSum _ fun i _ => continuousOn_jetNorm_sq hT
      (jointlySmoothOn_timeDerivIter hT hV j) i).intervalIntegrable_of_Icc hT.le]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [intervalIntegral.integral_finsetSum fun i _ =>
    (continuousOn_jetNorm_sq hT (jointlySmoothOn_timeDerivIter hT hV j) i).intervalIntegrable_of_Icc
      hT.le]
  exact Finset.sum_congr rfl fun i _ => (mixedInner_self_eq hT hV j i).symm

end Jets

/-! ### Integral of a pointwise bound -/

section Integral

variable {T : ℝ} {p N : ℕ} {ι : Type*} [Fintype ι] {b : ι → ℕ}

theorem jetNorm_sq_le_of_jetSq_le {b' : ℕ} {φ : ℝ → SmoothCcTensor g 0 b'}
    {V : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c)} {C : ℝ} {j i : ℕ} {t : ℝ}
    (h : ∀ x, jetSq g T φ j i t x ≤ C * (1 + ∑ c, parabolicJetSq g p N T (V c) t x)) :
    jetNorm g b' i (timeDerivIter T φ j t) ^ 2 ≤
      C * ((riemannianVolumeMeasure (I := I) (M := M) g).real univ +
        ∑ c, parabolicJetInt g p N T (V c) t) := by
  have := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  rw [← integral_jetSq]
  have hS : Integrable (fun x => ∑ c, parabolicJetSq g p N T (V c) t x)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    integrable_finset_sum _ fun c _ => integrable_parabolicJetSq p N (V c) t
  have h1 : Integrable (fun x => (1 : ℝ) + ∑ c, parabolicJetSq g p N T (V c) t x)
      (riemannianVolumeMeasure (I := I) (M := M) g) := (integrable_const (1 : ℝ)).add hS
  have hR : Integrable (fun x => C * (1 + ∑ c, parabolicJetSq g p N T (V c) t x))
      (riemannianVolumeMeasure (I := I) (M := M) g) := h1.const_mul C
  refine (integral_mono (integrable_jetSq φ j i t) hR h).trans_eq ?_
  rw [integral_const_mul, integral_add (integrable_const (1 : ℝ)) hS, integral_const,
    integral_finset_sum _ fun c _ => integrable_parabolicJetSq p N (V c) t]
  simp only [integral_parabolicJetSq, smul_eq_mul, mul_one]

/-- One pairing of `φ` is bounded by `C (T vol(M) + Σ_c ‖V c‖²_{𝒫^N})`. -/
theorem mixedInner_le_of_jetSq_le (hT : 0 < T) {b' : ℕ} {φ : ℝ → SmoothCcTensor g 0 b'}
    (hφ : JointlySmoothOn g 0 b' (Icc 0 T) φ) {V : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c)}
    (hV : ∀ c, JointlySmoothOn g 0 (b c) (Icc 0 T) (V c)) {C : ℝ} {j i : ℕ}
    (h : ∀ t ∈ Icc 0 T, ∀ x, jetSq g T φ j i t x ≤ C * (1 + ∑ c, parabolicJetSq g p N T (V c) t x)) :
    mixedInner g b' T φ φ j i ≤
      C * (T * (riemannianVolumeMeasure (I := I) (M := M) g).real univ +
        ∑ c, parabolicInner g (b c) p N T (V c) (V c)) := by
  rw [mixedInner_self_eq hT hφ]
  set vol := (riemannianVolumeMeasure (I := I) (M := M) g).real univ with hvol
  have hsum : ContinuousOn (fun t => ∑ c, parabolicJetInt g p N T (V c) t) (Icc 0 T) :=
    continuousOn_finsetSum _ fun c _ => continuousOn_parabolicJetInt hT (hV c) p N
  have hcont : ContinuousOn (fun t => C * (vol + ∑ c, parabolicJetInt g p N T (V c) t))
      (Icc 0 T) :=
    continuousOn_const.mul (continuousOn_const.add hsum)
  refine (intervalIntegral.integral_mono_on hT.le
    ((continuousOn_jetNorm_sq hT (jointlySmoothOn_timeDerivIter hT hφ j) i).intervalIntegrable_of_Icc
      hT.le)
    (hcont.intervalIntegrable_of_Icc hT.le)
    fun t ht => jetNorm_sq_le_of_jetSq_le (h t ht)).trans_eq ?_
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add intervalIntegrable_const (hsum.intervalIntegrable_of_Icc hT.le),
    intervalIntegral.integral_const,
    intervalIntegral.integral_finsetSum fun c _ =>
      (continuousOn_parabolicJetInt hT (hV c) p N).intervalIntegrable_of_Icc hT.le]
  simp only [integral_parabolicJetInt hT (hV _), smul_eq_mul, sub_zero]

/-- **Integral of a pointwise bound.** If `|∂ₜ^j ∇^i φ|² ≤ C (1 + Σ_c Σ_{2pj'+i' ≤ 2pN}
|∂ₜ^{j'} ∇^{i'} V_c|²)` on `M × [0,T]` for all `2pj + i ≤ 2pN`, then
`‖φ‖²_{𝒫^N} ≤ C · #{(j,i)} · (T vol(M) + 1) · (1 + Σ_c ‖V_c‖²_{𝒫^N})`. -/
theorem parabolicInner_le_of_jetSq_le (hT : 0 < T) {b' : ℕ} {φ : ℝ → SmoothCcTensor g 0 b'}
    (hφ : JointlySmoothOn g 0 b' (Icc 0 T) φ) {V : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c)}
    (hV : ∀ c, JointlySmoothOn g 0 (b c) (Icc 0 T) (V c)) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ j i, j ≤ N → i ≤ 2 * p * (N - j) → ∀ t ∈ Icc 0 T, ∀ x,
      jetSq g T φ j i t x ≤ C * (1 + ∑ c, parabolicJetSq g p N T (V c) t x)) :
    parabolicInner g b' p N T φ φ ≤
      C * parabolicCount p N * (T * (riemannianVolumeMeasure (I := I) (M := M) g).real univ + 1) *
        (1 + ∑ c, parabolicInner g (b c) p N T (V c) (V c)) := by
  have hS : 0 ≤ ∑ c, parabolicInner g (b c) p N T (V c) (V c) :=
    Finset.sum_nonneg fun c _ => parabolicInner_self_nonneg p N (V c)
  have hv : 0 ≤ T * (riemannianVolumeMeasure (I := I) (M := M) g).real univ :=
    mul_nonneg hT.le measureReal_nonneg
  have h1 : parabolicInner g b' p N T φ φ ≤
      ∑ j ∈ Finset.range (N + 1), ∑ _i ∈ Finset.range (2 * p * (N - j) + 1),
        C * (T * (riemannianVolumeMeasure (I := I) (M := M) g).real univ +
          ∑ c, parabolicInner g (b c) p N T (V c) (V c)) :=
    Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun i hi =>
      mixedInner_le_of_jetSq_le hT hφ hV
        (h j i (by have := Finset.mem_range.mp hj; omega)
          (by have := Finset.mem_range.mp hi; omega))
  rw [sum_parabolic_const] at h1
  exact h1.trans (count_arith (Nat.cast_nonneg _) hC hv hS)

end Integral

/-! ### Low jets are bounded by the norm -/

/-- **Step 1 of `prop:nemytskii`.** For `N ≥ N₀ = ⌊n/2p⌋ + 3`, the jets of weight at most `pN` are
bounded pointwise by the `𝒫^N` norm: `|∂ₜ^j ∇^i V|² ≤ C ‖V‖²_{𝒫^N}` when `2(2pj + i) ≤ 2pN`. -/
theorem exists_jetSq_le_parabolicInner {T : ℝ} (hT : 0 < T) {p N : ℕ} (hp : 1 ≤ p)
    (hN : Module.finrank ℝ E / (2 * p) + 3 ≤ N) (a : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ V : ℝ → SmoothCcTensor g 0 a, JointlySmoothOn g 0 a (Icc 0 T) V →
      ∀ j i, 2 * (2 * p * j + i) ≤ 2 * p * N → ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
        jetSq g T V j i t x ≤ C * parabolicInner g a p N T V V := by
  have hex : ∀ j i : ℕ, ∃ C : ℝ, 0 ≤ C ∧ (2 * (2 * p * j + i) ≤ 2 * p * N →
      ∀ V : ℝ → SmoothCcTensor g 0 a, JointlySmoothOn g 0 a (Icc 0 T) V →
        ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
          jetSq g T V j i t x ≤ C * parabolicInner g a p N T V V) := by
    intro j i
    by_cases hw : 2 * (2 * p * j + i) ≤ 2 * p * N
    · obtain ⟨hj, hk⟩ := embedding_arith hp hN hw
      obtain ⟨C, hC0, hC⟩ := exists_fiberNormSq_le_parabolicInner (g := g) (s := a) hT p hj hk
      exact ⟨C, hC0, fun _ V hV t ht x => hC V hV t ht x⟩
    · exact ⟨0, le_rfl, fun h => absurd h hw⟩
  choose Cf hCf0 hCf using hex
  refine ⟨∑ j ∈ Finset.range (N + 1), ∑ i ∈ Finset.range (2 * p * N + 1), Cf j i,
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => hCf0 j i,
    fun V hV j i hw t ht x => ?_⟩
  have hP := parabolicInner_self_nonneg (T := T) p N V
  have hjN := (embedding_arith hp hN hw).1
  refine (hCf j i hw V hV t ht x).trans (mul_le_mul_of_nonneg_right ?_ hP)
  refine (Finset.single_le_sum (f := fun i => Cf j i) (fun i _ => hCf0 j i)
    (Finset.mem_range.mpr (show i < 2 * p * N + 1 by omega))).trans ?_
  exact Finset.single_le_sum (f := fun j => ∑ i ∈ Finset.range (2 * p * N + 1), Cf j i)
    (fun j _ => Finset.sum_nonneg fun i _ => hCf0 j i) (Finset.mem_range.mpr (show j < N + 1 by omega))

/-! ### Derivatives cost one level (`lem:parabolic-basic` (i)) -/

section Level

variable {s : ℕ} {T : ℝ}

theorem level_arith {p N j k : ℕ} (hj : j ≤ N) (hk : k ≤ 2 * p) :
    2 * p * (N - j) + k ≤ 2 * p * (N + 1 - j) := by
  have e : 2 * p * (N + 1 - j) = 2 * p * (N - j) + 2 * p := by
    rw [show N + 1 - j = (N - j) + 1 by omega, Nat.mul_succ]
  omega

/-- **`‖∇^k u‖_{𝒫^N} ≤ ‖u‖_{𝒫^{N+1}}` for `k ≤ 2p`.** -/
theorem parabolicInner_iteratedCovGrad_le (hT : 0 < T) {u : ℝ → SmoothCcTensor g 0 s}
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u) {p N k : ℕ} (hk : k ≤ 2 * p) :
    parabolicInner g (s + k) p N T (fun t => iteratedCovGrad g 0 s k (u t))
        (fun t => iteratedCovGrad g 0 s k (u t)) ≤ parabolicInner g s p (N + 1) T u u := by
  have hU := jointlySmoothOn_iteratedCovGrad hu k
  rw [parabolicInner_self_eq hT hU, parabolicInner_self_eq hT hu]
  calc ∑ j ∈ Finset.range (N + 1), ∫ t in (0 : ℝ)..T, sobolevNormSq g 0 (s + k) (2 * p * (N - j))
          (timeDerivIter T (fun t => iteratedCovGrad g 0 s k (u t)) j t)
      ≤ ∑ j ∈ Finset.range (N + 1), ∫ t in (0 : ℝ)..T,
          sobolevNormSq g 0 s (2 * p * (N + 1 - j)) (timeDerivIter T u j t) := by
        refine Finset.sum_le_sum fun j hj => intervalIntegral.integral_mono_on hT.le
          ((continuousOn_sobolevNormSq hT (jointlySmoothOn_timeDerivIter hT hU j) _).intervalIntegrable_of_Icc
            hT.le)
          ((continuousOn_sobolevNormSq hT (jointlySmoothOn_timeDerivIter hT hu j) _).intervalIntegrable_of_Icc
            hT.le) fun t ht => ?_
        rw [timeDerivIter_iteratedCovGrad hT hu k j ht]
        exact (sobolevNormSq_iteratedCovGrad_le _ _ k).trans
          (sobolevNormSq_mono s (level_arith (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hk) _)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
        fun j _ _ => intervalIntegral.integral_nonneg hT.le fun t _ => sobolevNormSq_nonneg s _ _

/-- **`‖∂ₜu‖_{𝒫^N} ≤ ‖u‖_{𝒫^{N+1}}`.** -/
theorem parabolicInner_timeDeriv_le (hT : 0 < T) {u : ℝ → SmoothCcTensor g 0 s}
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u) (p N : ℕ) :
    parabolicInner g s p N T (timeDeriv T u) (timeDeriv T u) ≤ parabolicInner g s p (N + 1) T u u := by
  have hU := jointlySmoothOn_timeDeriv hT hu
  rw [parabolicInner_self_eq hT hU, parabolicInner_self_eq hT hu, Finset.sum_range_succ' _ (N + 1)]
  have e : ∑ j ∈ Finset.range (N + 1), ∫ t in (0 : ℝ)..T,
        sobolevNormSq g 0 s (2 * p * (N - j)) (timeDerivIter T (timeDeriv T u) j t) =
      ∑ j ∈ Finset.range (N + 1), ∫ t in (0 : ℝ)..T,
        sobolevNormSq g 0 s (2 * p * (N + 1 - (j + 1))) (timeDerivIter T u (j + 1) t) :=
    Finset.sum_congr rfl fun j _ => by
      rw [timeDerivIter_succ', show N + 1 - (j + 1) = N - j by omega]
  rw [e]
  have h0 : 0 ≤ ∫ t in (0 : ℝ)..T, sobolevNormSq g 0 s (2 * p * (N + 1 - 0)) (timeDerivIter T u 0 t) :=
    intervalIntegral.integral_nonneg hT.le fun t _ => sobolevNormSq_nonneg s _ _
  linarith

end Level

end ShortTime
