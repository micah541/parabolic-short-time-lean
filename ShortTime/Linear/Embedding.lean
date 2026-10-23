import ShortTime.Linear.ParabolicOp
import ShortTime.Analysis.IccCalculus
import DifferentialGeometry.Analysis.Sobolev.Embedding.Tensor.SharpC0JetSum

/-!
# Sup bounds for parabolic norms (`lem:parabolic-basic` (v), `lem:embedding`)

* `sobolevNormSq_le_integral`: for a jointly smooth family,
  `‖v(t)‖²_{H^k} ≤ T⁻¹ ∫₀ᵀ ‖v‖²_{H^k} + ∫₀ᵀ (‖v‖²_{H^k} + ‖∂ₜv‖²_{H^k})` (a one-dimensional Sobolev
  inequality in time).
* `sobolevNormSq_timeDerivIter_le_parabolicInner`: `sup_t ‖∂ₜ^j v(t)‖²_{H^{2p(m-j-1)}} ≤ C ‖v‖²_{𝒫^m}`
  for `j < m`.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2
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

variable {g : SmoothRiemannianMetric I M} {s : ℕ} {T : ℝ}

theorem tensorL2Norm_sq_eq {a : ℕ} (S : SmoothCcTensor g 0 a) :
    tensorL2Norm (I := I) (M := M) g 0 a S.toFun ^ 2 =
      tensorL2Inner (I := I) (M := M) g 0 a S.toFun S.toFun := by
  rw [← SmoothCcTensor.norm_def, ← real_inner_self_eq_norm_sq, SmoothCcTensor.inner_def]

theorem two_mul_abs_tensorL2Inner_le {a : ℕ} (S S' : SmoothCcTensor g 0 a) :
    |2 * tensorL2Inner (I := I) (M := M) g 0 a S.toFun S'.toFun| ≤
      tensorL2Norm (I := I) (M := M) g 0 a S.toFun ^ 2 +
        tensorL2Norm (I := I) (M := M) g 0 a S'.toFun ^ 2 := by
  rw [← SmoothCcTensor.inner_def, ← SmoothCcTensor.norm_def, ← SmoothCcTensor.norm_def, abs_mul,
    abs_two]
  have h := abs_real_inner_le_norm S S'
  nlinarith [sq_nonneg (‖S‖ - ‖S'‖)]

/-- **A Sobolev inequality in time**: `‖v(t)‖²_{H^k} ≤ T⁻¹ ∫ ‖v‖²_{H^k} + ∫ (‖v‖²_{H^k} + ‖∂ₜv‖²_{H^k})`. -/
theorem sobolevNormSq_le_integral (hT : 0 < T) {v : ℝ → SmoothCcTensor g 0 s}
    (hv : JointlySmoothOn g 0 s (Icc 0 T) v) (k : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    sobolevNormSq g 0 s k (v t) ≤
      T⁻¹ * (∫ τ in (0 : ℝ)..T, sobolevNormSq g 0 s k (v τ)) +
        ∫ τ in (0 : ℝ)..T, (sobolevNormSq g 0 s k (v τ) + sobolevNormSq g 0 s k (timeDeriv T v τ)) := by
  set U : (i : ℕ) → ℝ → SmoothCcTensor g 0 (s + i) := fun i τ => iteratedCovGrad g 0 s i (v τ) with hU
  have hUs : ∀ i, JointlySmoothOn g 0 (s + i) (Icc 0 T) (U i) := fun i =>
    jointlySmoothOn_iteratedCovGrad hv i
  set d : ℝ → ℝ := fun τ => ∑ i ∈ Finset.range (k + 1),
    2 * tensorL2Inner (I := I) (M := M) g 0 (s + i) (U i τ).toFun (timeDeriv T (U i) τ).toFun with hd
  have hφ := continuousOn_sobolevNormSq hT hv k
  have hψ := continuousOn_sobolevNormSq hT (jointlySmoothOn_timeDeriv hT hv) k
  have hdc : ContinuousOn d (Icc 0 T) :=
    continuousOn_finsetSum _ fun i _ => continuousOn_const.mul
      (continuousOn_l2Pairing hT (hUs i) (jointlySmoothOn_timeDeriv hT (hUs i)))
  have hder : ∀ τ ∈ Ioo 0 T, HasDerivAt (fun τ => sobolevNormSq g 0 s k (v τ)) (d τ) τ := by
    intro τ hτ
    have h : ∀ i ∈ Finset.range (k + 1), HasDerivAt
        (fun τ => tensorL2Inner (I := I) (M := M) g 0 (s + i) (U i τ).toFun (U i τ).toFun)
        (2 * tensorL2Inner (I := I) (M := M) g 0 (s + i) (U i τ).toFun (timeDeriv T (U i) τ).toFun) τ :=
      fun i _ => hasDerivAt_normSq g (hUs i) (jointlySmoothOn_timeDeriv hT (hUs i))
        (fun t ht x => hasDerivWithinAt_timeDeriv hT (hUs i) ht x) hτ
    have h2 := HasDerivAt.fun_sum h
    refine h2.congr_of_eventuallyEq (Eventually.of_forall fun τ => ?_)
    simp only [sobolevNormSq, tensorL2Norm_sq_eq, hU]
  have hdb : ∀ τ ∈ Icc 0 T, |d τ| ≤
      sobolevNormSq g 0 s k (v τ) + sobolevNormSq g 0 s k (timeDeriv T v τ) := by
    intro τ hτ
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    simp only [sobolevNormSq, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have e : timeDeriv T (U i) τ = iteratedCovGrad g 0 s i (timeDeriv T v τ) :=
      timeDeriv_iteratedCovGrad hT hv i hτ
    rw [e]
    exact two_mul_abs_tensorL2Inner_le _ _
  refine le_average_add hT hφ (fun a ha b hb => ?_) ht
  have hB := abs_sub_le_integral_of_deriv hφ hdc (hφ.add hψ) hder hdb ha hb
  have h1 := le_abs_self (sobolevNormSq g 0 s k (v b) - sobolevNormSq g 0 s k (v a))
  simp only [Pi.add_apply] at hB
  linarith

/-- One term of `‖v‖²_{𝒫^m}`. -/
theorem integral_term_le_parabolicInner (hT : 0 < T) {v : ℝ → SmoothCcTensor g 0 s}
    (hv : JointlySmoothOn g 0 s (Icc 0 T) v) (p m : ℕ) {j : ℕ} (hj : j ≤ m) :
    ∫ τ in (0 : ℝ)..T, sobolevNormSq g 0 s (2 * p * (m - j)) (timeDerivIter T v j τ) ≤
      parabolicInner g s p m T v v := by
  rw [parabolicInner_self_eq hT hv]
  exact Finset.single_le_sum (f := fun j => ∫ τ in (0 : ℝ)..T,
      sobolevNormSq g 0 s (2 * p * (m - j)) (timeDerivIter T v j τ))
    (fun j _ => intervalIntegral.integral_nonneg hT.le fun t _ => sobolevNormSq_nonneg s _ _)
    (Finset.mem_range.mpr (by omega))

theorem integral_sobolevNormSq_mono (hT : 0 < T) {w : ℝ → SmoothCcTensor g 0 s}
    (hw : JointlySmoothOn g 0 s (Icc 0 T) w) {k l : ℕ} (hkl : k ≤ l) :
    ∫ τ in (0 : ℝ)..T, sobolevNormSq g 0 s k (w τ) ≤ ∫ τ in (0 : ℝ)..T, sobolevNormSq g 0 s l (w τ) :=
  intervalIntegral.integral_mono_on hT.le
    ((continuousOn_sobolevNormSq hT hw k).intervalIntegrable_of_Icc hT.le)
    ((continuousOn_sobolevNormSq hT hw l).intervalIntegrable_of_Icc hT.le)
    fun _ _ => sobolevNormSq_mono s hkl _

/-- **`sup_t ‖∂ₜ^j v(t)‖²_{H^k} ≤ C ‖v‖²_{𝒫^m}`** for `j < m` and `k ≤ 2p(m - j - 1)`
(`lem:parabolic-basic` (v)). -/
theorem sobolevNormSq_timeDerivIter_le_parabolicInner (hT : 0 < T) {v : ℝ → SmoothCcTensor g 0 s}
    (hv : JointlySmoothOn g 0 s (Icc 0 T) v) {p m j k : ℕ} (hj : j < m) (hk : k ≤ 2 * p * (m - j - 1))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    sobolevNormSq g 0 s k (timeDerivIter T v j t) ≤ (T⁻¹ + 2) * parabolicInner g s p m T v v := by
  have hw := jointlySmoothOn_timeDerivIter hT hv j
  have hw' := jointlySmoothOn_timeDerivIter hT hv (j + 1)
  have h0 : sobolevNormSq g 0 s k (timeDerivIter T v j t) ≤ T⁻¹ * (∫ τ in (0 : ℝ)..T,
      sobolevNormSq g 0 s k (timeDerivIter T v j τ)) + ∫ τ in (0 : ℝ)..T,
      (sobolevNormSq g 0 s k (timeDerivIter T v j τ) +
        sobolevNormSq g 0 s k (timeDerivIter T v (j + 1) τ)) :=
    sobolevNormSq_le_integral hT hw k ht
  have h1 := (integral_sobolevNormSq_mono hT hw (show k ≤ 2 * p * (m - j) by
    have : 2 * p * (m - j - 1) ≤ 2 * p * (m - j) := Nat.mul_le_mul_left _ (by omega)
    omega)).trans (integral_term_le_parabolicInner hT hv p m hj.le)
  have h2 := (integral_sobolevNormSq_mono hT hw' (show k ≤ 2 * p * (m - (j + 1)) by
    rw [show m - (j + 1) = m - j - 1 by omega]; exact hk)).trans
    (integral_term_le_parabolicInner hT hv p m (show j + 1 ≤ m by omega))
  rw [intervalIntegral.integral_add ((continuousOn_sobolevNormSq hT hw k).intervalIntegrable_of_Icc hT.le)
    ((continuousOn_sobolevNormSq hT hw' k).intervalIntegrable_of_Icc hT.le)] at h0
  have hP : 0 ≤ parabolicInner g s p m T v v := by
    rw [parabolicInner_self_eq hT hv]
    exact Finset.sum_nonneg fun j _ =>
      intervalIntegral.integral_nonneg hT.le fun t _ => sobolevNormSq_nonneg s _ _
  have hTi : 0 ≤ T⁻¹ := inv_nonneg.mpr hT.le
  nlinarith [mul_le_mul_of_nonneg_left h1 hTi]

/-- **Sup bound** (`lem:embedding`): if `j < m` and `n/2 + 1 + i ≤ 2p(m - j - 1)`, then
`|∂ₜ^j ∇^i v|² ≤ C ‖v‖²_{𝒫^m}` on `M × [0,T]`. -/
theorem exists_fiberNormSq_le_parabolicInner (hT : 0 < T) (p : ℕ) {m j i : ℕ} (hj : j < m)
    (hk : Module.finrank ℝ E / 2 + 1 + i ≤ 2 * p * (m - j - 1)) :
    ∃ C, 0 ≤ C ∧ ∀ v : ℝ → SmoothCcTensor g 0 s, JointlySmoothOn g 0 s (Icc 0 T) v →
      ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g 0 (s + i) x
          ((iteratedCovGrad g 0 s i (timeDerivIter T v j t)).toSection x) ≤
          C * parabolicInner g s p m T v v := by
  obtain ⟨C₀, hC₀, hC⟩ := exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical
    (I := I) (M := M) g 0 (s + i)
  refine ⟨C₀ ^ 2 * (T⁻¹ + 2), by positivity, fun v hv t ht x => ?_⟩
  set N := Module.finrank ℝ E / 2 + 1 with hN
  set w := timeDerivIter T v j t
  have h1 := hC (iteratedCovGrad g 0 s i w) x
  have h2 : ∑ l ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
      ‖iteratedCovGrad g 0 (s + i) l (iteratedCovGrad g 0 s i w)‖ ^ 2 =
        sobolevNormSq g 0 (s + i) N (iteratedCovGrad g 0 s i w) := by
    rw [sobolevNormSq_eq_sum, show Module.finrank ℝ E / 2 + 2 = N + 1 by omega]
    exact Finset.sum_congr rfl fun l _ => by rw [SmoothCcTensor.norm_def]
  have h3 := (sobolevNormSq_iteratedCovGrad_le N w i).trans (sobolevNormSq_mono s hk w)
  have h4 := sobolevNormSq_timeDerivIter_le_parabolicInner (p := p) hT hv hj (le_refl _) ht
  rw [h2] at h1
  calc _ ≤ C₀ ^ 2 * sobolevNormSq g 0 (s + i) N (iteratedCovGrad g 0 s i w) := h1
    _ ≤ C₀ ^ 2 * ((T⁻¹ + 2) * parabolicInner g s p m T v v) :=
        mul_le_mul_of_nonneg_left (h3.trans h4) (sq_nonneg _)
    _ = _ := by ring

end ShortTime
