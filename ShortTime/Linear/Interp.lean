import ShortTime.Linear.Bounds
import ShortTime.Linear.Divergence
import DifferentialGeometry.Analysis.Sobolev.GagliardoNirenberg.FiberNorm.DiscreteLogConvexity

/-!
# Interpolation between covariant derivatives (`lem:interp`)

For `0 < j < k` and `ε > 0` there is `C` with `‖∇^j u‖ ≤ ε ‖∇^k u‖ + C ‖u‖` for every smooth
covariant tensor field `u`.

Proof (as in the paper): with `a_i = ‖∇^i u‖`, one integration by parts and the pointwise bound on
the metric trace give `a_{i+1}² ≤ M a_i a_{i+2}`. The sequence is therefore log-convex up to a
constant, and the library's `discrete_log_convex_power_interpolation` gives
`a_j^k ≤ M' a_0^{k-j} a_k^j`; Young's inequality finishes.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set MeasureTheory
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Spectral DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Spectral.DeTurck DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open scoped Manifold ContDiff BigOperators

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

variable (g : SmoothRiemannianMetric I M)

/-- `‖∇^i u‖`, the `L²` norm of the `i`-th covariant derivative. -/
abbrev jetNorm (s i : ℕ) (u : SmoothCcTensor g 0 s) : ℝ :=
  tensorL2Norm (I := I) (M := M) g 0 (s + i) (iteratedCovGrad g 0 s i u).toFun

theorem jetNorm_nonneg (s i : ℕ) (u : SmoothCcTensor g 0 s) : 0 ≤ jetNorm g s i u :=
  tensorL2Norm_nonneg (I := I) (M := M) g 0 (s + i) _

theorem tensorL2Inner_self_eq_sq_norm (t : ℕ) (S : SmoothCcTensor g 0 t) :
    tensorL2Inner (I := I) (M := M) g 0 t S.toFun S.toFun =
      tensorL2Norm (I := I) (M := M) g 0 t S.toFun ^ 2 :=
  (Real.sq_sqrt (tensorL2Inner_nonneg (I := I) (M := M) g 0 t _)).symm

/-- The metric trace has bounded fibre norm. -/
theorem exists_bound_cometricDoubleTraceField (t : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g (t + 2) t x
      ((cometricDoubleTraceField (I := I) g t).toSection x) ≤ K :=
  exists_bound_riemannianFiberNormSq_smoothCcTensor g (t + 2) t _

/-- **Log-convexity step.** `‖∇^{i+1} u‖² ≤ √K ‖∇^i u‖ ‖∇^{i+2} u‖`, with `K` a bound for the
trace on `T⁰_{s+i+2}`. -/
theorem jetNorm_succ_sq_le (s i : ℕ) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g (s + i + 2) (s + i) x
      ((cometricDoubleTraceField (I := I) g (s + i)).toSection x) ≤ K)
    (u : SmoothCcTensor g 0 s) :
    jetNorm g s (i + 1) u ^ 2 ≤ Real.sqrt K * jetNorm g s i u * jetNorm g s (i + 2) u := by
  set W := iteratedCovGrad g 0 s i u
  have h1 : jetNorm g s (i + 1) u ^ 2 =
      - tensorL2Inner (I := I) (M := M) g 0 (s + i) W.toFun
        (operatorFieldApply (I := I) (M := M) g (s + i + 2) (s + i)
          (cometricDoubleTraceField (I := I) g (s + i))
          (covGrad (I := I) (M := M) g 0 (s + i + 1) (covGrad (I := I) (M := M) g 0 (s + i) W))).toFun := by
    rw [← covDivergence_eq_trace_covGrad, ← tensorL2Inner_covGrad_eq_neg_tensorL2Inner_covDivergence,
      ← tensorL2Inner_self_eq_sq_norm]
    rfl
  have h2 := abs_inner_operatorFieldApply_le g (s + i + 2) (s + i)
    (cometricDoubleTraceField (I := I) g (s + i)) hK0 hK W
    (covGrad (I := I) (M := M) g 0 (s + i + 1) (covGrad (I := I) (M := M) g 0 (s + i) W))
  rw [h1]
  exact (neg_le_abs _).trans h2

/-- **Interpolation.** For `0 < j < k` and `ε > 0` there is `C` with
`‖∇^j u‖ ≤ ε ‖∇^k u‖ + C ‖u‖`. -/
theorem jetNorm_le_interp (s j k : ℕ) (hj : 0 < j) (hjk : j < k) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : SmoothCcTensor g 0 s,
      jetNorm g s j u ≤ ε * jetNorm g s k u + C * jetNorm g s 0 u := by
  classical
  -- a uniform log-convexity constant for the first `k` steps
  choose K hK0 hK using fun i : ℕ => exists_bound_cometricDoubleTraceField g (s + i)
  set Mc : ℝ := 1 + ∑ i ∈ Finset.range k, Real.sqrt (K i) with hMc
  have hMc1 : 1 ≤ Mc := by
    have : 0 ≤ ∑ i ∈ Finset.range k, Real.sqrt (K i) :=
      Finset.sum_nonneg fun i _ => Real.sqrt_nonneg _
    linarith
  have hsqrt_le : ∀ i ∈ Finset.range k, Real.sqrt (K i) ≤ Mc := by
    intro i hi
    have := Finset.single_le_sum (f := fun i => Real.sqrt (K i))
      (fun i _ => Real.sqrt_nonneg _) hi
    linarith
  set Kp : ℝ := Mc ^ (k ^ 3) with hKp
  have hKp1 : 1 ≤ Kp := one_le_pow₀ hMc1
  -- choose the constant
  set D : ℝ := max 1 (Kp / ε ^ j) with hD
  have hD1 : 1 ≤ D := le_max_left _ _
  refine ⟨D, by linarith, fun u => ?_⟩
  set a : ℕ → ℝ := fun i => jetNorm g s i u with ha
  have ha0 : ∀ i, 0 ≤ a i := fun i => jetNorm_nonneg g s i u
  have hlc : ∀ i, i + 1 < k → a (i + 1) ^ 2 ≤ Mc * a i * a (i + 2) := by
    intro i hi
    have h := jetNorm_succ_sq_le g s i (hK0 i) (hK i) u
    have hm : Real.sqrt (K i) ≤ Mc := hsqrt_le i (Finset.mem_range.mpr (by omega))
    calc a (i + 1) ^ 2 ≤ Real.sqrt (K i) * a i * a (i + 2) := h
      _ ≤ Mc * a i * a (i + 2) := by
        have := mul_nonneg (ha0 i) (ha0 (i + 2))
        nlinarith
  have hpow := DifferentialGeometry.Analysis.Sobolev.Tensor.discrete_log_convex_power_interpolation a ha0 Mc hMc1 j k hlc hj hjk
  -- Young: if `a j` were larger than both `ε a k` and `D a 0`, `hpow` would fail.
  by_contra hcon
  push Not at hcon
  have h1 : ε * a k < a j := by
    have := add_nonneg (mul_nonneg hε.le (ha0 k)) (mul_nonneg (by linarith : (0 : ℝ) ≤ D) (ha0 0))
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ D) (ha0 0)]
  have h2 : D * a 0 < a j := by
    nlinarith [mul_nonneg hε.le (ha0 k)]
  have hajpos : 0 < a j := lt_of_le_of_lt (mul_nonneg (by linarith) (ha0 0)) h2
  have hkj : 0 < k - j := Nat.sub_pos_of_lt hjk
  have hsplit : a j ^ k = a j ^ j * a j ^ (k - j) := by
    rw [← pow_add, Nat.add_sub_cancel' hjk.le]
  have hA : (ε * a k) ^ j ≤ a j ^ j := pow_le_pow_left₀ (mul_nonneg hε.le (ha0 k)) h1.le j
  have hB : (D * a 0) ^ (k - j) < a j ^ (k - j) :=
    pow_lt_pow_left₀ h2 (mul_nonneg (by linarith) (ha0 0)) hkj.ne'
  have hDpow : Kp / ε ^ j ≤ D ^ (k - j) := by
    calc Kp / ε ^ j ≤ D := le_max_right _ _
      _ = D ^ 1 := (pow_one D).symm
      _ ≤ D ^ (k - j) := pow_le_pow_right₀ hD1 hkj
  have hεj : 0 < ε ^ j := pow_pos hε j
  -- `Kp a0^{k-j} ak^j ≤ (ε ak)^j (D a0)^{k-j}`
  have hcmp : Kp * a 0 ^ (k - j) * a k ^ j ≤ (ε * a k) ^ j * (D * a 0) ^ (k - j) := by
    rw [mul_pow, mul_pow]
    have hK' : Kp ≤ ε ^ j * D ^ (k - j) := by
      rw [div_le_iff₀ hεj] at hDpow
      linarith [mul_comm (ε ^ j) (D ^ (k - j))]
    have hnn : 0 ≤ a 0 ^ (k - j) * a k ^ j := mul_nonneg (pow_nonneg (ha0 0) _) (pow_nonneg (ha0 k) _)
    nlinarith [mul_le_mul_of_nonneg_right hK' hnn]
  have hlt : (ε * a k) ^ j * (D * a 0) ^ (k - j) < a j ^ k := by
    rw [hsplit]
    calc (ε * a k) ^ j * (D * a 0) ^ (k - j) ≤ a j ^ j * (D * a 0) ^ (k - j) :=
          mul_le_mul_of_nonneg_right hA (pow_nonneg (mul_nonneg (by linarith) (ha0 0)) _)
      _ < a j ^ j * a j ^ (k - j) := mul_lt_mul_of_pos_left hB (pow_pos hajpos j)
  linarith

end ShortTime
