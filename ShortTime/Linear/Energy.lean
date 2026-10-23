import ShortTime.Linear.GardingOne
import DifferentialGeometry.Analysis.Integration.L2.Hilbert.DenseSubset
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The basic energy identity and uniqueness for second-order operators

For a family `u` that is jointly smooth on `M × [0, T]` with `∂ₜu = v`,

  `d/dt ‖u(t)‖² = 2 ⟨u(t), v(t)⟩`   for `0 < t < T`,

and `t ↦ ‖u(t)‖²` is continuous on `[0, T]`. Combined with Gårding's inequality this gives
`d/dt ‖u‖² ≤ 2C ‖u‖²` for solutions of `∂ₜu = L u`, hence uniqueness (`thm:linear` (ii), `p = 1`).
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set MeasureTheory Filter Metric
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Spectral DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Elliptic
open scoped Manifold ContDiff BigOperators Topology

namespace ShortTime

/-! ### A Gronwall-type lemma -/

/-- If `e ≥ 0` is continuous on `[0, T]`, `e 0 = 0` and `e' ≤ C e` in `(0, T)`, then `e = 0` on
`[0, T]`. -/
theorem eq_zero_of_hasDerivAt_le {e e' : ℝ → ℝ} {T C : ℝ}
    (hcont : ContinuousOn e (Icc 0 T)) (hnn : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ e t) (h0 : e 0 = 0)
    (hd : ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt e (e' t) t)
    (hle : ∀ t ∈ Ioo (0 : ℝ) T, e' t ≤ C * e t) :
    ∀ t ∈ Icc (0 : ℝ) T, e t = 0 := by
  set φ : ℝ → ℝ := fun t => e t * Real.exp (-(C * t)) with hφ
  have hφd : ∀ t ∈ Ioo (0 : ℝ) T,
      HasDerivAt φ (e' t * Real.exp (-(C * t)) + e t * (Real.exp (-(C * t)) * (-C))) t := by
    intro t ht
    have hexp : HasDerivAt (fun t => Real.exp (-(C * t))) (Real.exp (-(C * t)) * (-C)) t := by
      have := ((hasDerivAt_id t).const_mul C).neg.exp
      simpa using this
    exact (hd t ht).mul hexp
  have hanti : AntitoneOn φ (Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T)
    · exact hcont.mul ((Real.continuous_exp.comp (continuous_const.mul continuous_id).neg)
        |>.continuousOn)
    · intro t ht
      rw [interior_Icc] at ht
      exact (hφd t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hφd t ht).deriv]
      have hpos := Real.exp_pos (-(C * t))
      nlinarith [hle t ht]
  intro t ht
  by_cases hT : (0 : ℝ) ≤ T
  · have h := hanti ⟨le_rfl, hT⟩ ht ht.1
    have hφ0 : φ 0 = 0 := by simp [hφ, h0]
    rw [hφ0] at h
    have hpos := Real.exp_pos (-(C * t))
    have hle0 : e t ≤ 0 := by
      by_contra hne
      push Not at hne
      have : 0 < e t * Real.exp (-(C * t)) := mul_pos hne hpos
      simp only [hφ] at h
      linarith
    exact le_antisymm hle0 (hnn t ht)
  · exact absurd (ht.1.trans ht.2) hT

/-! ### The energy identity -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

variable (g : SmoothRiemannianMetric I M)

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- The pointwise inner product at `x`, as a continuous bilinear form on the model fibre. -/
def ptInnerBilin (r s : ℕ) (x : M) :
    TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun S => LinearMap.toContinuousLinearMap
        { toFun := fun T => tensorInnerPointwise (I := I) (M := M) g r s x S T
          map_add' := tensorInnerPointwise_add_right (I := I) (M := M) g r s x S
          map_smul' := fun c T => tensorInnerPointwise_smul_right (I := I) (M := M) g r s x c S T }
      map_add' := fun S₁ S₂ => by
        ext T
        exact tensorInnerPointwise_add_left (I := I) (M := M) g r s x S₁ S₂ T
      map_smul' := fun c S => by
        ext T
        exact tensorInnerPointwise_smul_left (I := I) (M := M) g r s x c S T }

theorem ptInnerBilin_apply (r s : ℕ) (x : M) (S T : TensorRSModel r s ℝ E) :
    ptInnerBilin g r s x S T = tensorInnerPointwise (I := I) (M := M) g r s x S T := rfl

theorem abs_tensorInnerPointwise_cc_le {r s : ℕ} (S T : SmoothCcTensor g r s) (x : M) {A B : ℝ}
    (hA : riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x) ≤ A)
    (hB : riemannianFiberNormSq (I := I) (M := M) g r s x (T.toSection x) ≤ B) :
    |tensorInnerPointwise (I := I) (M := M) g r s x (S.toFun x) (T.toFun x)| ≤
      Real.sqrt A * Real.sqrt B := by
  refine (abs_tensorInnerPointwise_le_mul (I := I) (M := M) g r s x _ _).trans ?_
  unfold tensorPointwiseNorm
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise] at hA hB
  exact mul_le_mul (Real.sqrt_le_sqrt hA) (Real.sqrt_le_sqrt hB) (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _)

variable [CompleteSpace E]

/-- **Energy identity.** If `∂ₜ u = v` on `[0, T]` (both jointly smooth), then
`d/dt ‖u(t)‖² = 2 ⟨u(t), v(t)⟩` for `0 < t < T`. -/
theorem hasDerivAt_normSq {s : ℕ} {T : ℝ} {u v : ℝ → SmoothCcTensor g 0 s}
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u) (hv : JointlySmoothOn g 0 s (Icc 0 T) v)
    (hd : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      HasDerivWithinAt (fun τ => (u τ).toFun x) ((v t).toFun x) (Icc 0 T) t)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt (fun τ => tensorL2Inner (I := I) (M := M) g 0 s (u τ).toFun (u τ).toFun)
      (2 * tensorL2Inner (I := I) (M := M) g 0 s (u t).toFun (v t).toFun) t := by
  have := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  obtain ⟨Bu, -, hBu⟩ := exists_bound_of_jointlySmoothOn hu
  obtain ⟨Bv, -, hBv⟩ := exists_bound_of_jointlySmoothOn hv
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_Ioo t ht
  have hderiv : ∀ x : M, ∀ τ ∈ Metric.ball t ε,
      HasDerivAt (fun τ => tensorInnerPointwise (I := I) (M := M) g 0 s x
          ((u τ).toFun x) ((u τ).toFun x))
        (2 * tensorInnerPointwise (I := I) (M := M) g 0 s x ((u τ).toFun x) ((v τ).toFun x)) τ := by
    intro x τ hτ
    have hτ' := hball hτ
    have hU : HasDerivAt (fun τ => (u τ).toFun x) ((v τ).toFun x) τ :=
      (hd τ (Ioo_subset_Icc_self hτ') x).hasDerivAt (Icc_mem_nhds hτ'.1 hτ'.2)
    have h := (ptInnerBilin g 0 s x).hasDerivAt_of_bilinear (fun _ => hU) (fun _ => hU)
    simp only [ptInnerBilin_apply] at h
    refine h.congr_deriv ?_
    rw [tensorInnerPointwise_symm (I := I) (M := M) g 0 s x ((v τ).toFun x)]
    ring
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := riemannianVolumeMeasure (I := I) (M := M) g)
    (F := fun τ x => tensorInnerPointwise (I := I) (M := M) g 0 s x
      ((u τ).toFun x) ((u τ).toFun x))
    (F' := fun τ x => 2 * tensorInnerPointwise (I := I) (M := M) g 0 s x
      ((u τ).toFun x) ((v τ).toFun x))
    (bound := fun _ => 2 * (Real.sqrt Bu * Real.sqrt Bv)) (Metric.ball_mem_nhds t hε)
    (Eventually.of_forall fun τ => SmoothCcTensor.aestronglyMeasurable_inner_self (u τ))
    (SmoothCcTensor.integrable_inner_cross (u t) (u t))
    ((SmoothCcTensor.aestronglyMeasurable_inner_cross (u t) (v t)).const_mul 2)
    (ae_of_all _ fun x τ hτ => by
      have hτ' := Ioo_subset_Icc_self (hball hτ)
      rw [Real.norm_eq_abs, abs_mul, abs_two]
      exact mul_le_mul_of_nonneg_left
        (abs_tensorInnerPointwise_cc_le g (u τ) (v τ) x (hBu τ hτ' x) (hBv τ hτ' x)) two_pos.le)
    (integrable_const _)
    (ae_of_all _ hderiv)
  have h2 := key.2
  unfold tensorL2Inner
  rw [← integral_const_mul]
  exact h2

/-- `t ↦ ‖u(t)‖²` is continuous on `[0, T]` if `u` has time derivatives there. -/
theorem continuousOn_normSq {s : ℕ} {T : ℝ} {u v : ℝ → SmoothCcTensor g 0 s}
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u)
    (hd : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      HasDerivWithinAt (fun τ => (u τ).toFun x) ((v t).toFun x) (Icc 0 T) t) :
    ContinuousOn (fun τ => tensorL2Inner (I := I) (M := M) g 0 s (u τ).toFun (u τ).toFun)
      (Icc 0 T) := by
  have := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  obtain ⟨Bu, -, hBu⟩ := exists_bound_of_jointlySmoothOn hu
  unfold tensorL2Inner
  refine continuousOn_of_dominated (bound := fun _ => Real.sqrt Bu * Real.sqrt Bu)
    (fun τ _ => SmoothCcTensor.aestronglyMeasurable_inner_self (u τ))
    (fun τ hτ => ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]
      exact abs_tensorInnerPointwise_cc_le g (u τ) (u τ) x (hBu τ hτ x) (hBu τ hτ x))
    (integrable_const _) (ae_of_all _ fun x => ?_)
  have hU : ContinuousOn (fun τ => (u τ).toFun x) (Icc 0 T) :=
    fun τ hτ => (hd τ hτ x).continuousWithinAt
  have hc : ContinuousOn (fun τ => ptInnerBilin g 0 s x ((u τ).toFun x) ((u τ).toFun x))
      (Icc 0 T) :=
    ((ptInnerBilin g 0 s x).continuous.comp_continuousOn hU).clm_apply hU
  simp only [ptInnerBilin_apply] at hc
  exact hc

end ShortTime
