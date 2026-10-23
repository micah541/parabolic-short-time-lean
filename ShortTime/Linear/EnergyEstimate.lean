import ShortTime.Linear.SobolevBasic
import ShortTime.Linear.Parabolic
import ShortTime.Analysis.EnergyODE

/-!
# Energy estimates

Paper: Proposition `prop:energy`.

The base case `k = 0` (`LinearOp.energy_estimate_zero`): if `∂ₜu = Lu + f` with `u(0) = 0` and `L`
parabolic, then
`sup_t ‖u(t)‖² + ∫₀ᵀ ‖u‖²_{H^p} ≤ C ∫₀ᵀ ‖f‖²_{H^{-p}}`.
From `d/dt ‖u‖² = 2⟨u, Lu⟩ + 2⟨u, f⟩`, Gårding's inequality and duality give
`d/dt ‖u‖² + (λ/4)‖u‖²_{H^p} ≤ 2C ‖u‖² + (4/λ)‖f‖²_{H^{-p}}`, and Grönwall's inequality
(`energy_ode`) concludes.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open scoped Manifold ContDiff

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

/-! ### Negative norms along a smooth family -/

theorem jetNorm_zero_eq_norm {s : ℕ} (u : SmoothCcTensor g 0 s) : jetNorm g s 0 u = ‖u‖ :=
  ccNorm_eq_norm u

theorem negSobolevNorm_le_jetNorm (s k : ℕ) (f : SmoothCcTensor g 0 s) :
    negSobolevNorm g 0 s k f ≤ jetNorm g s 0 f := by
  refine csSup_le ⟨_, zero_mem_negSobolevNorm_set s k f⟩ ?_
  rintro _ ⟨φ, hφ, rfl⟩
  have hcs := abs_inner_le_norm_mul_norm g 0 s f φ
  have h1 : jetNorm g s 0 φ ≤ 1 := (jetNorm_zero_le_sobolevNorm s k φ).trans hφ
  have hf := jetNorm_nonneg g s 0 f
  calc tensorL2Inner (I := I) (M := M) g 0 s f.toFun φ.toFun
      ≤ jetNorm g s 0 f * jetNorm g s 0 φ := (le_abs_self _).trans hcs
    _ ≤ jetNorm g s 0 f * 1 := mul_le_mul_of_nonneg_left h1 hf
    _ = jetNorm g s 0 f := mul_one _

theorem negSobolevNorm_add_le (s k : ℕ) (a b : SmoothCcTensor g 0 s) :
    negSobolevNorm g 0 s k (a + b) ≤ negSobolevNorm g 0 s k a + negSobolevNorm g 0 s k b := by
  refine csSup_le ⟨_, zero_mem_negSobolevNorm_set s k (a + b)⟩ ?_
  rintro _ ⟨φ, hφ, rfl⟩
  change tensorL2Inner (I := I) (M := M) g 0 s (a + b).toFun φ.toFun ≤ _
  rw [SmoothCcTensor.toFun_add, tensorL2Inner_add_left _ _ _ _ _ _
    (SmoothCcTensor.integrable_inner_cross a φ) (SmoothCcTensor.integrable_inner_cross b φ)]
  have ha := inner_le_negSobolevNorm s k a φ
  have hb := inner_le_negSobolevNorm s k b φ
  have ha0 := negSobolevNorm_nonneg s k a
  have hb0 := negSobolevNorm_nonneg s k b
  have h1 : negSobolevNorm g 0 s k a * sobolevNorm g 0 s k φ ≤ negSobolevNorm g 0 s k a :=
    (mul_le_mul_of_nonneg_left hφ ha0).trans (mul_one _).le
  have h2 : negSobolevNorm g 0 s k b * sobolevNorm g 0 s k φ ≤ negSobolevNorm g 0 s k b :=
    (mul_le_mul_of_nonneg_left hφ hb0).trans (mul_one _).le
  linarith

theorem negSobolevNorm_le_add (s k : ℕ) (a b : SmoothCcTensor g 0 s) :
    negSobolevNorm g 0 s k a ≤ negSobolevNorm g 0 s k b + ‖a - b‖ := by
  refine csSup_le ⟨_, zero_mem_negSobolevNorm_set s k a⟩ ?_
  rintro _ ⟨φ, hφ, rfl⟩
  change tensorL2Inner (I := I) (M := M) g 0 s a.toFun φ.toFun ≤ _
  have hsplit : a.toFun = b.toFun + (a - b).toFun := by
    rw [SmoothCcTensor.toFun_sub, add_sub_cancel]
  rw [hsplit, tensorL2Inner_add_left _ _ _ _ _ _
    (SmoothCcTensor.integrable_inner_cross b φ) (SmoothCcTensor.integrable_inner_cross (a - b) φ)]
  have hb := inner_le_negSobolevNorm s k b φ
  have hb0 := negSobolevNorm_nonneg s k b
  have hb1 : negSobolevNorm g 0 s k b * sobolevNorm g 0 s k φ ≤ negSobolevNorm g 0 s k b :=
    (mul_le_mul_of_nonneg_left hφ hb0).trans (mul_one _).le
  have hcs := abs_inner_le_norm_mul_norm g 0 s (a - b) φ
  have hφ1 : jetNorm g s 0 φ ≤ 1 := (jetNorm_zero_le_sobolevNorm s k φ).trans hφ
  have hab0 := jetNorm_nonneg g s 0 (a - b)
  have hab : jetNorm g s 0 (a - b) * jetNorm g s 0 φ ≤ jetNorm g s 0 (a - b) :=
    (mul_le_mul_of_nonneg_left hφ1 hab0).trans (mul_one _).le
  have hn : jetNorm g s 0 (a - b) = ‖a - b‖ := jetNorm_zero_eq_norm _
  change |_| ≤ jetNorm g s 0 (a - b) * jetNorm g s 0 φ at hcs
  linarith [le_abs_self (tensorL2Inner (I := I) (M := M) g 0 s (a - b).toFun φ.toFun)]

theorem norm_sq_eq_integral {s : ℕ} (u : SmoothCcTensor g 0 s) :
    ‖u‖ ^ 2 = ∫ x, tensorInnerPointwise (I := I) (M := M) g 0 s x (u.toFun x) (u.toFun x)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  rw [← jetNorm_zero_eq_norm]
  exact (tensorL2Inner_self_eq_sq_norm g s u).symm

/-- A jointly smooth family vanishing at `t₀` is `L²`-small near `t₀`. -/
theorem tendsto_norm_of_jointlySmooth {T : ℝ} (hT : 0 < T) {s : ℕ} {D : ℝ → SmoothCcTensor g 0 s}
    (hD : JointlySmoothOn g 0 s (Icc 0 T) D) {t₀ : ℝ} (ht₀ : t₀ ∈ Icc 0 T) (h0 : D t₀ = 0) :
    Tendsto (fun t => ‖D t‖) (𝓝[Icc 0 T] t₀) (𝓝 0) := by
  have hc := continuousOn_l2Pairing hT hD hD t₀ ht₀
  have h := (Real.continuous_sqrt.tendsto _).comp hc
  have e : ∀ t, ‖D t‖ = Real.sqrt (∫ x, tensorInnerPointwise (I := I) (M := M) g 0 s x
      ((D t).toFun x) ((D t).toFun x) ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := fun t => by
    rw [← norm_sq_eq_integral, Real.sqrt_sq (norm_nonneg _)]
  have e0 : Real.sqrt (∫ x, tensorInnerPointwise (I := I) (M := M) g 0 s x
      ((D t₀).toFun x) ((D t₀).toFun x) ∂(riemannianVolumeMeasure (I := I) (M := M) g)) = 0 := by
    rw [← e, h0, norm_zero]
  rw [e0] at h
  exact h.congr fun t => (e t).symm

/-- `t ↦ ‖f(t)‖_{H^{-k}}` is continuous on `[0,T]` for a jointly smooth family. -/
theorem continuousOn_negSobolevNorm {T : ℝ} (hT : 0 < T) {s : ℕ} {f : ℝ → SmoothCcTensor g 0 s}
    (hf : JointlySmoothOn g 0 s (Icc 0 T) f) (k : ℕ) :
    ContinuousOn (fun t => negSobolevNorm g 0 s k (f t)) (Icc 0 T) := by
  intro t₀ ht₀
  have hD : JointlySmoothOn g 0 s (Icc 0 T) (fun t => f t - f t₀) :=
    jointlySmoothOn_sub hf (jointlySmoothOn_const g _ (f t₀))
  have hD' : JointlySmoothOn g 0 s (Icc 0 T) (fun t => f t₀ - f t) :=
    jointlySmoothOn_sub (jointlySmoothOn_const g _ (f t₀)) hf
  have h1 := tendsto_norm_of_jointlySmooth hT hD ht₀ (sub_self _)
  have h2 := tendsto_norm_of_jointlySmooth hT hD' ht₀ (sub_self _)
  have hsum := h1.add h2
  rw [add_zero] at hsum
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun t => ?_) hsum
  rw [Real.norm_eq_abs]
  have ha := negSobolevNorm_le_add s k (f t) (f t₀)
  have hb := negSobolevNorm_le_add s k (f t₀) (f t)
  exact abs_sub_le_iff.mpr ⟨by linarith [norm_nonneg (f t₀ - f t)],
    by linarith [norm_nonneg (f t - f t₀)]⟩

/-- `t ↦ ‖u(t)‖²_{H^k}` is continuous on `[0,T]` for a jointly smooth family. -/
theorem continuousOn_sobolevNormSq {T : ℝ} (hT : 0 < T) {s : ℕ} {u : ℝ → SmoothCcTensor g 0 s}
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u) (k : ℕ) :
    ContinuousOn (fun t => sobolevNormSq g 0 s k (u t)) (Icc 0 T) := by
  simp only [sobolevNormSq_eq_sum]
  refine continuousOn_finsetSum _ fun i _ => ?_
  have hi := jointlySmoothOn_iteratedCovGrad hu i
  have h := continuousOn_l2Pairing hT hi hi
  refine h.congr fun t _ => ?_
  exact (tensorL2Inner_self_eq_sq_norm g (s + i) (iteratedCovGrad g 0 s i (u t))).symm

/-! ### The base case -/

namespace LinearOp

variable {s p : ℕ} {T : ℝ} (L : LinearOp g s p T)

theorem energy_arith (X Y N2 e Nf sn lam C B : ℝ) (hG : lam / 4 * N2 - C * e ≤ -X)
    (hf : Y ≤ Nf * sn) (hy : sn * Nf ≤ lam / 8 * N2 + 2 / lam * Nf ^ 2) (heB : C * e ≤ B * e) :
    2 * (X + Y) + lam / 4 * N2 ≤ 2 * B * e + 4 / lam * Nf ^ 2 := by
  have h4 : 4 / lam * Nf ^ 2 = 2 * (2 / lam * Nf ^ 2) := by ring
  linarith [mul_comm Nf sn]

theorem young (x y lam : ℝ) (hlam : 0 < lam) : x * y ≤ lam / 8 * x ^ 2 + 2 / lam * y ^ 2 := by
  have h := sq_nonneg (lam / 4 * x - y)
  have h' : 0 ≤ (lam / 4 * x - y) ^ 2 / (lam / 2) := div_nonneg h (by positivity)
  have key : (lam / 4 * x - y) ^ 2 / (lam / 2) = lam / 8 * x ^ 2 + 2 / lam * y ^ 2 - x * y := by
    field_simp
    ring
  linarith

/-- **Energy estimate, base case, from Gårding's inequality**: the constant depends only on the
constants `lam`, `C₁` of Gårding's inequality `lam/4 ‖u‖²_{H^p} - C₁ ‖u‖² ≤ -⟨u, L u⟩`. -/
theorem energy_estimate_zero_of_garding (hT : 0 < T) {lam : ℝ} (hlam : 0 < lam) (C₁ : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ L : LinearOp g s p T,
      (∀ t ∈ Icc (0 : ℝ) T, ∀ u : SmoothCcTensor g 0 s,
        lam / 4 * sobolevNormSq g 0 s p u - C₁ * jetNorm g s 0 u ^ 2 ≤
          -tensorL2Inner (I := I) (M := M) g 0 s u.toFun (L.apply t u).toFun) →
      ∀ u f : ℝ → SmoothCcTensor g 0 s,
      JointlySmoothOn g 0 s (Icc 0 T) u → JointlySmoothOn g 0 s (Icc 0 T) f → u 0 = 0 →
      L.Solves u f →
      (∀ t ∈ Icc 0 T, ‖u t‖ ^ 2 ≤ C * ∫ τ in (0 : ℝ)..T, negSobolevNorm g 0 s p (f τ) ^ 2) ∧
        ∫ τ in (0 : ℝ)..T, sobolevNormSq g 0 s p (u τ) ≤
          C * ∫ τ in (0 : ℝ)..T, negSobolevNorm g 0 s p (f τ) ^ 2 := by
  set B := max C₁ 0
  set a := lam / 4
  set b := 2 * B
  set c := 4 / lam
  have ha : 0 < a := by positivity
  have hb : 0 ≤ b := by positivity
  have hc : 0 ≤ c := by positivity
  refine ⟨max (c * Real.exp (b * T)) (c * (1 + b * T * Real.exp (b * T)) / a), le_max_of_le_left
    (by positivity), fun L hC₁ u f hu hf hu0 hsol => ?_⟩
  have hv : JointlySmoothOn g 0 s (Icc 0 T) (fun t => L.apply t (u t) + f t) :=
    jointlySmoothOn_add (L.jointlySmoothOn_apply hu) hf
  -- the energy and its derivative
  set e : ℝ → ℝ := fun τ => tensorL2Inner (I := I) (M := M) g 0 s (u τ).toFun (u τ).toFun
  have he : ContinuousOn e (Icc 0 T) := continuousOn_l2Pairing hT hu hu
  have hN : ContinuousOn (fun τ => sobolevNormSq g 0 s p (u τ)) (Icc 0 T) :=
    continuousOn_sobolevNormSq hT hu p
  have hF : ContinuousOn (fun τ => negSobolevNorm g 0 s p (f τ) ^ 2) (Icc 0 T) :=
    (continuousOn_negSobolevNorm hT hf p).pow 2
  have he0 : e 0 = 0 := by
    simp only [e, hu0, SmoothCcTensor.toFun_zero]
    exact tensorL2Inner_zero_left (I := I) (M := M) g 0 s _
  have hen : ∀ t ∈ Icc 0 T, 0 ≤ e t := fun t _ => tensorL2Inner_nonneg (I := I) (M := M) g 0 s _
  have hd : ∀ t ∈ Ioo 0 T, HasDerivAt e
      (2 * tensorL2Inner (I := I) (M := M) g 0 s (u t).toFun (L.apply t (u t) + f t).toFun) t :=
    fun t ht => hasDerivAt_normSq g hu hv hsol ht
  -- the differential inequality
  have hineq : ∀ t ∈ Ioo 0 T,
      2 * tensorL2Inner (I := I) (M := M) g 0 s (u t).toFun (L.apply t (u t) + f t).toFun +
        a * sobolevNormSq g 0 s p (u t) ≤ b * e t + c * negSobolevNorm g 0 s p (f t) ^ 2 := by
    intro t ht
    have htI : t ∈ Icc 0 T := Ioo_subset_Icc_self ht
    rw [SmoothCcTensor.toFun_add, tensorL2Inner_add_right _ _ _ _ _ _
      (SmoothCcTensor.integrable_inner_cross _ _) (SmoothCcTensor.integrable_inner_cross _ _)]
    have hG := hC₁ t htI (u t)
    have hje : jetNorm g s 0 (u t) ^ 2 = e t := (tensorL2Inner_self_eq_sq_norm g s (u t)).symm
    rw [hje] at hG
    have hf' := inner_le_negSobolevNorm s p (f t) (u t)
    rw [tensorL2Inner_symm] at hf'
    have hy := young (sobolevNorm g 0 s p (u t)) (negSobolevNorm g 0 s p (f t)) lam hlam
    have hsq : sobolevNorm g 0 s p (u t) ^ 2 = sobolevNormSq g 0 s p (u t) :=
      Real.sq_sqrt (sobolevNormSq_nonneg s p (u t))
    have heB : C₁ * e t ≤ B * e t := mul_le_mul_of_nonneg_right (le_max_left _ _) (hen t htI)
    rw [hsq] at hy
    exact energy_arith _ _ _ _ _ _ lam C₁ B hG hf' hy heB
  obtain ⟨hsup, hint⟩ := energy_ode hT.le ha hb hc he hN hF he0 hen
    (fun t ht => sobolevNormSq_nonneg s p (u t)) (fun t _ => sq_nonneg _) hd hineq
  have hIF : 0 ≤ ∫ τ in (0 : ℝ)..T, negSobolevNorm g 0 s p (f τ) ^ 2 :=
    intervalIntegral.integral_nonneg hT.le fun _ _ => sq_nonneg _
  refine ⟨fun t ht => ?_, ?_⟩
  · have h := hsup t ht
    have hn : ‖u t‖ ^ 2 = e t := by
      rw [← jetNorm_zero_eq_norm]
      exact (tensorL2Inner_self_eq_sq_norm g s (u t)).symm
    rw [hn]
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hIF)
  · have h : ∫ τ in (0 : ℝ)..T, sobolevNormSq g 0 s p (u τ) ≤
        c * (1 + b * T * Real.exp (b * T)) / a * ∫ τ in (0 : ℝ)..T, negSobolevNorm g 0 s p (f τ) ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ ha]
      linarith
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hIF)

/-- **Energy estimate, base case** (`prop:energy`, `k = 0`): if `∂ₜu = Lu + f`, `u(0) = 0`, then
`sup ‖u‖² + ∫₀ᵀ ‖u‖²_{H^p} ≤ C ∫₀ᵀ ‖f‖²_{H^{-p}}`. -/
theorem energy_estimate_zero (hT : 0 < T) {lam : ℝ} (hL : L.IsParabolic lam) :
    ∃ C, 0 ≤ C ∧ ∀ u f : ℝ → SmoothCcTensor g 0 s,
      JointlySmoothOn g 0 s (Icc 0 T) u → JointlySmoothOn g 0 s (Icc 0 T) f → u 0 = 0 →
      L.Solves u f →
      (∀ t ∈ Icc 0 T, ‖u t‖ ^ 2 ≤ C * ∫ τ in (0 : ℝ)..T, negSobolevNorm g 0 s p (f τ) ^ 2) ∧
        ∫ τ in (0 : ℝ)..T, sobolevNormSq g 0 s p (u τ) ≤
          C * ∫ τ in (0 : ℝ)..T, negSobolevNorm g 0 s p (f τ) ^ 2 := by
  obtain ⟨C₁, hC₁⟩ := L.garding hL
  obtain ⟨C, hC, h⟩ := energy_estimate_zero_of_garding (g := g) (s := s) (p := p) hT hL.1 C₁
  exact ⟨C, hC, h L hC₁⟩

end LinearOp

end ShortTime
