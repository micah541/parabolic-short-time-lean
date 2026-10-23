import ShortTime.Linear.LegendreComm

/-!
# Higher energy estimates (`prop:energy`)

For `k ∈ ℕ`, smooth solutions of `∂ₜu = L u + f` with `u(0) = 0` satisfy

  `sup_t ‖u(t)‖²_{H^k} + ∫₀ᵀ ‖u‖²_{H^{k+p}} ≤ C ∫₀ᵀ ‖f‖²_{H^{k-p}}`       (`energy_estimate`).

The estimate is stated for the segment `L_θ = (1-θ) L₀ + θ L₁` (`LinearOp.lerp`) of two parabolic
operators, with a constant uniform in `θ ∈ [0, 1]`; the method of continuity needs this. The
proof is by induction on `k`, for all ranks at once. The case `k = 0` is Gårding's inequality and
Grönwall (`energy_estimate_zero_of_garding`); Gårding's inequality holds uniformly along the
segment (`garding_lerp`). For the step, `w = ∇u` solves `∂ₜw = L̃_θ w + S_θ u + ∇f`
(`exists_covGrad_comm`, `hasDerivWithinAt_covGrad`), where `L̃₀, L̃₁` are parabolic with the same
constant (`isParabolic_comm`).
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

variable {g : SmoothRiemannianMetric I M}

/-! ### The segment between two operators -/

namespace LinearOp

variable {s p : ℕ} {T : ℝ}

/-- The operator `(1 - θ) L₀ + θ L₁`. -/
def lerp (θ : ℝ) (L₀ L₁ : LinearOp g s p T) : LinearOp g s p T where
  coeff k t := (1 - θ) • L₀.coeff k t + θ • L₁.coeff k t
  smooth k := jointlySmoothOn_add (jointlySmoothOn_smul _ (L₀.smooth k))
    (jointlySmoothOn_smul _ (L₁.smooth k))

theorem apply_lerp (θ : ℝ) (L₀ L₁ : LinearOp g s p T) (t : ℝ) (u : SmoothCcTensor g 0 s) :
    (lerp θ L₀ L₁).apply t u = (1 - θ) • L₀.apply t u + θ • L₁.apply t u := by
  simp only [apply, lerp, operatorFieldApplication_add_left, operatorFieldApplication_smul_left,
    Finset.sum_add_distrib, Finset.smul_sum]

theorem garding_lerp_arith {θ a e X₀ X₁ C₀ C₁ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) (he : 0 ≤ e)
    (h₀ : a - C₀ * e ≤ X₀) (h₁ : a - C₁ * e ≤ X₁) :
    a - max C₀ C₁ * e ≤ (1 - θ) * X₀ + θ * X₁ := by
  have hm₀ : C₀ * e ≤ max C₀ C₁ * e := mul_le_mul_of_nonneg_right (le_max_left _ _) he
  have hm₁ : C₁ * e ≤ max C₀ C₁ * e := mul_le_mul_of_nonneg_right (le_max_right _ _) he
  nlinarith [hθ.1, hθ.2]

/-- **Gårding's inequality along the segment**, with constants uniform in `θ ∈ [0, 1]`. -/
theorem garding_lerp {L₀ L₁ : LinearOp g s p T} {lam : ℝ} (h₀ : L₀.IsParabolic lam)
    (h₁ : L₁.IsParabolic lam) :
    ∃ C : ℝ, ∀ θ ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) T, ∀ u : SmoothCcTensor g 0 s,
      lam / 4 * sobolevNormSq g 0 s p u - C * jetNorm g s 0 u ^ 2 ≤
        -tensorL2Inner (I := I) (M := M) g 0 s u.toFun ((lerp θ L₀ L₁).apply t u).toFun := by
  obtain ⟨C₀, hC₀⟩ := L₀.garding h₀
  obtain ⟨C₁, hC₁⟩ := L₁.garding h₁
  refine ⟨max C₀ C₁, fun θ hθ t ht u => ?_⟩
  have e₀ := hC₀ t ht u
  have e₁ := hC₁ t ht u
  have hsplit : -tensorL2Inner (I := I) (M := M) g 0 s u.toFun ((lerp θ L₀ L₁).apply t u).toFun =
      (1 - θ) * -tensorL2Inner (I := I) (M := M) g 0 s u.toFun (L₀.apply t u).toFun +
        θ * -tensorL2Inner (I := I) (M := M) g 0 s u.toFun (L₁.apply t u).toFun := by
    rw [apply_lerp, ← SmoothCcTensor.inner_def, ← SmoothCcTensor.inner_def,
      ← SmoothCcTensor.inner_def, inner_add_right, inner_smul_right, inner_smul_right]
    ring
  rw [hsplit]
  exact garding_lerp_arith hθ (sq_nonneg _) e₀ e₁

end LinearOp

/-! ### Time derivatives commute with `∇` -/

theorem eq_zero_of_inner_self {r s : ℕ} {d : SmoothCcTensor g r s} (h : inner ℝ d d = (0 : ℝ)) :
    d = 0 := by
  have hn : ‖d‖ = 0 := by
    have := real_inner_self_eq_norm_sq d
    rw [h] at this
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this.symm
  refine SmoothCcTensor.smoothCcTensor_eq_of_toL2_eq d 0 ?_
  rw [map_zero, ← norm_eq_zero, SmoothCcTensor.norm_toL2, hn]

/-- `d/dt ⟨A(t), φ⟩ = ⟨∂ₜA(t), φ⟩`, by polarization from `hasDerivAt_normSq`. -/
theorem hasDerivAt_inner_const {s : ℕ} {T : ℝ} {A B : ℝ → SmoothCcTensor g 0 s}
    (hA : JointlySmoothOn g 0 s (Icc 0 T) A) (hB : JointlySmoothOn g 0 s (Icc 0 T) B)
    (hd : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      HasDerivWithinAt (fun τ => (A τ).toFun x) ((B t).toFun x) (Icc 0 T) t)
    (φ : SmoothCcTensor g 0 s) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt (fun τ => inner ℝ (A τ) φ) (inner ℝ (B t) φ) t := by
  have h₁ := hasDerivAt_normSq g (u := fun τ => A τ + φ) (v := B)
    (jointlySmoothOn_add hA (jointlySmoothOn_const g _ φ)) hB
    (fun t ht x => by
      simpa only [SmoothCcTensor.toFun_add, Pi.add_apply] using (hd t ht x).add_const (φ.toFun x))
    ht
  have h₂ := hasDerivAt_normSq g hA hB hd ht
  simp only [← SmoothCcTensor.inner_def] at h₁ h₂
  have key : (fun τ => inner ℝ (A τ) φ) =
      fun τ => (inner ℝ (A τ + φ) (A τ + φ) - inner ℝ (A τ) (A τ) - inner ℝ φ φ) / 2 := by
    funext τ
    rw [inner_add_left, inner_add_right, inner_add_right, real_inner_comm φ (A τ)]
    ring
  rw [key]
  refine (((h₁.sub h₂).sub_const (inner ℝ φ φ)).div_const 2).congr_deriv ?_
  rw [inner_add_left, real_inner_comm φ (B t)]
  ring

/-- **`∂ₜ∇u = ∇∂ₜu`** for jointly smooth families (weakly: pair with test fields and integrate by
parts). -/
theorem hasDerivWithinAt_covGrad {s : ℕ} {T : ℝ} (hT : 0 < T) {u v : ℝ → SmoothCcTensor g 0 s}
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u) (hv : JointlySmoothOn g 0 s (Icc 0 T) v)
    (hd : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      HasDerivWithinAt (fun τ => (u τ).toFun x) ((v t).toFun x) (Icc 0 T) t) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      HasDerivWithinAt (fun τ => (covGrad (I := I) (M := M) g 0 s (u τ)).toFun x)
        ((covGrad (I := I) (M := M) g 0 s (v t)).toFun x) (Icc 0 T) t := by
  set U : ℝ → SmoothCcTensor g 0 (s + 1) := fun τ => covGrad (I := I) (M := M) g 0 s (u τ)
  have hU : JointlySmoothOn g 0 (s + 1) (Icc 0 T) U := jointlySmoothOn_covGrad hu
  have hV : JointlySmoothOn g 0 (s + 1) (Icc 0 T)
      (fun τ => covGrad (I := I) (M := M) g 0 s (v τ)) := jointlySmoothOn_covGrad hv
  set w := timeDeriv T U
  have hw : JointlySmoothOn g 0 (s + 1) (Icc 0 T) w := jointlySmoothOn_timeDeriv hT hU
  have hdw : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      HasDerivWithinAt (fun τ => (U τ).toFun x) ((w t).toFun x) (Icc 0 T) t :=
    fun t ht x => hasDerivWithinAt_timeDeriv hT hU ht x
  -- the pairings of `w` and `∇v` with any test field agree
  have hpair : ∀ φ : SmoothCcTensor g 0 (s + 1), EqOn (fun τ => inner ℝ (w τ) φ)
      (fun τ => inner ℝ (covGrad (I := I) (M := M) g 0 s (v τ)) φ) (Icc 0 T) := by
    intro φ
    have hibp : ∀ X : SmoothCcTensor g 0 s, inner ℝ (covGrad (I := I) (M := M) g 0 s X) φ =
        -inner ℝ X (covDivergence (I := I) (M := M) g s φ) := by
      intro X
      rw [SmoothCcTensor.inner_def, SmoothCcTensor.inner_def,
        tensorL2Inner_covGrad_eq_neg_tensorL2Inner_covDivergence]
    refine EqOn.of_subset_closure (s := Ioo 0 T) (fun τ hτ => ?_) ?_ ?_ Ioo_subset_Icc_self
      (by rw [closure_Ioo hT.ne])
    · have e₁ := hasDerivAt_inner_const hU hw hdw φ hτ
      have e₂ := (hasDerivAt_inner_const hu hv hd (covDivergence (I := I) (M := M) g s φ) hτ).neg
      have heq : (fun τ => inner ℝ (U τ) φ) =
          fun τ => -inner ℝ (u τ) (covDivergence (I := I) (M := M) g s φ) :=
        funext fun τ => hibp (u τ)
      rw [heq] at e₁
      exact (e₁.unique e₂).trans (hibp (v τ)).symm
    · simp only [SmoothCcTensor.inner_def]
      exact continuousOn_l2Pairing hT hw (jointlySmoothOn_const g _ φ)
    · simp only [SmoothCcTensor.inner_def]
      exact continuousOn_l2Pairing hT hV (jointlySmoothOn_const g _ φ)
  intro t ht x
  have hwt : w t = covGrad (I := I) (M := M) g 0 s (v t) := by
    have h0 := hpair (w t - covGrad (I := I) (M := M) g 0 s (v t)) ht
    simp only at h0
    refine sub_eq_zero.mp (eq_zero_of_inner_self ?_)
    rw [inner_sub_left, h0, sub_self]
  rw [← hwt]
  exact hdw t ht x

/-! ### The integer-order norms `hNormSq` -/

section HNorm

variable {s : ℕ}

theorem sobolevNormSq_zero_eq (u : SmoothCcTensor g 0 s) :
    sobolevNormSq g 0 s 0 u = jetNorm g s 0 u ^ 2 := by
  rw [sobolevNormSq_eq_sum, Finset.sum_range_one]

theorem hNormSq_of_nonneg {m : ℤ} (hm : 0 ≤ m) (f : SmoothCcTensor g 0 s) :
    hNormSq g 0 s m f = sobolevNormSq g 0 s m.toNat f := if_pos hm

theorem hNormSq_of_neg {m : ℤ} (hm : m < 0) (f : SmoothCcTensor g 0 s) :
    hNormSq g 0 s m f = negSobolevNorm g 0 s (-m).toNat f ^ 2 := if_neg (not_le.mpr hm)

theorem hNormSq_nonneg (m : ℤ) (f : SmoothCcTensor g 0 s) : 0 ≤ hNormSq g 0 s m f := by
  rcases le_or_gt 0 m with hm | hm
  · rw [hNormSq_of_nonneg hm]; exact sobolevNormSq_nonneg s _ f
  · rw [hNormSq_of_neg hm]; exact sq_nonneg _

theorem continuousOn_hNormSq {T : ℝ} (hT : 0 < T) {f : ℝ → SmoothCcTensor g 0 s}
    (hf : JointlySmoothOn g 0 s (Icc 0 T) f) (m : ℤ) :
    ContinuousOn (fun t => hNormSq g 0 s m (f t)) (Icc 0 T) := by
  rcases le_or_gt 0 m with hm | hm
  · simp only [hNormSq_of_nonneg hm]; exact continuousOn_sobolevNormSq hT hf _
  · simp only [hNormSq_of_neg hm]; exact (continuousOn_negSobolevNorm hT hf _).pow 2

theorem negSobolevNorm_sq_le_sobolevNormSq_zero (k : ℕ) (f : SmoothCcTensor g 0 s) :
    negSobolevNorm g 0 s k f ^ 2 ≤ sobolevNormSq g 0 s 0 f := by
  rw [sobolevNormSq_zero_eq]
  exact pow_le_pow_left₀ (negSobolevNorm_nonneg s k f) (negSobolevNorm_le_jetNorm s k f) 2

/-- `‖f‖²_{H^m} ≤ ‖f‖²_{H^{m+1}}`. -/
theorem hNormSq_le_succ (m : ℤ) (f : SmoothCcTensor g 0 s) :
    hNormSq g 0 s m f ≤ hNormSq g 0 s (m + 1) f := by
  rcases le_or_gt 0 m with hm | hm
  · rw [hNormSq_of_nonneg hm, hNormSq_of_nonneg (by omega)]
    exact sobolevNormSq_mono s (by omega) f
  · rw [hNormSq_of_neg hm]
    rcases eq_or_lt_of_le (show m + 1 ≤ 0 by omega) with h1 | h1
    · rw [h1, hNormSq_of_nonneg le_rfl]
      exact negSobolevNorm_sq_le_sobolevNormSq_zero _ f
    · rw [hNormSq_of_neg h1]
      obtain ⟨n, hn⟩ : ∃ n : ℕ, (-m).toNat = n + 1 ∧ (-(m + 1)).toNat = n :=
        ⟨(-(m + 1)).toNat, by omega, rfl⟩
      rw [hn.1, hn.2]
      exact pow_le_pow_left₀ (negSobolevNorm_nonneg s _ f) (negSobolevNorm_mono s n f) 2

theorem hNormSq_mono {m m' : ℤ} (h : m ≤ m') (f : SmoothCcTensor g 0 s) :
    hNormSq g 0 s m f ≤ hNormSq g 0 s m' f := by
  induction m', h using Int.leInduction with
  | base => exact le_rfl
  | succ n _ ih => exact ih.trans (hNormSq_le_succ n f)

/-- The base norm `‖f‖_{H^{-p}}` of `energy_estimate_zero` is at most the `hNormSq` one. -/
theorem negSobolevNorm_sq_le_hNormSq (p : ℕ) (f : SmoothCcTensor g 0 s) :
    negSobolevNorm g 0 s p f ^ 2 ≤ hNormSq g 0 s ((0 : ℕ) - (p : ℤ)) f := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · rw [show ((0 : ℕ) : ℤ) - ((0 : ℕ) : ℤ) = 0 by simp, hNormSq_of_nonneg le_rfl]
    exact negSobolevNorm_sq_le_sobolevNormSq_zero _ f
  · rw [hNormSq_of_neg (by omega), show (-(((0 : ℕ) : ℤ) - (p : ℤ))).toNat = p by omega]

theorem negSobolevNorm_smul_le (k : ℕ) (c : ℝ) (f : SmoothCcTensor g 0 s) :
    negSobolevNorm g 0 s k (c • f) ≤ |c| * negSobolevNorm g 0 s k f := by
  refine csSup_le ⟨_, zero_mem_negSobolevNorm_set s k (c • f)⟩ ?_
  rintro _ ⟨φ, hφ, rfl⟩
  change tensorL2Inner (I := I) (M := M) g 0 s (c • f).toFun φ.toFun ≤ _
  rw [SmoothCcTensor.toFun_smul, tensorL2Inner_smul_left]
  have h1 := abs_inner_le_negSobolevNorm s k f φ
  have h2 : negSobolevNorm g 0 s k f * sobolevNorm g 0 s k φ ≤ negSobolevNorm g 0 s k f :=
    by simpa using mul_le_mul_of_nonneg_left hφ (negSobolevNorm_nonneg s k f)
  calc c * tensorL2Inner (I := I) (M := M) g 0 s f.toFun φ.toFun
      ≤ |c| * |tensorL2Inner (I := I) (M := M) g 0 s f.toFun φ.toFun| := by
        rw [← abs_mul]; exact le_abs_self _
    _ ≤ |c| * negSobolevNorm g 0 s k f := mul_le_mul_of_nonneg_left (h1.trans h2) (abs_nonneg c)

theorem hNormSq_smul_le (m : ℤ) (c : ℝ) (f : SmoothCcTensor g 0 s) :
    hNormSq g 0 s m (c • f) ≤ c ^ 2 * hNormSq g 0 s m f := by
  rcases le_or_gt 0 m with hm | hm
  · rw [hNormSq_of_nonneg hm, hNormSq_of_nonneg hm, sobolevNormSq_smul]
  · rw [hNormSq_of_neg hm, hNormSq_of_neg hm, ← sq_abs c, ← mul_pow]
    exact pow_le_pow_left₀ (negSobolevNorm_nonneg s _ _) (negSobolevNorm_smul_le _ c f) 2

theorem hNormSq_add_le (m : ℤ) (a b : SmoothCcTensor g 0 s) :
    hNormSq g 0 s m (a + b) ≤ 2 * hNormSq g 0 s m a + 2 * hNormSq g 0 s m b := by
  rcases le_or_gt 0 m with hm | hm
  · simp only [hNormSq_of_nonneg hm]; exact sobolevNormSq_add_le s _ a b
  · simp only [hNormSq_of_neg hm]
    have h := negSobolevNorm_add_le s (-m).toNat a b
    have ha := negSobolevNorm_nonneg s (-m).toNat a
    have hb := negSobolevNorm_nonneg s (-m).toNat b
    have hab := negSobolevNorm_nonneg s (-m).toNat (a + b)
    nlinarith [sq_nonneg (negSobolevNorm g 0 s (-m).toNat a - negSobolevNorm g 0 s (-m).toNat b)]

/-- `‖∇f‖²_{H^m} ≤ C ‖f‖²_{H^{m+1}}` for every integer `m`. -/
theorem exists_hNormSq_covGrad_le (s : ℕ) (m : ℤ) :
    ∃ C, 0 ≤ C ∧ ∀ f : SmoothCcTensor g 0 s,
      hNormSq g 0 (s + 1) m (covGrad (I := I) (M := M) g 0 s f) ≤ C * hNormSq g 0 s (m + 1) f := by
  rcases le_or_gt 0 m with hm | hm
  · refine ⟨1, zero_le_one, fun f => ?_⟩
    rw [hNormSq_of_nonneg hm, hNormSq_of_nonneg (by omega), one_mul,
      show (m + 1).toNat = m.toNat + 1 by omega]
    exact sobolevNormSq_covGrad_le s _ f
  · obtain ⟨j, hj⟩ : ∃ j : ℕ, (-m).toNat = j + 1 := ⟨(-m).toNat - 1, by omega⟩
    obtain ⟨C, hC, h⟩ := exists_negSobolevNorm_covGrad_le (g := g) s j
    refine ⟨C ^ 2, sq_nonneg C, fun f => ?_⟩
    rw [hNormSq_of_neg hm, hj]
    have hf := h f
    have hsq : negSobolevNorm g 0 (s + 1) (j + 1) (covGrad (I := I) (M := M) g 0 s f) ^ 2 ≤
        C ^ 2 * negSobolevNorm g 0 s j f ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (negSobolevNorm_nonneg _ _ _) hf 2
    refine hsq.trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg C))
    rcases eq_or_lt_of_le (show m + 1 ≤ 0 by omega) with h1 | h1
    · rw [h1, hNormSq_of_nonneg le_rfl]
      exact negSobolevNorm_sq_le_sobolevNormSq_zero j f
    · rw [hNormSq_of_neg h1, show (-(m + 1)).toNat = j by omega]

/-- A coefficient field maps `H^{m⁺}` to `H^m`, uniformly in time. -/
theorem exists_hNormSq_opField_le {T : ℝ} {a b : ℕ} (m : ℤ) (Φ : ℝ → SmoothCcTensor g a b)
    (hΦ : JointlySmoothOn g a b (Icc 0 T) Φ) :
    ∃ C, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) T, ∀ W : SmoothCcTensor g 0 a,
      hNormSq g 0 b m (operatorFieldApply (I := I) (M := M) g a b (Φ t) W) ≤
        C * sobolevNormSq g 0 a m.toNat W := by
  rcases le_or_gt 0 m with hm | hm
  · obtain ⟨C, hC, h⟩ := exists_sobolevNormSq_opField_le (g := g) (T := T) m.toNat a b Φ hΦ
    exact ⟨C, hC, fun t ht W => by rw [hNormSq_of_nonneg hm]; exact h t ht W⟩
  · obtain ⟨C, hC, h⟩ := exists_sobolevNormSq_opField_le (g := g) (T := T) 0 a b Φ hΦ
    refine ⟨C, hC, fun t ht W => ?_⟩
    rw [hNormSq_of_neg hm, show m.toNat = 0 by omega]
    exact (negSobolevNorm_sq_le_sobolevNormSq_zero _ _).trans (h t ht W)

end HNorm

/-- Monotonicity of `∫₀ᵀ` for functions continuous on `[0, T]`. -/
theorem integral_mono_Icc {T : ℝ} (hT : 0 ≤ T) {F G : ℝ → ℝ} (hF : ContinuousOn F (Icc 0 T))
    (hG : ContinuousOn G (Icc 0 T)) (h : ∀ t ∈ Icc (0 : ℝ) T, F t ≤ G t) :
    ∫ τ in (0 : ℝ)..T, F τ ≤ ∫ τ in (0 : ℝ)..T, G τ :=
  intervalIntegral.integral_mono_on hT (hF.intervalIntegrable_of_Icc hT)
    (hG.intervalIntegrable_of_Icc hT) h


/-! ### The energy estimates -/

theorem energy_step_arith {F Gd B X Y X0 Y0 Sm G H a2 b2 Cd C0 C1 : ℝ}
    (e1 : F ≤ 2 * Gd + 2 * B) (e2 : B ≤ 2 * X + 2 * Y) (e3 : X ≤ a2 * X0) (e4 : Y ≤ b2 * Y0)
    (e5 : X0 ≤ C0 * Sm) (e6 : Y0 ≤ C1 * Sm) (e7 : Gd ≤ Cd * G) (e8 : Sm ≤ H)
    (ha1 : a2 ≤ 1) (hb1 : b2 ≤ 1) (hX0 : 0 ≤ X0) (hY0 : 0 ≤ Y0)
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) :
    F ≤ 2 * Cd * G + 4 * (C0 + C1) * H := by
  have h3 : X ≤ C0 * H :=
    e3.trans ((mul_le_of_le_one_left hX0 ha1).trans (e5.trans (mul_le_mul_of_nonneg_left e8 hC0)))
  have h4 : Y ≤ C1 * H :=
    e4.trans ((mul_le_of_le_one_left hY0 hb1).trans (e6.trans (mul_le_mul_of_nonneg_left e8 hC1)))
  nlinarith

/-- **Energy estimates** (`prop:energy`): for `k ∈ ℕ`, smooth solutions of `∂ₜu = L_θ u + f`,
`u(0) = 0`, along the segment `L_θ = (1-θ) L₀ + θ L₁` of two parabolic operators satisfy
`sup_t ‖u(t)‖²_{H^k} + ∫₀ᵀ ‖u‖²_{H^{k+p}} ≤ C ∫₀ᵀ ‖f‖²_{H^{k-p}}`, with `C` uniform in
`θ ∈ [0, 1]`. -/
theorem energy_estimate {T : ℝ} (hT : 0 < T) (p : ℕ) (k : ℕ) :
    ∀ (s : ℕ) (L₀ L₁ : LinearOp g s p T) (lam : ℝ), L₀.IsParabolic lam → L₁.IsParabolic lam →
      ∃ C, 0 ≤ C ∧ ∀ θ ∈ Icc (0 : ℝ) 1, ∀ u f : ℝ → SmoothCcTensor g 0 s,
        JointlySmoothOn g 0 s (Icc 0 T) u → JointlySmoothOn g 0 s (Icc 0 T) f → u 0 = 0 →
        (LinearOp.lerp θ L₀ L₁).Solves u f →
        (∀ t ∈ Icc (0 : ℝ) T, sobolevNormSq g 0 s k (u t) ≤
            C * ∫ τ in (0 : ℝ)..T, hNormSq g 0 s ((k : ℤ) - p) (f τ)) ∧
          ∫ τ in (0 : ℝ)..T, sobolevNormSq g 0 s (k + p) (u τ) ≤
            C * ∫ τ in (0 : ℝ)..T, hNormSq g 0 s ((k : ℤ) - p) (f τ) := by
  induction k with
  | zero =>
    intro s L₀ L₁ lam h₀ h₁
    obtain ⟨C₁, hC₁⟩ := LinearOp.garding_lerp h₀ h₁
    obtain ⟨C, hC, hE⟩ :=
      LinearOp.energy_estimate_zero_of_garding (g := g) (s := s) (p := p) hT h₀.1 C₁
    refine ⟨C, hC, fun θ hθ u f hu hf hu0 hsol => ?_⟩
    obtain ⟨h1, h2⟩ := hE _ (hC₁ θ hθ) u f hu hf hu0 hsol
    have hF : ∫ τ in (0 : ℝ)..T, negSobolevNorm g 0 s p (f τ) ^ 2 ≤
        ∫ τ in (0 : ℝ)..T, hNormSq g 0 s ((0 : ℕ) - (p : ℤ)) (f τ) :=
      integral_mono_Icc hT.le ((continuousOn_negSobolevNorm hT hf p).pow 2)
        (continuousOn_hNormSq hT hf _) fun t _ => negSobolevNorm_sq_le_hNormSq p (f t)
    refine ⟨fun t ht => ?_, ?_⟩
    · rw [sobolevNormSq_zero_eq, jetNorm_zero_eq_norm]
      exact (h1 t ht).trans (mul_le_mul_of_nonneg_left hF hC)
    · rw [Nat.zero_add]
      exact h2.trans (mul_le_mul_of_nonneg_left hF hC)
  | succ k ih =>
    intro s L₀ L₁ lam h₀ h₁
    obtain ⟨L₀', S₀, hS₀, hL₀', hc₀⟩ := L₀.exists_covGrad_comm
    obtain ⟨L₁', S₁, hS₁, hL₁', hc₁⟩ := L₁.exists_covGrad_comm
    obtain ⟨C', hC', hE'⟩ := ih (s + 1) L₀' L₁' lam (LinearOp.isParabolic_comm L₀ L₀' hL₀' h₀)
      (LinearOp.isParabolic_comm L₁ L₁' hL₁' h₁)
    obtain ⟨C, hC, hE⟩ := ih s L₀ L₁ lam h₀ h₁
    set m : ℤ := (k : ℤ) - p with hm
    have hm1 : ((k + 1 : ℕ) : ℤ) - p = m + 1 := by rw [hm]; push_cast; ring
    rw [hm1]
    obtain ⟨Cd, hCd, hgrad⟩ := exists_hNormSq_covGrad_le (g := g) s m
    obtain ⟨Cs₀, hCs₀, hs₀⟩ := exists_hNormSq_opField_le (T := T) m S₀ hS₀
    obtain ⟨Cs₁, hCs₁, hs₁⟩ := exists_hNormSq_opField_le (T := T) m S₁ hS₁
    set K := 2 * Cd + 4 * (Cs₀ + Cs₁) * C with hK
    have hK0 : 0 ≤ K := by positivity
    refine ⟨C + C' * K + T * C, by positivity, fun θ hθ u f hu hf hu0 hsol => ?_⟩
    -- `w = ∇u` solves the differentiated equation
    set w : ℝ → SmoothCcTensor g 0 (s + 1) := fun t => covGrad (I := I) (M := M) g 0 s (u t)
    set f' : ℝ → SmoothCcTensor g 0 (s + 1) := fun t => covGrad (I := I) (M := M) g 0 s (f t) +
      ((1 - θ) • operatorFieldApply (I := I) (M := M) g s (s + 1) (S₀ t) (u t) +
        θ • operatorFieldApply (I := I) (M := M) g s (s + 1) (S₁ t) (u t))
    have hw : JointlySmoothOn g 0 (s + 1) (Icc 0 T) w := jointlySmoothOn_covGrad hu
    have hf' : JointlySmoothOn g 0 (s + 1) (Icc 0 T) f' :=
      jointlySmoothOn_add (jointlySmoothOn_covGrad hf)
        (jointlySmoothOn_add (jointlySmoothOn_smul _ (jointlySmoothOn_operatorFieldApply hS₀ hu))
          (jointlySmoothOn_smul _ (jointlySmoothOn_operatorFieldApply hS₁ hu)))
    have hw0 : w 0 = 0 := by simp only [w, hu0, covGrad_zero]
    have hsol' : (LinearOp.lerp θ L₀' L₁').Solves w f' := by
      intro t ht x
      have hv : JointlySmoothOn g 0 s (Icc 0 T)
          (fun t => (LinearOp.lerp θ L₀ L₁).apply t (u t) + f t) :=
        jointlySmoothOn_add ((LinearOp.lerp θ L₀ L₁).jointlySmoothOn_apply hu) hf
      have h := hasDerivWithinAt_covGrad hT hu hv hsol t ht x
      have heq : covGrad (I := I) (M := M) g 0 s ((LinearOp.lerp θ L₀ L₁).apply t (u t) + f t) =
          (LinearOp.lerp θ L₀' L₁').apply t (w t) + f' t := by
        simp only [w, f', LinearOp.apply_lerp, covGrad_add, covGrad_smul, hc₀, hc₁, smul_add]
        abel
      rw [heq] at h
      exact h
    obtain ⟨hw1, hw2⟩ := hE' θ hθ w f' hw hf' hw0 hsol'
    obtain ⟨hu1, hu2⟩ := hE θ hθ u f hu hf hu0 hsol
    -- integrals of the data
    set IF := ∫ τ in (0 : ℝ)..T, hNormSq g 0 s (m + 1) (f τ)
    have hIF0 : 0 ≤ IF := intervalIntegral.integral_nonneg hT.le fun τ _ => hNormSq_nonneg _ _
    have hcm := continuousOn_hNormSq hT hf m
    have hcm1 := continuousOn_hNormSq hT hf (m + 1)
    have hIm : ∫ τ in (0 : ℝ)..T, hNormSq g 0 s m (f τ) ≤ IF :=
      integral_mono_Icc hT.le hcm hcm1 fun τ _ => hNormSq_le_succ m (f τ)
    have hcu := continuousOn_sobolevNormSq hT hu (k + p)
    -- `∫ ‖f'‖²_{H^m} ≤ K ∫ ‖f‖²_{H^{m+1}}`
    have hpt : ∀ τ ∈ Icc (0 : ℝ) T, hNormSq g 0 (s + 1) m (f' τ) ≤
        2 * Cd * hNormSq g 0 s (m + 1) (f τ) +
          4 * (Cs₀ + Cs₁) * sobolevNormSq g 0 s (k + p) (u τ) := by
      intro τ hτ
      exact energy_step_arith (hNormSq_add_le m _ _) (hNormSq_add_le m _ _)
        (hNormSq_smul_le m (1 - θ) _) (hNormSq_smul_le m θ _) (hs₀ τ hτ (u τ)) (hs₁ τ hτ (u τ))
        (hgrad (f τ)) (sobolevNormSq_mono s (by omega) (u τ))
        (by nlinarith [hθ.1, hθ.2]) (by nlinarith [hθ.1, hθ.2])
        (hNormSq_nonneg _ _) (hNormSq_nonneg _ _) hCs₀ hCs₁
    have hF' : ∫ τ in (0 : ℝ)..T, hNormSq g 0 (s + 1) m (f' τ) ≤ K * IF := by
      have h1 := integral_mono_Icc (G := fun τ => 2 * Cd * hNormSq g 0 s (m + 1) (f τ) +
          4 * (Cs₀ + Cs₁) * sobolevNormSq g 0 s (k + p) (u τ)) hT.le (continuousOn_hNormSq hT hf' m)
        ((continuousOn_const.mul hcm1).add (continuousOn_const.mul hcu)) hpt
      have i1 : IntervalIntegrable (fun τ => 2 * Cd * hNormSq g 0 s (m + 1) (f τ)) volume 0 T :=
        (continuousOn_const.mul hcm1).intervalIntegrable_of_Icc hT.le
      have i2 : IntervalIntegrable (fun τ => 4 * (Cs₀ + Cs₁) * sobolevNormSq g 0 s (k + p) (u τ))
          volume 0 T := (continuousOn_const.mul hcu).intervalIntegrable_of_Icc hT.le
      rw [intervalIntegral.integral_add i1 i2,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h1
      have h2 := mul_le_mul_of_nonneg_left (hu2.trans (mul_le_mul_of_nonneg_left hIm hC))
        (by positivity : (0 : ℝ) ≤ 4 * (Cs₀ + Cs₁))
      rw [hK]
      nlinarith
    -- the two estimates for `u`
    have hsup : ∀ t ∈ Icc (0 : ℝ) T, jetNorm g s 0 (u t) ^ 2 ≤ C * IF := fun t ht =>
      (jetNorm_zero_sq_le s k (u t)).trans ((hu1 t ht).trans (mul_le_mul_of_nonneg_left hIm hC))
    refine ⟨fun t ht => ?_, ?_⟩
    · rw [sobolevNormSq_succ]
      have h1 := hw1 t ht
      have h2 := hsup t ht
      have h3 := mul_le_mul_of_nonneg_left hF' hC'
      have h4 : 0 ≤ T * C * IF := by positivity
      nlinarith
    · have hsplit : ∀ τ, sobolevNormSq g 0 s (k + 1 + p) (u τ) =
          jetNorm g s 0 (u τ) ^ 2 + sobolevNormSq g 0 (s + 1) (k + p) (w τ) := fun τ => by
        rw [show k + 1 + p = (k + p) + 1 by omega, sobolevNormSq_succ]
      simp only [hsplit]
      have hc0 : ContinuousOn (fun τ => jetNorm g s 0 (u τ) ^ 2) (Icc 0 T) := by
        simpa only [sobolevNormSq_zero_eq] using continuousOn_sobolevNormSq hT hu 0
      have hcw := continuousOn_sobolevNormSq hT hw (k + p)
      rw [intervalIntegral.integral_add (hc0.intervalIntegrable_of_Icc hT.le)
        (hcw.intervalIntegrable_of_Icc hT.le)]
      have h1 : ∫ τ in (0 : ℝ)..T, jetNorm g s 0 (u τ) ^ 2 ≤ T * (C * IF) := by
        have := integral_mono_Icc hT.le hc0 continuousOn_const hsup
        rwa [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at this
      have h3 := mul_le_mul_of_nonneg_left hF' hC'
      have h4 : 0 ≤ C * IF := by positivity
      nlinarith

end ShortTime
