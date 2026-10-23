import ShortTime.Linear.TimeCalc

/-!
# The a priori estimate in parabolic norms (`prop:apriori`)

For `m ≥ 1`, smooth `u` with `u(0) = 0` and `∂ₜu = L_θ u + f` along a segment of parabolic
operators, `‖u‖²_{𝒫^m} ≤ C ‖f‖²_{𝒫^{m-1}}` with `C` uniform in `θ` (`apriori_estimate`).

* `parabolicInner_self_eq`: `‖u‖²_{𝒫^m} = Σ_{j ≤ m} ∫₀ᵀ ‖∂ₜ^j u‖²_{H^{2p(m-j)}}`.
* The term `j = 0` is the energy estimate with `k = 2pm - p`. For `j ≥ 1`,
  `∂ₜ^j u = ∂ₜ^{j-1}(L_θ u) + ∂ₜ^{j-1} f`, and `∂ₜ^{j-1}(L_θ u)` is bounded by the lower terms
  (`LinearOp.exists_sobolevNormSq_timeDerivIter_apply_le`).
-/

noncomputable section

open Bundle Manifold Set MeasureTheory
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
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

/-! ### The parabolic norm through Sobolev norms of time derivatives -/

section Norm

variable {s : ℕ} {T : ℝ}

theorem continuousOn_jetNorm_sq (hT : 0 < T) {u : ℝ → SmoothCcTensor g 0 s}
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u) (i : ℕ) :
    ContinuousOn (fun t => jetNorm g s i (u t) ^ 2) (Icc 0 T) := by
  have h := continuousOn_sobolevNormSq hT (jointlySmoothOn_iteratedCovGrad hu i) 0
  simp only [sobolevNormSq_zero_eq] at h
  exact h

theorem mixedInner_self_eq (hT : 0 < T) {u : ℝ → SmoothCcTensor g 0 s}
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u) (j i : ℕ) :
    mixedInner g s T u u j i = ∫ t in (0 : ℝ)..T, jetNorm g s i (timeDerivIter T u j t) ^ 2 := by
  rw [mixedInner_eq hT hu hu, intervalIntegral.integral_of_le hT.le,
    ← integral_Icc_eq_integral_Ioc]
  refine setIntegral_congr_fun measurableSet_Icc fun t ht => ?_
  rw [timeDerivIter_iteratedCovGrad hT hu i j ht,
    ← tensorL2Inner_self_eq_sq_norm g (s + i) (iteratedCovGrad g 0 s i (timeDerivIter T u j t))]
  rfl

/-- **`‖u‖²_{𝒫^m} = Σ_{j ≤ m} ∫₀ᵀ ‖∂ₜ^j u‖²_{H^{2p(m-j)}}`.** -/
theorem parabolicInner_self_eq (hT : 0 < T) {u : ℝ → SmoothCcTensor g 0 s}
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u) (p m : ℕ) :
    parabolicInner g s p m T u u = ∑ j ∈ Finset.range (m + 1),
      ∫ t in (0 : ℝ)..T, sobolevNormSq g 0 s (2 * p * (m - j)) (timeDerivIter T u j t) := by
  unfold parabolicInner
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [mixedInner_self_eq hT hu, sobolevNormSq_eq_sum]
  rw [intervalIntegral.integral_finsetSum fun i _ =>
    (continuousOn_jetNorm_sq hT (jointlySmoothOn_timeDerivIter hT hu j) i).intervalIntegrable_of_Icc
      hT.le]

end Norm


/-! ### The estimate -/

theorem apriori_arith {X Y R a b P Q α β C0 C1 S : ℝ} (e1 : X ≤ 2 * Y + 2 * R)
    (e2 : Y ≤ 2 * a + 2 * b) (e3 : a = α * P) (e4 : b = β * Q) (hα : α ≤ 1) (hβ : β ≤ 1)
    (e5 : P ≤ C0 * S) (e6 : Q ≤ C1 * S) (hP : 0 ≤ P) (hQ : 0 ≤ Q) :
    X ≤ 4 * (C0 + C1) * S + 2 * R := by
  have h3 : a ≤ C0 * S := by rw [e3]; exact (mul_le_of_le_one_left hP hα).trans e5
  have h4 : b ≤ C1 * S := by rw [e4]; exact (mul_le_of_le_one_left hQ hβ).trans e6
  nlinarith

/-- **A priori estimate** (`prop:apriori`): for `m ≥ 1`, smooth `u` with `u(0) = 0` and
`∂ₜu = L_θ u + f`, `‖u‖²_{𝒫^m} ≤ C ‖f‖²_{𝒫^{m-1}}`, uniformly along the segment
`L_θ = (1-θ) L₀ + θ L₁` of two parabolic operators. -/
theorem apriori_estimate {s p : ℕ} {T : ℝ} (hT : 0 < T) (hp : 1 ≤ p) {m : ℕ} (hm : 1 ≤ m)
    (L₀ L₁ : LinearOp g s p T) {lam : ℝ} (h₀ : L₀.IsParabolic lam) (h₁ : L₁.IsParabolic lam) :
    ∃ C, 0 ≤ C ∧ ∀ θ ∈ Icc (0 : ℝ) 1, ∀ u f : ℝ → SmoothCcTensor g 0 s,
      JointlySmoothOn g 0 s (Icc 0 T) u → JointlySmoothOn g 0 s (Icc 0 T) f → u 0 = 0 →
      (LinearOp.lerp θ L₀ L₁).Solves u f →
      parabolicInner g s p m T u u ≤ C * parabolicInner g s p (m - 1) T f f := by
  -- the pieces `N_j = ∫ ‖∂ₜ^j u‖²_{H^{2p(m-j)}}` and `F = ‖f‖²_{𝒫^{m-1}}`
  set N : ℕ → (ℝ → SmoothCcTensor g 0 s) → ℝ := fun j u =>
    ∫ t in (0 : ℝ)..T, sobolevNormSq g 0 s (2 * p * (m - j)) (timeDerivIter T u j t) with hN
  set F : (ℝ → SmoothCcTensor g 0 s) → ℝ := fun f => ∑ j ∈ Finset.range m,
    ∫ t in (0 : ℝ)..T, sobolevNormSq g 0 s (2 * p * (m - 1 - j)) (timeDerivIter T f j t) with hF
  have hFterm : ∀ f : ℝ → SmoothCcTensor g 0 s, JointlySmoothOn g 0 s (Icc 0 T) f →
      ∀ j < m, ∫ t in (0 : ℝ)..T, sobolevNormSq g 0 s (2 * p * (m - 1 - j)) (timeDerivIter T f j t)
        ≤ F f := fun f hf j hj =>
    Finset.single_le_sum (f := fun j => ∫ t in (0 : ℝ)..T,
        sobolevNormSq g 0 s (2 * p * (m - 1 - j)) (timeDerivIter T f j t))
      (fun j _ => intervalIntegral.integral_nonneg hT.le fun t _ => sobolevNormSq_nonneg s _ _)
      (Finset.mem_range.mpr hj)
  -- the cumulative estimate `Σ_{b ≤ n} N_b ≤ K F`
  have key : ∀ n ≤ m, ∃ K, 0 ≤ K ∧ ∀ θ ∈ Icc (0 : ℝ) 1, ∀ u f : ℝ → SmoothCcTensor g 0 s,
      JointlySmoothOn g 0 s (Icc 0 T) u → JointlySmoothOn g 0 s (Icc 0 T) f → u 0 = 0 →
      (LinearOp.lerp θ L₀ L₁).Solves u f → ∑ b ∈ Finset.range (n + 1), N b u ≤ K * F f := by
    intro n
    induction n with
    | zero =>
      intro _
      obtain ⟨C, hC, hE⟩ := energy_estimate (g := g) hT p (2 * p * m - p) s L₀ L₁ lam h₀ h₁
      refine ⟨C, hC, fun θ hθ u f hu hf hu0 hsol => ?_⟩
      have h := (hE θ hθ u f hu hf hu0 hsol).2
      have hidx : 2 * p * m - p + p = 2 * p * (m - 0) := by
        rw [Nat.sub_zero, Nat.sub_add_cancel (by nlinarith)]
      have hnorm : ∀ τ, hNormSq g 0 s (((2 * p * m - p : ℕ) : ℤ) - p) (f τ) =
          sobolevNormSq g 0 s (2 * p * (m - 1 - 0)) (timeDerivIter T f 0 τ) := fun τ => by
        rw [hNormSq_of_nonneg (by push_cast [Nat.cast_sub (show p ≤ 2 * p * m by nlinarith)]; nlinarith)]
        congr 1
        rw [Nat.sub_zero, Nat.mul_sub_one]
        omega
      rw [hidx] at h
      simp only [hnorm] at h
      rw [Finset.sum_range_one]
      exact h.trans (mul_le_mul_of_nonneg_left (hFterm f hf 0 (by omega)) hC)
    | succ n ih =>
      intro hn
      obtain ⟨K, hK, hKe⟩ := ih (by omega)
      obtain ⟨C₀, hC₀, e₀⟩ := L₀.exists_sobolevNormSq_timeDerivIter_apply_le hT
        (2 * p * (m - (n + 1))) n
      obtain ⟨C₁, hC₁, e₁⟩ := L₁.exists_sobolevNormSq_timeDerivIter_apply_le hT
        (2 * p * (m - (n + 1))) n
      refine ⟨K + 4 * (C₀ + C₁) * K + 2, by positivity, fun θ hθ u f hu hf hu0 hsol => ?_⟩
      have hKu := hKe θ hθ u f hu hf hu0 hsol
      -- `∂ₜ^{n+1} u = (1-θ) ∂ₜ^n(L₀ u) + θ ∂ₜ^n(L₁ u) + ∂ₜ^n f` on `[0,T]`
      have hL₀ := L₀.jointlySmoothOn_apply hu
      have hL₁ := L₁.jointlySmoothOn_apply hu
      have hA₀ := jointlySmoothOn_smul (1 - θ) hL₀
      have hA₁ := jointlySmoothOn_smul θ hL₁
      have hsplit : ∀ t ∈ Icc (0 : ℝ) T, timeDerivIter T u (n + 1) t =
          ((1 - θ) • timeDerivIter T (fun τ => L₀.apply τ (u τ)) n t +
            θ • timeDerivIter T (fun τ => L₁.apply τ (u τ)) n t) + timeDerivIter T f n t := by
        intro t ht
        have hdu : EqOn (timeDeriv T u)
            (fun τ => ((1 - θ) • L₀.apply τ (u τ) + θ • L₁.apply τ (u τ)) + f τ) (Icc 0 T) :=
          fun τ hτ => by
            rw [timeDeriv_eq hT hu hτ (hsol τ hτ), LinearOp.apply_lerp]
        rw [timeDerivIter_succ', timeDerivIter_congr hT (jointlySmoothOn_timeDeriv hT hu)
          (jointlySmoothOn_add (jointlySmoothOn_add hA₀ hA₁) hf) hdu n ht,
          timeDerivIter_add hT (jointlySmoothOn_add hA₀ hA₁) hf n,
          timeDerivIter_add hT hA₀ hA₁ n, timeDerivIter_smul hT _ hL₀ n,
          timeDerivIter_smul hT _ hL₁ n]
      -- the pointwise bound
      set S : ℝ → ℝ := fun t => ∑ b ∈ Finset.range (n + 1),
        sobolevNormSq g 0 s (2 * p * (m - b)) (timeDerivIter T u b t) with hS
      have hmono : ∀ t, ∑ b ∈ Finset.range (n + 1),
          sobolevNormSq g 0 s (2 * p * (m - (n + 1)) + 2 * p) (timeDerivIter T u b t) ≤ S t :=
        fun t => Finset.sum_le_sum fun b hb => sobolevNormSq_mono s (by
          simp only [Finset.mem_range] at hb
          have : m - (n + 1) + 1 ≤ m - b := by omega
          nlinarith) _
      have hpt : ∀ t ∈ Icc (0 : ℝ) T,
          sobolevNormSq g 0 s (2 * p * (m - (n + 1))) (timeDerivIter T u (n + 1) t) ≤
            4 * (C₀ + C₁) * S t +
              2 * sobolevNormSq g 0 s (2 * p * (m - 1 - n)) (timeDerivIter T f n t) := by
        intro t ht
        rw [hsplit t ht, show m - 1 - n = m - (n + 1) by omega]
        exact apriori_arith (sobolevNormSq_add_le s _ _ _) (sobolevNormSq_add_le s _ _ _)
          (sobolevNormSq_smul s _ _ _) (sobolevNormSq_smul s _ _ _)
          (by nlinarith [hθ.1, hθ.2]) (by nlinarith [hθ.1, hθ.2])
          ((e₀ u hu t ht).trans (mul_le_mul_of_nonneg_left (hmono t) hC₀))
          ((e₁ u hu t ht).trans (mul_le_mul_of_nonneg_left (hmono t) hC₁))
          (sobolevNormSq_nonneg s _ _) (sobolevNormSq_nonneg s _ _)
      -- integrate
      have hcS : ContinuousOn S (Icc 0 T) := continuousOn_finsetSum _ fun b _ =>
        continuousOn_sobolevNormSq hT (jointlySmoothOn_timeDerivIter hT hu b) _
      have hcf := continuousOn_sobolevNormSq hT (jointlySmoothOn_timeDerivIter hT hf n)
        (2 * p * (m - 1 - n))
      have hint := integral_mono_Icc (G := fun t => 4 * (C₀ + C₁) * S t +
          2 * sobolevNormSq g 0 s (2 * p * (m - 1 - n)) (timeDerivIter T f n t)) hT.le
        (continuousOn_sobolevNormSq hT (jointlySmoothOn_timeDerivIter hT hu (n + 1)) _)
        ((continuousOn_const.mul hcS).add (continuousOn_const.mul hcf)) hpt
      have i1 : IntervalIntegrable (fun t => 4 * (C₀ + C₁) * S t) MeasureTheory.volume 0 T :=
        (continuousOn_const.mul hcS).intervalIntegrable_of_Icc hT.le
      have i2 : IntervalIntegrable (fun t => 2 * sobolevNormSq g 0 s (2 * p * (m - 1 - n))
          (timeDerivIter T f n t)) MeasureTheory.volume 0 T :=
        (continuousOn_const.mul hcf).intervalIntegrable_of_Icc hT.le
      rw [intervalIntegral.integral_add i1 i2, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul] at hint
      have hSint : ∫ t in (0 : ℝ)..T, S t = ∑ b ∈ Finset.range (n + 1), N b u := by
        rw [hS, intervalIntegral.integral_finsetSum fun b _ =>
          (continuousOn_sobolevNormSq hT (jointlySmoothOn_timeDerivIter hT hu b) _).intervalIntegrable_of_Icc
            hT.le]
      rw [hSint] at hint
      have hf' := hFterm f hf n (by omega)
      have hFnn : 0 ≤ F f := Finset.sum_nonneg fun j _ =>
        intervalIntegral.integral_nonneg hT.le fun t _ => sobolevNormSq_nonneg s _ _
      rw [Finset.sum_range_succ]
      have h4 := mul_le_mul_of_nonneg_left hKu (by positivity : (0 : ℝ) ≤ 4 * (C₀ + C₁))
      change ∑ b ∈ Finset.range (n + 1), N b u +
          ∫ t in (0 : ℝ)..T, sobolevNormSq g 0 s (2 * p * (m - (n + 1))) (timeDerivIter T u (n + 1) t)
        ≤ _
      nlinarith
  obtain ⟨K, hK, hKe⟩ := key m le_rfl
  refine ⟨K, hK, fun θ hθ u f hu hf hu0 hsol => ?_⟩
  rw [parabolicInner_self_eq hT hu, parabolicInner_self_eq hT hf, Nat.sub_add_cancel hm]
  exact hKe θ hθ u f hu hf hu0 hsol

end ShortTime
