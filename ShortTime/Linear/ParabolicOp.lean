import ShortTime.Linear.Apriori

/-!
# The operator `∂ₜ - L` between parabolic spaces

On jointly smooth families, `(∂ₜ - L) u = ∂ₜu - L u` (`LinearOp.heatOp`) satisfies
`‖(∂ₜ - L)u‖²_{𝒫^{m-1}} ≤ C ‖u‖²_{𝒫^m}` (`LinearOp.parabolicInner_heatOp_le`).
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

theorem sobolevNormSq_sub_le {s : ℕ} (l : ℕ) (a b : SmoothCcTensor g 0 s) :
    sobolevNormSq g 0 s l (a - b) ≤ 2 * sobolevNormSq g 0 s l a + 2 * sobolevNormSq g 0 s l b := by
  have h := sobolevNormSq_add_le s l a ((-1 : ℝ) • b)
  rw [sobolevNormSq_smul, neg_one_sq, one_mul, neg_one_smul, ← sub_eq_add_neg] at h
  exact h

namespace LinearOp

variable {s p : ℕ} {T : ℝ}

/-- `(∂ₜ - L) u`. -/
def heatOp (L : LinearOp g s p T) (u : ℝ → SmoothCcTensor g 0 s) : ℝ → SmoothCcTensor g 0 s :=
  fun t => timeDeriv T u t - L.apply t (u t)

theorem jointlySmoothOn_heatOp (hT : 0 < T) (L : LinearOp g s p T) {u : ℝ → SmoothCcTensor g 0 s}
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u) : JointlySmoothOn g 0 s (Icc 0 T) (L.heatOp u) :=
  jointlySmoothOn_sub (jointlySmoothOn_timeDeriv hT hu) (L.jointlySmoothOn_apply hu)

theorem timeDerivIter_heatOp (hT : 0 < T) (L : LinearOp g s p T) {u : ℝ → SmoothCcTensor g 0 s}
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u) (j : ℕ) :
    timeDerivIter T (L.heatOp u) j =
      fun t => timeDerivIter T u (j + 1) t - timeDerivIter T (fun τ => L.apply τ (u τ)) j t := by
  have hfun : L.heatOp u = fun τ => timeDeriv T u τ + (-1 : ℝ) • L.apply τ (u τ) :=
    funext fun τ => by rw [heatOp, neg_one_smul, sub_eq_add_neg]
  rw [hfun, timeDerivIter_add hT (jointlySmoothOn_timeDeriv hT hu)
    (jointlySmoothOn_smul (-1) (L.jointlySmoothOn_apply hu)) j,
    timeDerivIter_smul hT (-1) (L.jointlySmoothOn_apply hu) j, ← timeDerivIter_succ']
  funext t
  simp only [neg_one_smul, ← sub_eq_add_neg]

/-- **`∂ₜ - L : 𝒫^m → 𝒫^{m-1}` is bounded** on smooth families (`m ≥ 1`). -/
theorem parabolicInner_heatOp_le (hT : 0 < T) (L : LinearOp g s p T) {m : ℕ} (hm : 1 ≤ m) :
    ∃ C, 0 ≤ C ∧ ∀ u : ℝ → SmoothCcTensor g 0 s, JointlySmoothOn g 0 s (Icc 0 T) u →
      parabolicInner g s p (m - 1) T (L.heatOp u) (L.heatOp u) ≤
        C * parabolicInner g s p m T u u := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hj : ∀ j : ℕ, ∃ C, 0 ≤ C ∧ ∀ u : ℝ → SmoothCcTensor g 0 s,
      JointlySmoothOn g 0 s (Icc 0 T) u → ∀ t ∈ Icc (0 : ℝ) T,
        sobolevNormSq g 0 s (2 * p * (n - j)) (timeDerivIter T (fun τ => L.apply τ (u τ)) j t) ≤
          C * ∑ b ∈ Finset.range (j + 1),
            sobolevNormSq g 0 s (2 * p * (n - j) + 2 * p) (timeDerivIter T u b t) :=
    fun j => exists_sobolevNormSq_timeDerivIter_apply_le hT _ j L
  choose C hC0 hC using hj
  set K := 2 + 2 * ∑ j ∈ Finset.range (n + 1), C j with hK
  refine ⟨K, add_nonneg (by norm_num) (mul_nonneg (by norm_num)
    (Finset.sum_nonneg fun j _ => hC0 j)), fun u hu => ?_⟩
  rw [Nat.add_sub_cancel, parabolicInner_self_eq hT (L.jointlySmoothOn_heatOp hT hu),
    parabolicInner_self_eq hT hu]
  set N : ℕ → ℝ := fun b =>
    ∫ t in (0 : ℝ)..T, sobolevNormSq g 0 s (2 * p * (n + 1 - b)) (timeDerivIter T u b t) with hN
  have hNnn : ∀ b, 0 ≤ N b := fun b =>
    intervalIntegral.integral_nonneg hT.le fun t _ => sobolevNormSq_nonneg s _ _
  have hcont : ∀ b l, ContinuousOn (fun t => sobolevNormSq g 0 s l (timeDerivIter T u b t))
      (Icc 0 T) := fun b l => continuousOn_sobolevNormSq hT (jointlySmoothOn_timeDerivIter hT hu b) l
  -- one term
  have hterm : ∀ j ∈ Finset.range (n + 1),
      ∫ t in (0 : ℝ)..T, sobolevNormSq g 0 s (2 * p * (n - j))
          (timeDerivIter T (L.heatOp u) j t) ≤
        2 * N (j + 1) + 2 * C j * ∑ b ∈ Finset.range (j + 1), N b := by
    intro j hj
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hpt : ∀ t ∈ Icc (0 : ℝ) T, sobolevNormSq g 0 s (2 * p * (n - j))
          (timeDerivIter T (L.heatOp u) j t) ≤
        2 * sobolevNormSq g 0 s (2 * p * (n + 1 - (j + 1))) (timeDerivIter T u (j + 1) t) +
          2 * C j * ∑ b ∈ Finset.range (j + 1),
            sobolevNormSq g 0 s (2 * p * (n + 1 - b)) (timeDerivIter T u b t) := by
      intro t ht
      rw [timeDerivIter_heatOp hT L hu j, show n + 1 - (j + 1) = n - j by omega]
      refine (sobolevNormSq_sub_le _ _ _).trans ?_
      have h1 := hC j u hu t ht
      have h2 : ∑ b ∈ Finset.range (j + 1),
            sobolevNormSq g 0 s (2 * p * (n - j) + 2 * p) (timeDerivIter T u b t) ≤
          ∑ b ∈ Finset.range (j + 1),
            sobolevNormSq g 0 s (2 * p * (n + 1 - b)) (timeDerivIter T u b t) :=
        Finset.sum_le_sum fun b hb => sobolevNormSq_mono s (by
          simp only [Finset.mem_range] at hb
          have : n - j + 1 ≤ n + 1 - b := by omega
          nlinarith) _
      nlinarith [mul_le_mul_of_nonneg_left h2 (hC0 j)]
    have hcS : ContinuousOn (fun t => ∑ b ∈ Finset.range (j + 1),
        sobolevNormSq g 0 s (2 * p * (n + 1 - b)) (timeDerivIter T u b t)) (Icc 0 T) :=
      continuousOn_finsetSum _ fun b _ => hcont b _
    have hint := integral_mono_Icc (G := fun t =>
        2 * sobolevNormSq g 0 s (2 * p * (n + 1 - (j + 1))) (timeDerivIter T u (j + 1) t) +
          2 * C j * ∑ b ∈ Finset.range (j + 1),
            sobolevNormSq g 0 s (2 * p * (n + 1 - b)) (timeDerivIter T u b t)) hT.le
      (continuousOn_sobolevNormSq hT
        (jointlySmoothOn_timeDerivIter hT (L.jointlySmoothOn_heatOp hT hu) j) _)
      ((continuousOn_const.mul (hcont (j + 1) _)).add (continuousOn_const.mul hcS)) hpt
    have i1 : IntervalIntegrable (fun t => 2 * sobolevNormSq g 0 s (2 * p * (n + 1 - (j + 1)))
        (timeDerivIter T u (j + 1) t)) MeasureTheory.volume 0 T :=
      (continuousOn_const.mul (hcont (j + 1) _)).intervalIntegrable_of_Icc hT.le
    have i2 : IntervalIntegrable (fun t => 2 * C j * ∑ b ∈ Finset.range (j + 1),
        sobolevNormSq g 0 s (2 * p * (n + 1 - b)) (timeDerivIter T u b t)) MeasureTheory.volume 0 T :=
      (continuousOn_const.mul hcS).intervalIntegrable_of_Icc hT.le
    rw [intervalIntegral.integral_add i1 i2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum fun b _ =>
        (hcont b _).intervalIntegrable_of_Icc hT.le] at hint
    exact hint
  -- sum over `j`
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hS : ∀ j ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (j + 1), N b ≤
      ∑ b ∈ Finset.range (n + 1 + 1), N b := fun j hj =>
    Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.mpr (by simp only [Finset.mem_range] at hj; omega))
      fun b _ _ => hNnn b
  have h1 : ∑ j ∈ Finset.range (n + 1), N (j + 1) ≤ ∑ b ∈ Finset.range (n + 1 + 1), N b := by
    rw [Finset.sum_range_succ' _ (n + 1)]
    exact le_add_of_nonneg_right (hNnn 0)
  have h2 : ∑ j ∈ Finset.range (n + 1), 2 * C j * ∑ b ∈ Finset.range (j + 1), N b ≤
      (2 * ∑ j ∈ Finset.range (n + 1), C j) * ∑ b ∈ Finset.range (n + 1 + 1), N b := by
    calc ∑ j ∈ Finset.range (n + 1), 2 * C j * ∑ b ∈ Finset.range (j + 1), N b
        ≤ ∑ j ∈ Finset.range (n + 1), 2 * C j * ∑ b ∈ Finset.range (n + 1 + 1), N b :=
          Finset.sum_le_sum fun j hj =>
            mul_le_mul_of_nonneg_left (hS j hj) (mul_nonneg (by norm_num) (hC0 j))
      _ = (2 * ∑ j ∈ Finset.range (n + 1), C j) * ∑ b ∈ Finset.range (n + 1 + 1), N b := by
          rw [← Finset.sum_mul, ← Finset.mul_sum]
  have hTot : 0 ≤ ∑ b ∈ Finset.range (n + 1 + 1), N b := Finset.sum_nonneg fun b _ => hNnn b
  change 2 * ∑ j ∈ Finset.range (n + 1), N (j + 1) +
      ∑ j ∈ Finset.range (n + 1), 2 * C j * ∑ b ∈ Finset.range (j + 1), N b ≤
    K * ∑ b ∈ Finset.range (n + 1 + 1), N b
  rw [hK]
  nlinarith

end LinearOp

end ShortTime
