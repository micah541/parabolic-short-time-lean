import ShortTime.Linear.EnergyEstimate
import ShortTime.Linear.PrincipalIBP
import ShortTime.Linear.GardingOne

/-!
# Differential operators in negative Sobolev norms

Paper: Lemma `lem:sobolev-basic` (iii)–(iv), negative orders.

* `negSobolevNorm_mono`: `‖f‖_{H^{-(m+1)}} ≤ ‖f‖_{H^{-m}}`.
* `exists_negSobolevNorm_opField_covGrad_le`: for a jointly smooth family of coefficient fields
  `A(t)` and `j ≥ m`, `‖A(t)(∇^j W)‖_{H^{-m}} ≤ C ‖W‖_{H^{j-m}}`, uniformly in `t ∈ [0,T]`.
  The proof moves one derivative at a time onto the test function with the integration by parts
  `⟨φ, A(∇V)⟩ = -⟨∇φ, ǍV⟩ - ⟨φ, R_A V⟩` (`inner_apply_covGrad`). No adjoint coefficient fields are
  needed.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
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

theorem sobolevNorm_mono (s : ℕ) {k l : ℕ} (hkl : k ≤ l) (u : SmoothCcTensor g 0 s) :
    sobolevNorm g 0 s k u ≤ sobolevNorm g 0 s l u :=
  Real.sqrt_le_sqrt (sobolevNormSq_mono s hkl u)

/-- `‖f‖_{H^{-(m+1)}} ≤ ‖f‖_{H^{-m}}`. -/
theorem negSobolevNorm_mono (s m : ℕ) (f : SmoothCcTensor g 0 s) :
    negSobolevNorm g 0 s (m + 1) f ≤ negSobolevNorm g 0 s m f := by
  refine csSup_le ⟨_, zero_mem_negSobolevNorm_set s (m + 1) f⟩ ?_
  rintro _ ⟨φ, hφ, rfl⟩
  exact le_csSup (negSobolevNorm_bddAbove s m f)
    ⟨φ, (sobolevNorm_mono s (Nat.le_succ m) φ).trans hφ, rfl⟩

theorem sobolevNorm_covGrad_le (s k : ℕ) (u : SmoothCcTensor g 0 s) :
    sobolevNorm g 0 (s + 1) k (covGrad (I := I) (M := M) g 0 s u) ≤ sobolevNorm g 0 s (k + 1) u :=
  Real.sqrt_le_sqrt (sobolevNormSq_covGrad_le s k u)

/-- **Order-`j` operators lose `m` derivatives into `H^{-m}`.** For `j ≥ m`,
`‖A(t)(∇^j W)‖_{H^{-m}} ≤ C ‖W‖_{H^{j-m}}`, uniformly in `t ∈ [0,T]`. -/
theorem exists_negSobolevNorm_opField_covGrad_le {T : ℝ} (m : ℕ) :
    ∀ (a b j : ℕ), m ≤ j → ∀ A : ℝ → SmoothCcTensor g (a + j) b,
      JointlySmoothOn g (a + j) b (Icc 0 T) A →
      ∃ C, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) T, ∀ W : SmoothCcTensor g 0 a,
        negSobolevNorm g 0 b m (operatorFieldApply (I := I) (M := M) g (a + j) b (A t)
          (iteratedCovGrad g 0 a j W)) ≤ C * sobolevNorm g 0 a (j - m) W := by
  induction m with
  | zero =>
    intro a b j _ A hA
    obtain ⟨K, hK0, hK⟩ := exists_sobolevNormSq_opField_le (g := g) (T := T) 0 (a + j) b A hA
    refine ⟨Real.sqrt K, Real.sqrt_nonneg _, fun t ht W => ?_⟩
    have h1 := negSobolevNorm_le_jetNorm b 0
      (operatorFieldApply (I := I) (M := M) g (a + j) b (A t) (iteratedCovGrad g 0 a j W))
    have h2 := hK t ht (iteratedCovGrad g 0 a j W)
    have hj : sobolevNormSq g 0 (a + j) 0 (iteratedCovGrad g 0 a j W) ≤ sobolevNormSq g 0 a j W := by
      rw [sobolevNormSq_eq_sum, Finset.sum_range_one, sobolevNormSq_eq_sum]
      exact Finset.single_le_sum (f := fun i => jetNorm g a i W ^ 2) (fun _ _ => sq_nonneg _)
        (Finset.mem_range.mpr (Nat.lt_succ_self j))
    have h3 : jetNorm g b 0 (operatorFieldApply (I := I) (M := M) g (a + j) b (A t)
        (iteratedCovGrad g 0 a j W)) ≤ Real.sqrt K * sobolevNorm g 0 a j W := by
      rw [sobolevNorm, ← Real.sqrt_mul hK0, ← Real.sqrt_sq (jetNorm_nonneg g b 0 _)]
      refine Real.sqrt_le_sqrt ?_
      have h0 := jetNorm_zero_sq_le b 0
        (operatorFieldApply (I := I) (M := M) g (a + j) b (A t) (iteratedCovGrad g 0 a j W))
      exact h0.trans (h2.trans (mul_le_mul_of_nonneg_left hj hK0))
    rw [Nat.sub_zero]
    exact h1.trans h3
  | succ m ih =>
    intro a b j hmj A hA
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have hm : m ≤ j' := by omega
    obtain ⟨C₁, hC₁, h₁⟩ := ih a (b + 1) j' hm (fun t => flipField g (a + j') b (A t))
      (jointlySmoothOn_flipField g hA)
    obtain ⟨C₂, hC₂, h₂⟩ := ih a b j' hm (fun t => flipRemainder g (a + j') b (A t))
      (jointlySmoothOn_flipRemainder hA)
    refine ⟨C₁ + C₂, by positivity, fun t ht W => ?_⟩
    rw [show j' + 1 - (m + 1) = j' - m by omega]
    set V := iteratedCovGrad g 0 a j' W
    refine csSup_le ⟨_, zero_mem_negSobolevNorm_set b (m + 1) _⟩ ?_
    rintro _ ⟨φ, hφ, rfl⟩
    change tensorL2Inner (I := I) (M := M) g 0 b
      (operatorFieldApply (I := I) (M := M) g (a + j' + 1) b (A t)
        (covGrad (I := I) (M := M) g 0 (a + j') V)).toFun φ.toFun ≤ _
    rw [tensorL2Inner_symm, inner_apply_covGrad]
    have hX := abs_inner_le_negSobolevNorm (b + 1) m
      (operatorFieldApply (I := I) (M := M) g (a + j') (b + 1) (flipField g (a + j') b (A t)) V)
      (covGrad (I := I) (M := M) g 0 b φ)
    rw [tensorL2Inner_symm] at hX
    have hY := abs_inner_le_negSobolevNorm b (m + 1)
      (operatorFieldApply (I := I) (M := M) g (a + j') b (flipRemainder g (a + j') b (A t)) V) φ
    rw [tensorL2Inner_symm] at hY
    have hφ' : sobolevNorm g 0 (b + 1) m (covGrad (I := I) (M := M) g 0 b φ) ≤ 1 :=
      (sobolevNorm_covGrad_le b m φ).trans hφ
    have hN1 := h₁ t ht W
    have hN2 := (negSobolevNorm_mono b m _).trans (h₂ t ht W)
    have hn1 := negSobolevNorm_nonneg (b + 1) m
      (operatorFieldApply (I := I) (M := M) g (a + j') (b + 1) (flipField g (a + j') b (A t)) V)
    have hn2 := negSobolevNorm_nonneg b (m + 1)
      (operatorFieldApply (I := I) (M := M) g (a + j') b (flipRemainder g (a + j') b (A t)) V)
    have hX' := hX.trans (mul_le_mul_of_nonneg_left hφ' hn1)
    have hY' := hY.trans (mul_le_mul_of_nonneg_left hφ hn2)
    have hW := sobolevNorm_nonneg a (j' - m) W
    rw [mul_one] at hX' hY'
    nlinarith [neg_le_abs (tensorL2Inner (I := I) (M := M) g 0 (b + 1)
        (covGrad (I := I) (M := M) g 0 b φ).toFun
        (operatorFieldApply (I := I) (M := M) g (a + j') (b + 1) (flipField g (a + j') b (A t)) V).toFun),
      neg_le_abs (tensorL2Inner (I := I) (M := M) g 0 b φ.toFun
        (operatorFieldApply (I := I) (M := M) g (a + j') b (flipRemainder g (a + j') b (A t)) V).toFun)]

end ShortTime
