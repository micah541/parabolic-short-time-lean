import ShortTime.Linear.Garding

/-!
# Basic properties of the integer Sobolev norms

Paper: Lemma `lem:sobolev-basic`, positive orders.

* `sobolevNormSq_succ`: `‖u‖²_{H^{k+1}} = ‖u‖² + ‖∇u‖²_{H^k}` (part (i)).
* `sobolevNormSq_add_le`: `‖A + B‖²_{H^k} ≤ 2‖A‖²_{H^k} + 2‖B‖²_{H^k}`.
* `exists_sobolevNormSq_opField_le`: a jointly smooth family of coefficient fields `Φ(t)` is bounded
  on `H^k`, uniformly in `t ∈ [0,T]` (part (iv) for `r = 0`, `s ≥ 0`). The proof is by induction on
  `k` with the Leibniz rule `∇(ΦW) = (∇Φ)W + Φ_•(∇W)` (`covGrad_operatorFieldApply_eq`).
-/

noncomputable section

open Bundle Manifold Set MeasureTheory
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Spectral.DeTurck DifferentialGeometry.Geometry.Connection.Realization
open DifferentialGeometry.TensorMultilinear DifferentialGeometry.Analysis.Elliptic
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

/-! ### Smooth families of extended coefficient fields -/

/-- The slot extension `Φ_•` of a jointly smooth family of coefficient fields is jointly smooth. -/
theorem jointlySmoothOn_slotExtend {m n : ℕ} {S : Set ℝ} {A : ℝ → SmoothCcTensor g m n}
    (hA : JointlySmoothOn g m n S A) :
    JointlySmoothOn g (m + 1) (n + 1) S (fun t => slotExtend (I := I) (M := M) g m n (A t)) := by
  apply contMDiffOn_clm_section_of_apply (I := I) (M := M)
    (F₁ := Tensor0SModel (m + 1) ℝ E) (V₁ := fun x : M => Tensor0SSpace (m + 1) I x)
    (F₂ := Tensor0SModel (n + 1) ℝ E) (V₂ := fun x : M => Tensor0SSpace (n + 1) I x)
    (φ := fun p : M × ℝ => slotExtendPointwise (I := I) (M := M) m n p.1
      (show Tensor0SSpace m I p.1 →L[ℝ] Tensor0SSpace n I p.1 from (A p.2).toSection p.1))
    (S := S)
  intro Y
  apply contMDiffOn_uncurry_param (I := I) (M := M)
    (fun p : M × ℝ => (show Tensor0SSpace m I p.1 →L[ℝ] Tensor0SSpace n I p.1 from
      (A p.2).toSection p.1).comp ((tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) m p.1) (Y p.1)))
  apply contMDiffOn_clm_section_of_apply (I := I) (M := M)
    (F₁ := E) (V₁ := fun x : M => TangentSpace I x)
    (F₂ := Tensor0SModel n ℝ E) (V₂ := fun x : M => Tensor0SSpace n I x)
    (φ := fun p : M × ℝ => (show Tensor0SSpace m I p.1 →L[ℝ] Tensor0SSpace n I p.1 from
      (A p.2).toSection p.1).comp ((tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) m p.1) (Y p.1)))
    (S := S)
  intro Z
  have hcurriedY : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel m ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] Tensor0SModel m ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SSpace m I z) x
        (curriedSection (I := I) (M := M) (fun y : M => Y y) x)) :=
    fun x => contMDiffAt_curriedSection_of_contMDiffAt_section (I := I) (M := M)
      (fun y : M => Y y) x (Y.contMDiff x)
  have hinner : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel m ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel m ℝ E)
        (E := fun z : M => Tensor0SSpace m I z) x
        ((curriedSection (I := I) (M := M) (fun y : M => Y y) x) (Z x))) :=
    ContMDiff.clm_bundle_apply (b := id) hcurriedY Z.contMDiff
  have hfst : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞ (Prod.fst : M × ℝ → M) ((Set.univ : Set M) ×ˢ S) :=
    contMDiffOn_fst
  have h := ContMDiffOn.clm_bundle_apply (b := Prod.fst) hA (hinner.comp_contMDiffOn hfst)
  exact h.congr fun p _ => rfl

/-! ### The recursion `H^{k+1} = L² ⊕ ∇H^k` -/

theorem tensorL2Norm_eq_of_heq {a b : ℕ} (h : a = b) {A : SmoothCcTensor g 0 a}
    {B : SmoothCcTensor g 0 b} (hAB : HEq A B) :
    tensorL2Norm (I := I) (M := M) g 0 a A.toFun = tensorL2Norm (I := I) (M := M) g 0 b B.toFun := by
  subst h
  rw [eq_of_heq hAB]

theorem iteratedCovGrad_heq_of_eq {s n n' : ℕ} (h : n = n') (u : SmoothCcTensor g 0 s) :
    HEq (iteratedCovGrad g 0 s n u) (iteratedCovGrad g 0 s n' u) := by
  subst h
  rfl

/-- `‖∇^{i+1}u‖ = ‖∇^i(∇u)‖`. -/
theorem jetNorm_succ_eq (s i : ℕ) (u : SmoothCcTensor g 0 s) :
    jetNorm g s (i + 1) u = jetNorm g (s + 1) i (covGrad (I := I) (M := M) g 0 s u) := by
  refine (tensorL2Norm_eq_of_heq (by omega) ?_)
  exact (iteratedCovGrad_heq_of_eq (by omega) u).trans
    (iteratedCovGrad_comp_heq (g := g) 0 s 1 u i).symm

theorem sobolevNormSq_eq_sum (s k : ℕ) (u : SmoothCcTensor g 0 s) :
    sobolevNormSq g 0 s k u = ∑ i ∈ Finset.range (k + 1), jetNorm g s i u ^ 2 := rfl

/-- **`‖u‖²_{H^{k+1}} = ‖u‖² + ‖∇u‖²_{H^k}`** (`lem:sobolev-basic` (i)). -/
theorem sobolevNormSq_succ (s k : ℕ) (u : SmoothCcTensor g 0 s) :
    sobolevNormSq g 0 s (k + 1) u =
      jetNorm g s 0 u ^ 2 + sobolevNormSq g 0 (s + 1) k (covGrad (I := I) (M := M) g 0 s u) := by
  rw [sobolevNormSq_eq_sum, sobolevNormSq_eq_sum, Finset.sum_range_succ', add_comm]
  simp only [jetNorm_succ_eq]

theorem sobolevNormSq_nonneg (s k : ℕ) (u : SmoothCcTensor g 0 s) : 0 ≤ sobolevNormSq g 0 s k u :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem sobolevNormSq_mono (s : ℕ) {k l : ℕ} (hkl : k ≤ l) (u : SmoothCcTensor g 0 s) :
    sobolevNormSq g 0 s k u ≤ sobolevNormSq g 0 s l u := by
  rw [sobolevNormSq_eq_sum, sobolevNormSq_eq_sum]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.succ_le_succ hkl))
    fun _ _ _ => sq_nonneg _

theorem jetNorm_zero_sq_le (s k : ℕ) (u : SmoothCcTensor g 0 s) :
    jetNorm g s 0 u ^ 2 ≤ sobolevNormSq g 0 s k u := by
  have h := sobolevNormSq_mono s (Nat.zero_le k) u
  rwa [sobolevNormSq_eq_sum, Finset.sum_range_one] at h

theorem sobolevNormSq_covGrad_le (s k : ℕ) (u : SmoothCcTensor g 0 s) :
    sobolevNormSq g 0 (s + 1) k (covGrad (I := I) (M := M) g 0 s u) ≤ sobolevNormSq g 0 s (k + 1) u := by
  rw [sobolevNormSq_succ]
  exact le_add_of_nonneg_left (sq_nonneg _)

/-! ### Sums -/

theorem sq_add_le_two_mul (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (h : c ≤ a + b) (hc : 0 ≤ c) :
    c ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

theorem jetNorm_add_sq_le (s i : ℕ) (A B : SmoothCcTensor g 0 s) :
    jetNorm g s i (A + B) ^ 2 ≤ 2 * jetNorm g s i A ^ 2 + 2 * jetNorm g s i B ^ 2 := by
  refine sq_add_le_two_mul _ _ _ (jetNorm_nonneg g s i A) (jetNorm_nonneg g s i B) ?_
    (jetNorm_nonneg g s i (A + B))
  have e : ∀ X : SmoothCcTensor g 0 (s + i),
      tensorL2Norm (I := I) (M := M) g 0 (s + i) X.toFun = ‖X‖ := fun X => ccNorm_eq_norm X
  simp only [jetNorm, iteratedCovGrad_add, e]
  exact norm_add_le _ _

/-- `‖A + B‖²_{H^k} ≤ 2‖A‖²_{H^k} + 2‖B‖²_{H^k}`. -/
theorem sobolevNormSq_add_le (s k : ℕ) (A B : SmoothCcTensor g 0 s) :
    sobolevNormSq g 0 s k (A + B) ≤ 2 * sobolevNormSq g 0 s k A + 2 * sobolevNormSq g 0 s k B := by
  simp only [sobolevNormSq_eq_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => jetNorm_add_sq_le s i A B

/-! ### Coefficient fields are bounded on `H^k` -/

/-- **Smooth coefficient fields are bounded on `H^k`, uniformly in time** (`lem:sobolev-basic`
(iv), order `0`, `s ≥ 0`). -/
theorem exists_sobolevNormSq_opField_le {T : ℝ} (k : ℕ) :
    ∀ (a b : ℕ) (Φ : ℝ → SmoothCcTensor g a b), JointlySmoothOn g a b (Icc 0 T) Φ →
      ∃ C, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) T, ∀ W : SmoothCcTensor g 0 a,
        sobolevNormSq g 0 b k (operatorFieldApply (I := I) (M := M) g a b (Φ t) W) ≤
          C * sobolevNormSq g 0 a k W := by
  induction k with
  | zero =>
    intro a b Φ hΦ
    obtain ⟨K, hK0, hK⟩ := exists_bound_of_jointlySmoothOn hΦ
    refine ⟨K, hK0, fun t ht W => ?_⟩
    have h := normSq_operatorFieldApply_le g a b (Φ t) (hK t ht) W
    rw [tensorL2Inner_self_eq_sq_norm, tensorL2Inner_self_eq_sq_norm] at h
    simpa [sobolevNormSq_eq_sum, jetNorm] using h
  | succ k ih =>
    intro a b Φ hΦ
    obtain ⟨K, hK0, hK⟩ := exists_bound_of_jointlySmoothOn hΦ
    obtain ⟨C₁, hC₁, h₁⟩ := ih a (b + 1) (fun t => covGrad (I := I) (M := M) g a b (Φ t))
      (Vendor.covGrad_iter_joint (I := I) (M := M) g a b 1 Φ (Icc 0 T) hΦ)
    obtain ⟨C₂, hC₂, h₂⟩ := ih (a + 1) (b + 1) (fun t => slotExtend (I := I) (M := M) g a b (Φ t))
      (jointlySmoothOn_slotExtend hΦ)
    refine ⟨K + 2 * C₁ + 2 * C₂, by positivity, fun t ht W => ?_⟩
    have h0 := normSq_operatorFieldApply_le g a b (Φ t) (hK t ht) W
    rw [tensorL2Inner_self_eq_sq_norm, tensorL2Inner_self_eq_sq_norm] at h0
    rw [sobolevNormSq_succ, covGrad_operatorFieldApply_eq]
    have hsum := sobolevNormSq_add_le (b + 1) k
      (operatorFieldApply (I := I) (M := M) g a (b + 1) (covGrad (I := I) (M := M) g a b (Φ t)) W)
      (operatorFieldApply (I := I) (M := M) g (a + 1) (b + 1) (slotExtend (I := I) (M := M) g a b (Φ t))
        (covGrad (I := I) (M := M) g 0 a W))
    have hW1 := h₁ t ht W
    have hW2 := h₂ t ht (covGrad (I := I) (M := M) g 0 a W)
    have hm1 := sobolevNormSq_mono a (Nat.le_succ k) W
    have hm2 := sobolevNormSq_covGrad_le a k W
    have hm0 := jetNorm_zero_sq_le a (k + 1) W
    have hn1 := sobolevNormSq_nonneg a k W
    have hn2 := sobolevNormSq_nonneg (a + 1) k (covGrad (I := I) (M := M) g 0 a W)
    have h0' : jetNorm g b 0 (operatorFieldApply (I := I) (M := M) g a b (Φ t) W) ^ 2 ≤
        K * jetNorm g a 0 W ^ 2 := h0
    nlinarith [mul_le_mul_of_nonneg_left hm1 hC₁, mul_le_mul_of_nonneg_left hm2 hC₂,
      mul_le_mul_of_nonneg_left hm0 hK0]

/-! ### Homogeneity -/

theorem sobolevNormSq_smul (s k : ℕ) (c : ℝ) (u : SmoothCcTensor g 0 s) :
    sobolevNormSq g 0 s k (c • u) = c ^ 2 * sobolevNormSq g 0 s k u := by
  have e : ∀ i, jetNorm g s i (c • u) = |c| * jetNorm g s i u := by
    intro i
    have e' : ∀ X : SmoothCcTensor g 0 (s + i),
        tensorL2Norm (I := I) (M := M) g 0 (s + i) X.toFun = ‖X‖ := fun X => ccNorm_eq_norm X
    simp only [jetNorm, iteratedCovGrad_smul, e', norm_smul, Real.norm_eq_abs]
  simp only [sobolevNormSq_eq_sum, e, mul_pow, sq_abs, Finset.mul_sum]

theorem sobolevNorm_smul (s k : ℕ) (c : ℝ) (u : SmoothCcTensor g 0 s) :
    sobolevNorm g 0 s k (c • u) = |c| * sobolevNorm g 0 s k u := by
  rw [sobolevNorm, sobolevNorm, sobolevNormSq_smul, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

theorem sobolevNorm_zero (s k : ℕ) : sobolevNorm g 0 s k (0 : SmoothCcTensor g 0 s) = 0 := by
  have h := sobolevNorm_smul (g := g) s k 0 0
  rwa [zero_smul, abs_zero, zero_mul] at h

theorem sobolevNorm_nonneg (s k : ℕ) (u : SmoothCcTensor g 0 s) : 0 ≤ sobolevNorm g 0 s k u :=
  Real.sqrt_nonneg _

theorem jetNorm_zero_le_sobolevNorm (s k : ℕ) (u : SmoothCcTensor g 0 s) :
    jetNorm g s 0 u ≤ sobolevNorm g 0 s k u := by
  rw [sobolevNorm, ← Real.sqrt_sq (jetNorm_nonneg g s 0 u)]
  exact Real.sqrt_le_sqrt (jetNorm_zero_sq_le s k u)

/-! ### Negative norms -/

/-- The set whose supremum is `‖f‖_{H^{-k}}`. -/
theorem negSobolevNorm_bddAbove (s k : ℕ) (f : SmoothCcTensor g 0 s) :
    BddAbove ((fun φ : SmoothCcTensor g 0 s => tensorL2Inner (I := I) (M := M) g 0 s f.toFun φ.toFun) ''
      {φ | sobolevNorm g 0 s k φ ≤ 1}) := by
  refine ⟨jetNorm g s 0 f, ?_⟩
  rintro _ ⟨φ, hφ, rfl⟩
  have hcs := abs_inner_le_norm_mul_norm g 0 s f φ
  have h1 : jetNorm g s 0 φ ≤ 1 := (jetNorm_zero_le_sobolevNorm s k φ).trans hφ
  have hf := jetNorm_nonneg g s 0 f
  calc tensorL2Inner (I := I) (M := M) g 0 s f.toFun φ.toFun
      ≤ jetNorm g s 0 f * jetNorm g s 0 φ := (le_abs_self _).trans hcs
    _ ≤ jetNorm g s 0 f * 1 := mul_le_mul_of_nonneg_left h1 hf
    _ = jetNorm g s 0 f := mul_one _

theorem zero_mem_negSobolevNorm_set (s k : ℕ) (f : SmoothCcTensor g 0 s) :
    (0 : ℝ) ∈ ((fun φ : SmoothCcTensor g 0 s =>
      tensorL2Inner (I := I) (M := M) g 0 s f.toFun φ.toFun) '' {φ | sobolevNorm g 0 s k φ ≤ 1}) := by
  refine ⟨0, ?_, ?_⟩
  · change sobolevNorm g 0 s k 0 ≤ 1
    rw [sobolevNorm_zero]
    exact zero_le_one
  · change tensorL2Inner (I := I) (M := M) g 0 s f.toFun (0 : SmoothCcTensor g 0 s).toFun = 0
    rw [SmoothCcTensor.toFun_zero]
    have h := tensorL2Inner_smul_right (I := I) (M := M) g 0 s 0 f.toFun 0
    rwa [smul_zero, zero_mul] at h

theorem negSobolevNorm_nonneg (s k : ℕ) (f : SmoothCcTensor g 0 s) : 0 ≤ negSobolevNorm g 0 s k f :=
  le_csSup (negSobolevNorm_bddAbove s k f) (zero_mem_negSobolevNorm_set s k f)

/-- **Duality**: `⟨f, φ⟩ ≤ ‖f‖_{H^{-k}} ‖φ‖_{H^k}` (`lem:sobolev-basic` (ii)). -/
theorem inner_le_negSobolevNorm (s k : ℕ) (f φ : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 s f.toFun φ.toFun ≤
      negSobolevNorm g 0 s k f * sobolevNorm g 0 s k φ := by
  set N := sobolevNorm g 0 s k φ with hN
  rcases (sobolevNorm_nonneg s k φ).eq_or_lt with h0 | hpos
  · -- `φ = 0` in `L²`
    have hφ : jetNorm g s 0 φ = 0 :=
      le_antisymm ((jetNorm_zero_le_sobolevNorm s k φ).trans h0.symm.le) (jetNorm_nonneg g s 0 φ)
    have hcs := abs_inner_le_norm_mul_norm g 0 s f φ
    change |_| ≤ jetNorm g s 0 f * jetNorm g s 0 φ at hcs
    rw [hφ, mul_zero] at hcs
    rw [show N = 0 from h0.symm, mul_zero]
    exact (le_abs_self _).trans hcs
  · have hψ : sobolevNorm g 0 s k (N⁻¹ • φ) ≤ 1 := by
      rw [sobolevNorm_smul, abs_of_pos (inv_pos.mpr hpos), inv_mul_cancel₀ hpos.ne']
    have hle := le_csSup (negSobolevNorm_bddAbove s k f) ⟨N⁻¹ • φ, hψ, rfl⟩
    change tensorL2Inner (I := I) (M := M) g 0 s f.toFun (N⁻¹ • φ).toFun ≤ negSobolevNorm g 0 s k f
      at hle
    rw [SmoothCcTensor.toFun_smul, tensorL2Inner_smul_right] at hle
    have := mul_le_mul_of_nonneg_left hle hpos.le
    rwa [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul, mul_comm] at this

theorem abs_inner_le_negSobolevNorm (s k : ℕ) (f φ : SmoothCcTensor g 0 s) :
    |tensorL2Inner (I := I) (M := M) g 0 s f.toFun φ.toFun| ≤
      negSobolevNorm g 0 s k f * sobolevNorm g 0 s k φ := by
  refine abs_le.mpr ⟨?_, inner_le_negSobolevNorm s k f φ⟩
  have h := inner_le_negSobolevNorm s k f ((-1 : ℝ) • φ)
  rw [SmoothCcTensor.toFun_smul, tensorL2Inner_smul_right, sobolevNorm_smul, abs_neg, abs_one,
    one_mul] at h
  linarith

/-- `‖div φ‖_{H^k} ≤ C ‖φ‖_{H^{k+1}}`. -/
theorem exists_sobolevNorm_covDivergence_le (s k : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ φ : SmoothCcTensor g 0 (s + 1),
      sobolevNorm g 0 s k (covDivergence (I := I) (M := M) g s φ) ≤ C * sobolevNorm g 0 (s + 1) (k + 1) φ := by
  obtain ⟨C₀, hC₀, h⟩ := exists_sobolevNormSq_opField_le (g := g) (T := 0) k (s + 2) s
    (fun _ => cometricDoubleTraceField g s)
    (jointlySmoothOn_const g (Icc 0 0) (cometricDoubleTraceField g s))
  refine ⟨Real.sqrt C₀, Real.sqrt_nonneg _, fun φ => ?_⟩
  rw [covDivergence_eq_trace_covGrad, sobolevNorm, sobolevNorm, ← Real.sqrt_mul hC₀]
  refine Real.sqrt_le_sqrt ((h 0 ⟨le_rfl, le_rfl⟩ _).trans ?_)
  exact mul_le_mul_of_nonneg_left (sobolevNormSq_covGrad_le (s + 1) k φ) hC₀

/-- **`‖∇f‖_{H^{-k-1}} ≤ C ‖f‖_{H^{-k}}`** (`lem:sobolev-basic` (iii), negative orders). -/
theorem exists_negSobolevNorm_covGrad_le (s k : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ f : SmoothCcTensor g 0 s,
      negSobolevNorm g 0 (s + 1) (k + 1) (covGrad (I := I) (M := M) g 0 s f) ≤
        C * negSobolevNorm g 0 s k f := by
  obtain ⟨C, hC, hdiv⟩ := exists_sobolevNorm_covDivergence_le (g := g) s k
  refine ⟨C, hC, fun f => ?_⟩
  refine csSup_le ⟨_, zero_mem_negSobolevNorm_set (s + 1) (k + 1) _⟩ ?_
  rintro _ ⟨φ, hφ, rfl⟩
  change tensorL2Inner (I := I) (M := M) g 0 (s + 1) (covGrad (I := I) (M := M) g 0 s f).toFun φ.toFun ≤ _
  rw [tensorL2Inner_covGrad_eq_neg_tensorL2Inner_covDivergence]
  have h1 := abs_inner_le_negSobolevNorm s k f (covDivergence (I := I) (M := M) g s φ)
  have h2 := hdiv φ
  have hn := negSobolevNorm_nonneg s k f
  calc -tensorL2Inner (I := I) (M := M) g 0 s f.toFun (covDivergence (I := I) (M := M) g s φ).toFun
      ≤ negSobolevNorm g 0 s k f * sobolevNorm g 0 s k (covDivergence (I := I) (M := M) g s φ) :=
        (neg_le_abs _).trans h1
    _ ≤ negSobolevNorm g 0 s k f * (C * 1) :=
        mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left hφ hC)) hn
    _ = C * negSobolevNorm g 0 s k f := by ring

end ShortTime
