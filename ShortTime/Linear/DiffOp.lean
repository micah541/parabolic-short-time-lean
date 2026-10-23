import ShortTime.Linear.PermField

/-!
# Differential operators with smooth time-dependent coefficients

`IsDiffOp S r D` says that `D t W = ∑_{c ≤ r} F_c(t) (∇^c W)` for operator fields `F_c(t)` that are
jointly smooth in `(x, t)` on `M × S`. This class is closed under sums, composition with
coefficient fields, slot relabellings, `∇` (Leibniz rule, `IsDiffOp.grad`) and precomposition
with `∇` (`IsDiffOp.comp_grad`). Conversely, every operator of order `r` is a zeroth-order term
plus an operator of order `r - 1` applied to `∇W` (`IsDiffOp.split`).

These are used to differentiate a linear operator (`lem:commute`).
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

/-- `D` is a differential operator `T⁰_a → T⁰_b` of order `≤ r` whose coefficients are jointly
smooth on `M × S`: `D t W = ∑_{c ≤ r} F_c(t) (∇^c W)`. -/
def IsDiffOp (S : Set ℝ) {a b : ℕ} (r : ℕ)
    (D : ℝ → SmoothCcTensor g 0 a → SmoothCcTensor g 0 b) : Prop :=
  ∃ F : ∀ c : ℕ, ℝ → SmoothCcTensor g (a + c) b,
    (∀ c, JointlySmoothOn g (a + c) b S (F c)) ∧
    ∀ t W, D t W = ∑ c ∈ Finset.range (r + 1),
      operatorFieldApply (I := I) (M := M) g (a + c) b (F c t) (iteratedCovGrad g 0 a c W)

namespace IsDiffOp

variable {S : Set ℝ} {a b : ℕ}

theorem mono {r r' : ℕ} {D : ℝ → SmoothCcTensor g 0 a → SmoothCcTensor g 0 b}
    (hD : IsDiffOp S r D) (hr : r ≤ r') : IsDiffOp S r' D := by
  classical
  obtain ⟨F, hF, hDF⟩ := hD
  refine ⟨fun c t => if c ≤ r then F c t else 0, fun c => ?_, fun t W => ?_⟩
  · by_cases hc : c ≤ r
    · simpa only [hc, if_true] using hF c
    · simpa only [hc, if_false] using jointlySmoothOn_const g S (0 : SmoothCcTensor g (a + c) b)
  · rw [hDF, ← Finset.sum_subset (Finset.range_subset_range.mpr (by omega : r + 1 ≤ r' + 1))
      (fun c _ hc => ?_)]
    · refine Finset.sum_congr rfl fun c hc => ?_
      have hc' : c ≤ r := by simp only [Finset.mem_range] at hc; omega
      simp only [hc', if_true]
    · have hc' : ¬ c ≤ r := by simp only [Finset.mem_range] at hc; omega
      simp only [hc', if_false, operatorFieldApplication_zero_left]

theorem congr' {r : ℕ} {D D' : ℝ → SmoothCcTensor g 0 a → SmoothCcTensor g 0 b}
    (hD : IsDiffOp S r D) (h : ∀ t W, D t W = D' t W) : IsDiffOp S r D' := by
  obtain ⟨F, hF, hDF⟩ := hD
  exact ⟨F, hF, fun t W => (h t W).symm.trans (hDF t W)⟩

theorem zero (r : ℕ) : IsDiffOp S r (fun _ _ => (0 : SmoothCcTensor g 0 b)) (a := a) :=
  ⟨fun _ _ => 0, fun c => jointlySmoothOn_const g S 0, fun t W => by
    simp only [operatorFieldApplication_zero_left, Finset.sum_const_zero]⟩

theorem add {r : ℕ} {D D' : ℝ → SmoothCcTensor g 0 a → SmoothCcTensor g 0 b}
    (hD : IsDiffOp S r D) (hD' : IsDiffOp S r D') : IsDiffOp S r (fun t W => D t W + D' t W) := by
  obtain ⟨F, hF, hDF⟩ := hD
  obtain ⟨F', hF', hDF'⟩ := hD'
  refine ⟨fun c t => F c t + F' c t, fun c => jointlySmoothOn_add (hF c) (hF' c), fun t W => ?_⟩
  simp only [hDF, hDF', operatorFieldApplication_add_left, Finset.sum_add_distrib]

theorem smul {r : ℕ} {D : ℝ → SmoothCcTensor g 0 a → SmoothCcTensor g 0 b}
    (hD : IsDiffOp S r D) (k : ℝ) : IsDiffOp S r (fun t W => k • D t W) := by
  obtain ⟨F, hF, hDF⟩ := hD
  refine ⟨fun c t => k • F c t, fun c => jointlySmoothOn_smul k (hF c), fun t W => ?_⟩
  simp only [hDF, operatorFieldApplication_smul_left, Finset.smul_sum]

theorem neg {r : ℕ} {D : ℝ → SmoothCcTensor g 0 a → SmoothCcTensor g 0 b}
    (hD : IsDiffOp S r D) : IsDiffOp S r (fun t W => -D t W) := by
  simpa only [neg_one_smul] using hD.smul (-1)

theorem sub {r : ℕ} {D D' : ℝ → SmoothCcTensor g 0 a → SmoothCcTensor g 0 b}
    (hD : IsDiffOp S r D) (hD' : IsDiffOp S r D') : IsDiffOp S r (fun t W => D t W - D' t W) := by
  simpa only [sub_eq_add_neg] using hD.add hD'.neg

theorem sum {ι : Type*} (s : Finset ι) {r : ℕ}
    {D : ι → ℝ → SmoothCcTensor g 0 a → SmoothCcTensor g 0 b}
    (hD : ∀ i ∈ s, IsDiffOp S r (D i)) : IsDiffOp S r (fun t W => ∑ i ∈ s, D i t W) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using zero (S := S) (a := a) (b := b) r
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hD i (Finset.mem_insert_self i s)).add (ih fun j hj => hD j (Finset.mem_insert_of_mem hj))

end IsDiffOp

/-! ### Auxiliary identities -/

theorem operatorFieldApply_sum_right {a b : ℕ} {ι : Type*} (s : Finset ι) (Φ : SmoothCcTensor g a b)
    (W : ι → SmoothCcTensor g 0 a) :
    operatorFieldApply (I := I) (M := M) g a b Φ (∑ i ∈ s, W i) =
      ∑ i ∈ s, operatorFieldApply (I := I) (M := M) g a b Φ (W i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, operatorFieldApplication_zero_right]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, operatorFieldApplication_add_right, ih]

/-- Relabelling the source rank of a coefficient along `a = a'`. -/
theorem operatorFieldApply_castSource {a a' b : ℕ} (h : a = a') (F : SmoothCcTensor g a b)
    {X : SmoothCcTensor g 0 a} {X' : SmoothCcTensor g 0 a'} (hX : HEq X X') :
    operatorFieldApply (I := I) (M := M) g a' b (castCcTensorSourceRank g b h F) X' =
      operatorFieldApply (I := I) (M := M) g a b F X := by
  subst h
  rw [eq_of_heq hX]
  rfl

theorem jointlySmoothOn_castSource {S : Set ℝ} {a a' b : ℕ} (h : a = a')
    {F : ℝ → SmoothCcTensor g a b} (hF : JointlySmoothOn g a b S F) :
    JointlySmoothOn g a' b S (fun t => castCcTensorSourceRank g b h (F t)) := by
  subst h
  exact hF

theorem jointlySmoothOn_covGrad {S : Set ℝ} {a b : ℕ} {F : ℝ → SmoothCcTensor g a b}
    (hF : JointlySmoothOn g a b S F) :
    JointlySmoothOn g a (b + 1) S (fun t => covGrad (I := I) (M := M) g a b (F t)) :=
  Vendor.covGrad_step_jointContMDiffOn g a b F S hF

namespace IsDiffOp

variable {S : Set ℝ} {a b : ℕ}

/-- A coefficient field is an operator of order `0`. -/
theorem field {G : ℝ → SmoothCcTensor g a b} (hG : JointlySmoothOn g a b S G) :
    IsDiffOp S 0 (fun t W => operatorFieldApply (I := I) (M := M) g a b (G t) W) := by
  refine ⟨fun c => match c with
    | 0 => G
    | _ + 1 => fun _ => 0, fun c => ?_, fun t W => ?_⟩
  · cases c with
    | zero => exact hG
    | succ c => exact jointlySmoothOn_const g S 0
  · rw [Finset.sum_range_one, iteratedCovGrad_zero]
    rfl

/-- Composition with a coefficient field. -/
theorem comp_field {r b' : ℕ} {D : ℝ → SmoothCcTensor g 0 a → SmoothCcTensor g 0 b}
    (hD : IsDiffOp S r D) {G : ℝ → SmoothCcTensor g b b'} (hG : JointlySmoothOn g b b' S G) :
    IsDiffOp S r (fun t W => operatorFieldApply (I := I) (M := M) g b b' (G t) (D t W)) := by
  obtain ⟨F, hF, hDF⟩ := hD
  refine ⟨fun c t => ccOperatorFieldComp (I := I) (M := M) g (a + c) b b' (G t) (F c t),
    fun c => jointlySmoothOn_comp g hG (hF c), fun t W => ?_⟩
  dsimp only
  rw [hDF, operatorFieldApply_sum_right]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [operatorFieldApply_assoc]

/-- Composition with a slot permutation. -/
theorem perm {r : ℕ} {D : ℝ → SmoothCcTensor g 0 a → SmoothCcTensor g 0 b}
    (hD : IsDiffOp S r D) (σ : Equiv.Perm (Fin b)) :
    IsDiffOp S r (fun t W => domDomCongrSection (I := I) g σ (D t W)) := by
  simpa only [operatorFieldApply_permField] using
    hD.comp_field (jointlySmoothOn_const g S (permField g σ))

/-- Relabelling the target rank along `b = b'`. -/
theorem cast_target {r b' : ℕ} (h : b = b') {D : ℝ → SmoothCcTensor g 0 a → SmoothCcTensor g 0 b}
    (hD : IsDiffOp S r D) :
    IsDiffOp S r (fun t W => castCcTensorRank g 0 h (D t W)) := by
  subst h
  exact hD

/-- **Leibniz rule**: `∇ ∘ D` is an operator of order `r + 1`. -/
theorem grad {r : ℕ} {D : ℝ → SmoothCcTensor g 0 a → SmoothCcTensor g 0 b}
    (hD : IsDiffOp S r D) :
    IsDiffOp S (r + 1) (fun t W => covGrad (I := I) (M := M) g 0 b (D t W)) := by
  obtain ⟨F, hF, hDF⟩ := hD
  have hA : IsDiffOp S r (fun t W => ∑ c ∈ Finset.range (r + 1),
      operatorFieldApply (I := I) (M := M) g (a + c) (b + 1)
        (covGrad (I := I) (M := M) g (a + c) b (F c t)) (iteratedCovGrad g 0 a c W)) :=
    ⟨fun c t => covGrad (I := I) (M := M) g (a + c) b (F c t),
      fun c => jointlySmoothOn_covGrad (hF c), fun t W => rfl⟩
  have hB : IsDiffOp S (r + 1) (fun t W => ∑ c ∈ Finset.range (r + 1),
      operatorFieldApply (I := I) (M := M) g (a + c + 1) (b + 1)
        (slotExtend (I := I) (M := M) g (a + c) b (F c t)) (iteratedCovGrad g 0 a (c + 1) W)) := by
    refine ⟨fun c => match c with
      | 0 => fun _ => 0
      | c + 1 => fun t => slotExtend (I := I) (M := M) g (a + c) b (F c t), fun c => ?_,
      fun t W => ?_⟩
    · cases c with
      | zero => exact jointlySmoothOn_const g S 0
      | succ c => exact jointlySmoothOn_slotExtend (hF c)
    · rw [Finset.sum_range_succ' _ (r + 1)]
      simp only [operatorFieldApplication_zero_left, add_zero]
      rfl
  have key : (fun t W => covGrad (I := I) (M := M) g 0 b (D t W)) = fun t W =>
      (∑ c ∈ Finset.range (r + 1),
        operatorFieldApply (I := I) (M := M) g (a + c) (b + 1)
          (covGrad (I := I) (M := M) g (a + c) b (F c t)) (iteratedCovGrad g 0 a c W)) +
      ∑ c ∈ Finset.range (r + 1),
        operatorFieldApply (I := I) (M := M) g (a + c + 1) (b + 1)
          (slotExtend (I := I) (M := M) g (a + c) b (F c t)) (iteratedCovGrad g 0 a (c + 1) W) := by
    funext t W
    rw [hDF, covGrad_finset_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [covGrad_operatorFieldApply_eq, iteratedCovGrad_succ]
  rw [key]
  exact (hA.mono (Nat.le_succ r)).add hB

/-- Precomposition with `∇`: `W ↦ D(∇W)` is an operator of order `r + 1`. -/
theorem comp_grad {r : ℕ} {D : ℝ → SmoothCcTensor g 0 (a + 1) → SmoothCcTensor g 0 b}
    (hD : IsDiffOp S r D) :
    IsDiffOp S (r + 1) (fun t W => D t (covGrad (I := I) (M := M) g 0 a W)) := by
  obtain ⟨F, hF, hDF⟩ := hD
  refine ⟨fun c => match c with
    | 0 => fun _ => 0
    | c + 1 => fun t => castCcTensorSourceRank g b (by omega : a + 1 + c = a + (c + 1)) (F c t),
    fun c => ?_, fun t W => ?_⟩
  · cases c with
    | zero => exact jointlySmoothOn_const g S 0
    | succ c => exact jointlySmoothOn_castSource _ (hF c)
  · dsimp only
    rw [hDF, Finset.sum_range_succ' _ (r + 1)]
    simp only [operatorFieldApplication_zero_left, add_zero]
    refine Finset.sum_congr rfl fun c _ => ?_
    exact (operatorFieldApply_castSource _ _ (iteratedCovGrad_covGrad_comm_heq g 0 a c W)).symm

/-- **Splitting off one derivative**: an operator of order `r` is a zeroth-order term plus an
operator of order `r - 1` applied to `∇W`. -/
theorem split {r : ℕ} {D : ℝ → SmoothCcTensor g 0 a → SmoothCcTensor g 0 b}
    (hD : IsDiffOp S r D) :
    ∃ S₀ : ℝ → SmoothCcTensor g a b, JointlySmoothOn g a b S S₀ ∧
      ∃ F' : ∀ c : ℕ, ℝ → SmoothCcTensor g (a + 1 + c) b,
        (∀ c, JointlySmoothOn g (a + 1 + c) b S (F' c)) ∧
        ∀ t W, D t W = operatorFieldApply (I := I) (M := M) g a b (S₀ t) W +
          ∑ c ∈ Finset.range r, operatorFieldApply (I := I) (M := M) g (a + 1 + c) b (F' c t)
            (iteratedCovGrad g 0 (a + 1) c (covGrad (I := I) (M := M) g 0 a W)) := by
  obtain ⟨F, hF, hDF⟩ := hD
  refine ⟨F 0, hF 0, fun c t => castCcTensorSourceRank g b (by omega : a + (c + 1) = a + 1 + c)
    (F (c + 1) t), fun c => jointlySmoothOn_castSource _ (hF (c + 1)), fun t W => ?_⟩
  rw [hDF, Finset.sum_range_succ', add_comm]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  exact (operatorFieldApply_castSource _ _ (iteratedCovGrad_covGrad_comm_heq g 0 a c W).symm).symm

/-- Iterated Leibniz rule: `∇^k ∘ D` is an operator of order `r + k`. -/
theorem iterGrad {r : ℕ} {D : ℝ → SmoothCcTensor g 0 a → SmoothCcTensor g 0 b}
    (hD : IsDiffOp S r D) :
    ∀ k : ℕ, IsDiffOp S (r + k) (fun t W => iteratedCovGrad g 0 b k (D t W))
  | 0 => hD
  | k + 1 => (iterGrad hD k).grad

/-- A coefficient field applied to `∇^j W` is an operator of order `j`. -/
theorem field_grad : ∀ (j : ℕ) {a : ℕ} {G : ℝ → SmoothCcTensor g (a + j) b},
    JointlySmoothOn g (a + j) b S G →
    IsDiffOp S j (fun t W => operatorFieldApply (I := I) (M := M) g (a + j) b (G t)
      (iteratedCovGrad g 0 a j W))
  | 0, a, G, hG => field (S := S) hG
  | j + 1, a, G, hG => by
    have h := (field_grad j (a := a + 1)
      (jointlySmoothOn_castSource (by omega : a + (j + 1) = a + 1 + j) hG)).comp_grad
    have key : (fun t W => operatorFieldApply (I := I) (M := M) g (a + 1 + j) b
        (castCcTensorSourceRank g b (by omega : a + (j + 1) = a + 1 + j) (G t))
        (iteratedCovGrad g 0 (a + 1) j (covGrad (I := I) (M := M) g 0 a W))) =
        fun t W => operatorFieldApply (I := I) (M := M) g (a + (j + 1)) b (G t)
          (iteratedCovGrad g 0 a (j + 1) W) :=
      funext fun t => funext fun W =>
        operatorFieldApply_castSource _ _ (iteratedCovGrad_covGrad_comm_heq g 0 a j W).symm
    rw [key] at h
    exact h

end IsDiffOp

end ShortTime
