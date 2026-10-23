import ShortTime.Linear.Flip
import ShortTime.Linear.Divergence

/-!
# One integration by parts across a coefficient (`lem:ibp`)

For an operator field `A : T⁰_{m+1} → T⁰_n` and covariant tensor fields `T ∈ Γ(T⁰_n)`,
`W ∈ Γ(T⁰_m)`,

  `⟨T, A(∇W)⟩ = -⟨∇T, Ǎ W⟩ - ⟨T, R_A W⟩`,

where `Ǎ` is the flip of `A` (`flipField`) and `R_A = tr₁₂ ∘ ∇Ǎ` (`flipRemainder`) has order zero.
Iterating this moves all derivatives off the top-order term. For `p = 1`, one step already gives
the Gårding identity `⟨u, P(∇²u)⟩ = -⟨∇u, P̌ ∇u⟩ - ⟨u, R_P ∇u⟩`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Spectral DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open scoped Manifold ContDiff BigOperators

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

variable (g : SmoothRiemannianMetric I M)

theorem tensorL2Inner_sub_right_cc (r s : ℕ) (S A B : SmoothCcTensor g r s) :
    tensorL2Inner (I := I) (M := M) g r s S.toFun (A - B).toFun =
      tensorL2Inner (I := I) (M := M) g r s S.toFun A.toFun -
        tensorL2Inner (I := I) (M := M) g r s S.toFun B.toFun := by
  have h : (A - B).toFun = A.toFun + ((-1 : ℝ) • B).toFun := by
    rw [SmoothCcTensor.toFun_sub, SmoothCcTensor.toFun_smul, neg_one_smul, sub_eq_add_neg]
  rw [h, tensorL2Inner_add_right (I := I) (M := M) g r s _ _ _
    (SmoothCcTensor.integrable_inner_cross S A) (SmoothCcTensor.integrable_inner_cross S _),
    SmoothCcTensor.toFun_smul, tensorL2Inner_smul_right]
  ring

/-- `⟨T, tr₁₂ ∇V⟩ = -⟨∇T, V⟩`. -/
theorem inner_trace_covGrad (s : ℕ) (T : SmoothCcTensor g 0 s) (V : SmoothCcTensor g 0 (s + 1)) :
    tensorL2Inner (I := I) (M := M) g 0 s T.toFun
        (operatorFieldApply (I := I) (M := M) g (s + 2) s (cometricDoubleTraceField (I := I) g s)
          (covGrad (I := I) (M := M) g 0 (s + 1) V)).toFun =
      - tensorL2Inner (I := I) (M := M) g 0 (s + 1) (covGrad (I := I) (M := M) g 0 s T).toFun
          V.toFun := by
  rw [← covDivergence_eq_trace_covGrad, tensorL2Inner_covGrad_eq_neg_tensorL2Inner_covDivergence,
    neg_neg]

/-- The zeroth-order coefficient `R_A = tr₁₂ ∘ ∇Ǎ` produced by one integration by parts. -/
def flipRemainder (m n : ℕ) (A : SmoothCcTensor g (m + 1) n) : SmoothCcTensor g m n :=
  ccOperatorFieldComp (I := I) (M := M) g m (n + 2) n (cometricDoubleTraceField (I := I) g n)
    (covGrad (I := I) (M := M) g m (n + 1) (flipField g m n A))

/-- `tr₁₂ ∘ slotExtend Ǎ = A` as operator fields. -/
theorem trace_comp_slotExtend_flipField (m n : ℕ) (A : SmoothCcTensor g (m + 1) n) :
    ccOperatorFieldComp (I := I) (M := M) g (m + 1) (n + 2) n
        (cometricDoubleTraceField (I := I) g n)
        (slotExtend (I := I) (M := M) g m (n + 1) (flipField g m n A)) = A := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [operatorFieldComposition_toSection]
  exact cometricDoubleTraceFib_comp_slotExtend_flipFib g m n x _

/-- `A(∇W) = tr₁₂ ∇(Ǎ W) - R_A W`. -/
theorem apply_covGrad_eq (m n : ℕ) (A : SmoothCcTensor g (m + 1) n) (W : SmoothCcTensor g 0 m) :
    operatorFieldApply (I := I) (M := M) g (m + 1) n A (covGrad (I := I) (M := M) g 0 m W) =
      operatorFieldApply (I := I) (M := M) g (n + 2) n (cometricDoubleTraceField (I := I) g n)
          (covGrad (I := I) (M := M) g 0 (n + 1)
            (operatorFieldApply (I := I) (M := M) g m (n + 1) (flipField g m n A) W)) -
        operatorFieldApply (I := I) (M := M) g m n (flipRemainder g m n A) W := by
  rw [covGrad_operatorFieldApply_eq, operatorFieldApplication_add_right, operatorFieldApply_assoc,
    operatorFieldApply_assoc, trace_comp_slotExtend_flipField, flipRemainder]
  abel

/-- **One integration by parts.** `⟨T, A(∇W)⟩ = -⟨∇T, Ǎ W⟩ - ⟨T, R_A W⟩`. -/
theorem inner_apply_covGrad (m n : ℕ) (A : SmoothCcTensor g (m + 1) n)
    (T : SmoothCcTensor g 0 n) (W : SmoothCcTensor g 0 m) :
    tensorL2Inner (I := I) (M := M) g 0 n T.toFun
        (operatorFieldApply (I := I) (M := M) g (m + 1) n A
          (covGrad (I := I) (M := M) g 0 m W)).toFun =
      - tensorL2Inner (I := I) (M := M) g 0 (n + 1) (covGrad (I := I) (M := M) g 0 n T).toFun
          (operatorFieldApply (I := I) (M := M) g m (n + 1) (flipField g m n A) W).toFun
      - tensorL2Inner (I := I) (M := M) g 0 n T.toFun
          (operatorFieldApply (I := I) (M := M) g m n (flipRemainder g m n A) W).toFun := by
  rw [apply_covGrad_eq, tensorL2Inner_sub_right_cc, inner_trace_covGrad]

end ShortTime
