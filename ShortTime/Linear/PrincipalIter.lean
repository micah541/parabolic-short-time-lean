import ShortTime.Linear.Balance

/-!
# Integrating the principal term by parts `p` times (`lem:ibp`)

For `P : T⁰_{s+2p} → T⁰_s`, the iterated flips `P^{(j)} : T⁰_{s+i} → T⁰_{s+j}` (`i + j = 2p`) satisfy

  `⟨u, P ∇^{2p} u⟩ = (-1)^j ⟨∇^j u, P^{(j)} ∇^i u⟩ + E_j(u)`,   `|E_j(u)| ≤ C N_p(u) N_{p-1}(u)`.

For `j = p` this is the main term of Gårding's inequality. Each step is one integration by parts
(`inner_apply_covGrad`); the remainder it produces is a balanced pairing (`exists_bound_pairing`).
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set MeasureTheory
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Spectral DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Elliptic
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

/-- Transport an operator field along an equality of input ranks. -/
def castIn {a a' b : ℕ} (h : a = a') (P : SmoothCcTensor g a b) : SmoothCcTensor g a' b := by
  subst h
  exact P

omit [CompleteSpace E] in
@[simp] theorem castIn_rfl {a b : ℕ} (P : SmoothCcTensor g a b) : castIn g rfl P = P := rfl

omit [CompleteSpace E] in
theorem jointlySmoothOn_castIn {a a' b : ℕ} (h : a = a') {S : Set ℝ}
    {P : ℝ → SmoothCcTensor g a b} (hP : JointlySmoothOn g a b S P) :
    JointlySmoothOn g a' b S (fun t => castIn g h (P t)) := by
  subst h
  exact hP

/-- The iterated flips of `P : T⁰_{s+2p} → T⁰_s`: `flipIter j i h P : T⁰_{s+i} → T⁰_{s+j}` for
`i + j = 2p`. The step is `flipIter (j+1) i = flip ∘ flipIter j (i+1)`; only the base case needs a
transport of ranks. -/
def flipIter (s p : ℕ) : ∀ (j i : ℕ), i + j = 2 * p →
    SmoothCcTensor g (s + 2 * p) s → SmoothCcTensor g (s + i) (s + j)
  | 0, i, h, P => castIn g (show s + 2 * p = s + i by omega) P
  | j + 1, i, h, P => flipField g (s + i) (s + j) (flipIter s p j (i + 1) (by omega) P)

theorem flipIter_succ (s p j i : ℕ) (h : i + (j + 1) = 2 * p) (P : SmoothCcTensor g (s + 2 * p) s) :
    flipIter g s p (j + 1) i h P =
      flipField g (s + i) (s + j) (flipIter g s p j (i + 1) (by omega) P) := rfl

theorem jointlySmoothOn_flipIter (s p : ℕ) {T : ℝ} {P : ℝ → SmoothCcTensor g (s + 2 * p) s}
    (hP : JointlySmoothOn g (s + 2 * p) s (Icc 0 T) P) :
    ∀ (j i : ℕ) (h : i + j = 2 * p),
      JointlySmoothOn g (s + i) (s + j) (Icc 0 T) (fun t => flipIter g s p j i h (P t))
  | 0, i, h => jointlySmoothOn_castIn g _ hP
  | j + 1, i, h => jointlySmoothOn_flipField g (jointlySmoothOn_flipIter s p hP j (i + 1) (by omega))

variable {g}

/-- **The principal term after `j` integrations by parts.** -/
theorem principal_iter {s p : ℕ} {T : ℝ} {P : ℝ → SmoothCcTensor g (s + 2 * p) s}
    (hP : JointlySmoothOn g (s + 2 * p) s (Icc 0 T) P) :
    ∀ j, j ≤ p → ∀ i (h : i + j = 2 * p),
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) T, ∀ u : SmoothCcTensor g 0 s,
        |tensorL2Inner (I := I) (M := M) g 0 s u.toFun
            (operatorFieldApply (I := I) (M := M) g (s + 2 * p) s (P t)
              (iteratedCovGrad g 0 s (2 * p) u)).toFun -
          (-1) ^ j * tensorL2Inner (I := I) (M := M) g 0 (s + j)
            (iteratedCovGrad g 0 s j u).toFun
            (operatorFieldApply (I := I) (M := M) g (s + i) (s + j)
              (flipIter g s p j i h (P t)) (iteratedCovGrad g 0 s i u)).toFun| ≤
          C * jetSum g s p u * jetSum g s (p - 1) u := by
  intro j
  induction j with
  | zero =>
    intro _ i h
    obtain rfl : i = 2 * p := by omega
    refine ⟨0, le_rfl, fun t _ u => ?_⟩
    have hP := mul_nonneg (jetSum_nonneg s p u) (jetSum_nonneg s (p - 1) u)
    simp only [pow_zero, one_mul, zero_mul]
    rw [show flipIter g s p 0 (2 * p) h (P t) = P t from rfl]
    simp
  | succ j ih =>
    intro hj i h
    obtain ⟨C, hC0, hC⟩ := ih (by omega) (i + 1) (by omega)
    obtain ⟨CR, hCR0, hCR⟩ := exists_bound_pairing (g := g) (s := s) (p := p) (T := T) i j
      (by omega) (by omega)
      (fun t => flipRemainder g (s + i) (s + j) (flipIter g s p j (i + 1) (by omega) (P t)))
      (jointlySmoothOn_flipRemainder (jointlySmoothOn_flipIter g s p hP j (i + 1) (by omega)))
    refine ⟨C + CR, by positivity, fun t ht u => ?_⟩
    have hibp := inner_apply_covGrad g (s + i) (s + j)
      (flipIter g s p j (i + 1) (by omega) (P t)) (iteratedCovGrad g 0 s j u)
      (iteratedCovGrad g 0 s i u)
    have e : tensorL2Inner (I := I) (M := M) g 0 (s + j) (iteratedCovGrad g 0 s j u).toFun
        (operatorFieldApply (I := I) (M := M) g (s + (i + 1)) (s + j)
          (flipIter g s p j (i + 1) (by omega) (P t)) (iteratedCovGrad g 0 s (i + 1) u)).toFun =
        - tensorL2Inner (I := I) (M := M) g 0 (s + (j + 1))
            (iteratedCovGrad g 0 s (j + 1) u).toFun
            (operatorFieldApply (I := I) (M := M) g (s + i) (s + (j + 1))
              (flipIter g s p (j + 1) i h (P t)) (iteratedCovGrad g 0 s i u)).toFun
          - tensorL2Inner (I := I) (M := M) g 0 (s + j) (iteratedCovGrad g 0 s j u).toFun
            (operatorFieldApply (I := I) (M := M) g (s + i) (s + j)
              (flipRemainder g (s + i) (s + j) (flipIter g s p j (i + 1) (by omega) (P t)))
              (iteratedCovGrad g 0 s i u)).toFun :=
      hibp
    have h1 := hC t ht u
    have h2 := hCR t ht u
    rw [e] at h1
    have hsign : ((-1 : ℝ) ^ (j + 1)) = - (-1) ^ j := by ring
    rw [hsign]
    have habs : |((-1 : ℝ) ^ j)| = 1 := by simp
    calc _ = |(tensorL2Inner (I := I) (M := M) g 0 s u.toFun
            (operatorFieldApply (I := I) (M := M) g (s + 2 * p) s (P t)
              (iteratedCovGrad g 0 s (2 * p) u)).toFun -
          (-1) ^ j * (- tensorL2Inner (I := I) (M := M) g 0 (s + (j + 1))
            (iteratedCovGrad g 0 s (j + 1) u).toFun
            (operatorFieldApply (I := I) (M := M) g (s + i) (s + (j + 1))
              (flipIter g s p (j + 1) i h (P t)) (iteratedCovGrad g 0 s i u)).toFun
          - tensorL2Inner (I := I) (M := M) g 0 (s + j) (iteratedCovGrad g 0 s j u).toFun
            (operatorFieldApply (I := I) (M := M) g (s + i) (s + j)
              (flipRemainder g (s + i) (s + j) (flipIter g s p j (i + 1) (by omega) (P t)))
              (iteratedCovGrad g 0 s i u)).toFun)) -
          (-1) ^ j * tensorL2Inner (I := I) (M := M) g 0 (s + j)
            (iteratedCovGrad g 0 s j u).toFun
            (operatorFieldApply (I := I) (M := M) g (s + i) (s + j)
              (flipRemainder g (s + i) (s + j) (flipIter g s p j (i + 1) (by omega) (P t)))
              (iteratedCovGrad g 0 s i u)).toFun| := by
          congr 1
          ring
      _ ≤ _ + |(-1) ^ j * tensorL2Inner (I := I) (M := M) g 0 (s + j)
            (iteratedCovGrad g 0 s j u).toFun
            (operatorFieldApply (I := I) (M := M) g (s + i) (s + j)
              (flipRemainder g (s + i) (s + j) (flipIter g s p j (i + 1) (by omega) (P t)))
              (iteratedCovGrad g 0 s i u)).toFun| := abs_sub _ _
      _ ≤ C * jetSum g s p u * jetSum g s (p - 1) u + CR * jetSum g s p u * jetSum g s (p - 1) u := by
          rw [abs_mul, habs, one_mul]
          exact add_le_add h1 h2
      _ = (C + CR) * jetSum g s p u * jetSum g s (p - 1) u := by ring

end ShortTime
