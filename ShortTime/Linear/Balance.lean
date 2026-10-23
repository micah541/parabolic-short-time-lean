import ShortTime.Linear.GardingOne
import ShortTime.Linear.Interp

/-!
# Balancing derivatives in a pairing (lower-order terms of `lem:garding`)

For a coefficient family `B(t) : T⁰_{s+b} → T⁰_{s+a}`, jointly smooth on `M × [0, T]`, with
`a ≤ b` and `a + b ≤ 2p - 1`,

  `|⟨∇^a u, B(t) ∇^b u⟩| ≤ C · N_p(u) · N_{p-1}(u)`,   `N_k(u) = ∑_{i ≤ k} ‖∇^i u‖`.

If `b ≤ p` this is Cauchy–Schwarz. Otherwise one integration by parts (`inner_apply_covGrad`)
replaces the pairing by two pairings with `b` smaller by one, of the same type, and we induct.
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

variable {g : SmoothRiemannianMetric I M}

/-- `N_k(u) = ∑_{i ≤ k} ‖∇^i u‖`. -/
def jetSum (g : SmoothRiemannianMetric I M) (s k : ℕ) (u : SmoothCcTensor g 0 s) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), jetNorm g s i u

theorem jetSum_nonneg (s k : ℕ) (u : SmoothCcTensor g 0 s) : 0 ≤ jetSum g s k u :=
  Finset.sum_nonneg fun i _ => jetNorm_nonneg g s i u

theorem jetNorm_le_jetSum (s k i : ℕ) (hi : i ≤ k) (u : SmoothCcTensor g 0 s) :
    jetNorm g s i u ≤ jetSum g s k u :=
  Finset.single_le_sum (f := fun i => jetNorm g s i u) (fun i _ => jetNorm_nonneg g s i u)
    (Finset.mem_range.mpr (by omega))

theorem jetSum_mono (s : ℕ) {k l : ℕ} (hkl : k ≤ l) (u : SmoothCcTensor g 0 s) :
    jetSum g s k u ≤ jetSum g s l u :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
    fun i _ _ => jetNorm_nonneg g s i u

/-- **Balancing lemma.** -/
theorem exists_bound_pairing {s p : ℕ} {T : ℝ} :
    ∀ (b a : ℕ), a ≤ b → a + b + 1 ≤ 2 * p →
      ∀ B : ℝ → SmoothCcTensor g (s + b) (s + a), JointlySmoothOn g (s + b) (s + a) (Icc 0 T) B →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) T, ∀ u : SmoothCcTensor g 0 s,
          |tensorL2Inner (I := I) (M := M) g 0 (s + a) (iteratedCovGrad g 0 s a u).toFun
              (operatorFieldApply (I := I) (M := M) g (s + b) (s + a) (B t)
                (iteratedCovGrad g 0 s b u)).toFun| ≤
            C * jetSum g s p u * jetSum g s (p - 1) u := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
  intro a hab hsum B hB
  by_cases hbp : b ≤ p
  · -- Cauchy–Schwarz: `a ≤ p - 1` and `b ≤ p`
    obtain ⟨K, hK0, hK⟩ := exists_bound_of_jointlySmoothOn hB
    refine ⟨Real.sqrt K, Real.sqrt_nonneg _, fun t ht u => ?_⟩
    have h := abs_inner_operatorFieldApply_le g (s + b) (s + a) (B t) hK0 (hK t ht)
      (iteratedCovGrad g 0 s a u) (iteratedCovGrad g 0 s b u)
    refine h.trans ?_
    have ha : jetNorm g s a u ≤ jetSum g s (p - 1) u := jetNorm_le_jetSum s (p - 1) a (by omega) u
    have hb : jetNorm g s b u ≤ jetSum g s p u := jetNorm_le_jetSum s p b hbp u
    have h0 := Real.sqrt_nonneg K
    calc Real.sqrt K * jetNorm g s a u * jetNorm g s b u
        ≤ Real.sqrt K * jetSum g s (p - 1) u * jetSum g s p u := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left ha h0) hb (jetNorm_nonneg g s b u)
          exact mul_nonneg h0 (jetSum_nonneg s _ u)
      _ = Real.sqrt K * jetSum g s p u * jetSum g s (p - 1) u := by ring
  · -- one integration by parts
    obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    obtain ⟨C₁, hC₁0, hC₁⟩ := ih b' (by omega) (a + 1) (by omega) (by omega)
      (fun t => flipField g (s + b') (s + a) (B t)) (jointlySmoothOn_flipField g hB)
    obtain ⟨C₂, hC₂0, hC₂⟩ := ih b' (by omega) a (by omega) (by omega)
      (fun t => flipRemainder g (s + b') (s + a) (B t)) (jointlySmoothOn_flipRemainder hB)
    refine ⟨C₁ + C₂, by positivity, fun t ht u => ?_⟩
    have hibp := inner_apply_covGrad g (s + b') (s + a) (B t) (iteratedCovGrad g 0 s a u)
      (iteratedCovGrad g 0 s b' u)
    have e : tensorL2Inner (I := I) (M := M) g 0 (s + a) (iteratedCovGrad g 0 s a u).toFun
        (operatorFieldApply (I := I) (M := M) g (s + (b' + 1)) (s + a) (B t)
          (iteratedCovGrad g 0 s (b' + 1) u)).toFun =
        - tensorL2Inner (I := I) (M := M) g 0 (s + (a + 1))
            (iteratedCovGrad g 0 s (a + 1) u).toFun
            (operatorFieldApply (I := I) (M := M) g (s + b') (s + (a + 1))
              (flipField g (s + b') (s + a) (B t)) (iteratedCovGrad g 0 s b' u)).toFun
          - tensorL2Inner (I := I) (M := M) g 0 (s + a) (iteratedCovGrad g 0 s a u).toFun
            (operatorFieldApply (I := I) (M := M) g (s + b') (s + a)
              (flipRemainder g (s + b') (s + a) (B t)) (iteratedCovGrad g 0 s b' u)).toFun :=
      hibp
    rw [e]
    have h1 := hC₁ t ht u
    have h2 := hC₂ t ht u
    have hP := mul_nonneg (jetSum_nonneg s p u) (jetSum_nonneg s (p - 1) u)
    calc _ ≤ |tensorL2Inner (I := I) (M := M) g 0 (s + (a + 1))
            (iteratedCovGrad g 0 s (a + 1) u).toFun
            (operatorFieldApply (I := I) (M := M) g (s + b') (s + (a + 1))
              (flipField g (s + b') (s + a) (B t)) (iteratedCovGrad g 0 s b' u)).toFun| +
          |tensorL2Inner (I := I) (M := M) g 0 (s + a) (iteratedCovGrad g 0 s a u).toFun
            (operatorFieldApply (I := I) (M := M) g (s + b') (s + a)
              (flipRemainder g (s + b') (s + a) (B t)) (iteratedCovGrad g 0 s b' u)).toFun| := by
          rw [sub_eq_add_neg, ← neg_add]
          rw [abs_neg]
          exact abs_add_le _ _
      _ ≤ C₁ * jetSum g s p u * jetSum g s (p - 1) u + C₂ * jetSum g s p u * jetSum g s (p - 1) u :=
          add_le_add h1 h2
      _ = (C₁ + C₂) * jetSum g s p u * jetSum g s (p - 1) u := by ring

end ShortTime
