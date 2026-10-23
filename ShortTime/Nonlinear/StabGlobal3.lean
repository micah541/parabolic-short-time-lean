import ShortTime.Nonlinear.StabGlobal2

/-!
# Uniform stability of parabolicity on `M × [0, T]` (`cor:C`)
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set Filter Topology
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Elliptic DifferentialGeometry.Geometry.Connection
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

namespace EquationData

variable {s p : ℕ} (D : EquationData I M 0 s p)

/-- **Uniform stability of parabolicity.** If the jets of the smooth family `u` are parabolic at
every point of `M × [0, T]`, there are `η > 0` and `lam > 0` such that every jet `ζ` with
`|ζ_k - ∇^k u|² ≤ η` (`k ≤ 2p`) at `(t, y)` lies in the domain and satisfies the Legendre
condition with constant `lam`. -/
theorem exists_stab {T : ℝ} (hTD : T ≤ D.T₀) {u : ℝ → SmoothCcTensor g 0 s}
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u)
    (hpar : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, D.IsParabolicAt g t x (covJet g 0 s (2 * p) (u t) x)) :
    ∃ η > 0, ∃ lam > 0, ∀ t ∈ Icc (0 : ℝ) T, ∀ y : M, ∀ ζ : CovJetFiber I 0 s (2 * p) y,
      (∀ k : Fin (2 * p + 1), riemannianFiberNormSq (I := I) (M := M) g 0 (s + k) y
        (ζ k - covJet g 0 s (2 * p) (u t) y k) ≤ η) →
      ζ ∈ D.dom t y ∧ LegendreAt g 0 s p y (D.principal t y ζ) lam := by
  classical
  have hdata : ∀ q : M × ℝ, ∃ lam > 0, ∃ η > 0, ∃ W ∈ 𝓝 q, ∀ y : M, ∀ t : ℝ, (y, t) ∈ W →
      t ∈ Icc (0 : ℝ) T → ∀ ζ : CovJetFiber I 0 s (2 * p) y,
        (∀ k : Fin (2 * p + 1), riemannianFiberNormSq (I := I) (M := M) g 0 (s + k) y
          (ζ k - covJet g 0 s (2 * p) (u t) y k) ≤ η) →
        ζ ∈ D.dom t y ∧ LegendreAt g 0 s p y (D.principal t y ζ) lam := by
    intro q
    by_cases hq : q.2 ∈ Icc (0 : ℝ) T
    · exact D.stab_box hTD hu hpar q.1 hq
    · refine ⟨1, one_pos, 1, one_pos, {q' | q'.2 ∈ (Icc (0 : ℝ) T)ᶜ}, ?_, ?_⟩
      · exact (isClosed_Icc.isOpen_compl.preimage continuous_snd).mem_nhds hq
      · intro y t hyt ht
        exact absurd ht hyt
  choose lam hlam η hη W hW hprop using hdata
  obtain ⟨t, -, hcover⟩ := (isCompact_univ.prod (isCompact_Icc (a := (0 : ℝ)) (b := T))).elim_nhds_subcover
    W (fun q _ => hW q)
  obtain ⟨c, hc, hct⟩ := exists_pos_le_finset lam hlam t
  obtain ⟨e, he, het⟩ := exists_pos_le_finset η hη t
  refine ⟨e, he, c, hc, fun t' ht' y ζ hζ => ?_⟩
  have hmem : (y, t') ∈ Set.univ ×ˢ Icc (0 : ℝ) T := ⟨mem_univ _, ht'⟩
  have := hcover hmem
  simp only [mem_iUnion] at this
  obtain ⟨q, hqt, hqW⟩ := this
  have h := hprop q y t' hqW ht' ζ (fun k => (hζ k).trans (het q hqt))
  exact ⟨h.1, LegendreAt.mono g h.2 hc (hct q hqt)⟩

end EquationData

end ShortTime
