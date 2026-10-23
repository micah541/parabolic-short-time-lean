import ShortTime.MainTheorems

/-!
# Maximal solutions (paper: `cor:maximal`)

Parabolic solutions on different intervals agree where both are defined (Theorem B), and a solution
on `[0,T]` restricts to one on `[0,T']` for `0 < T' ≤ T`. Hence all solutions glue to one section on
`[0,T*)` (or `[0,T*]`), where `T*` is the supremum of the times with a solution.
-/

noncomputable section

open Bundle Manifold Set Filter
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Analysis.Sobolev
open scoped Manifold ContDiff Topology

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable {r s p : ℕ}

namespace EquationData

variable (D : EquationData I M r s p) {g : SmoothRiemannianMetric I M}
  {u₀ : SmoothCcTensor g r s}

/-- Being a parabolic solution on `[0,T]` only depends on the values on `[0,T]`, and passes to
shorter intervals. -/
theorem isParabolicSolution_of_le {T T' : ℝ} {u v : ℝ → SmoothCcTensor g r s}
    (hu : D.IsParabolicSolution g u₀ T u) (hT' : 0 < T') (hle : T' ≤ T)
    (huv : ∀ t ∈ Icc (0 : ℝ) T', v t = u t) : D.IsParabolicSolution g u₀ T' v := by
  obtain ⟨⟨hpos, hT₀, hsm, hini, hjets, heq⟩, hpar⟩ := hu
  have hsub : Icc (0 : ℝ) T' ⊆ Icc 0 T := Icc_subset_Icc_right hle
  refine ⟨⟨hT', hle.trans hT₀, ?_, ?_, ?_, ?_⟩, ?_⟩
  · refine ((hsm.mono (prod_mono subset_rfl hsub)).congr ?_)
    rintro ⟨x, t⟩ ⟨-, ht⟩
    simp only [huv t ht]
  · rw [huv 0 ⟨le_rfl, hT'.le⟩]; exact hini
  · intro t ht x; rw [huv t ht]; exact hjets t (hsub ht) x
  · intro t ht x
    rw [huv t ht]
    exact ((heq t (hsub ht) x).mono hsub).congr
      (fun y hy => by simp only [huv y hy]) (by simp only [huv t ht])
  · intro t ht x; rw [huv t ht]; exact hpar t (hsub ht) x

end EquationData

/-- **Corollary (maximal solutions, `cor:maximal`).** Under the hypothesis of Theorem A there is a
section `u`, unique on the union of the intervals `[0,T]` carrying a parabolic solution, whose
restriction to every such `[0,T]` is a parabolic solution. (Its interval of existence is `[0,T*)` or
`[0,T*]`, `T*` the supremum of those `T`.) -/
theorem exists_maximal_solution (D : EquationData I M r s p) (hp : 1 ≤ p)
    (g : SmoothRiemannianMetric I M) (u₀ : SmoothCcTensor g r s)
    (h₀ : ∀ x : M, D.IsParabolicAt g 0 x (covJet g r s (2 * p) u₀ x)) :
    (∃ T > 0, ∃ v, D.IsParabolicSolution g u₀ T v) ∧
    ∃ u : ℝ → SmoothCcTensor g r s,
      (∀ T, (∃ v, D.IsParabolicSolution g u₀ T v) → D.IsParabolicSolution g u₀ T u) ∧
      ∀ u' : ℝ → SmoothCcTensor g r s,
        (∀ T, (∃ v, D.IsParabolicSolution g u₀ T v) → D.IsParabolicSolution g u₀ T u') →
        ∀ T, (∃ v, D.IsParabolicSolution g u₀ T v) → ∀ t ∈ Icc (0 : ℝ) T, u' t = u t := by
  classical
  obtain ⟨T₁, hT₁, v₁, hv₁⟩ := exists_solution D hp g u₀ h₀
  refine ⟨⟨T₁, hT₁, v₁, hv₁⟩, ?_⟩
  -- agreement of any two solutions on a common time
  have agree : ∀ {T T' : ℝ} {v v' : ℝ → SmoothCcTensor g r s},
      D.IsParabolicSolution g u₀ T v → D.IsParabolicSolution g u₀ T' v' →
      ∀ t, 0 ≤ t → t ≤ T → t ≤ T' → v t = v' t := by
    intro T T' v v' hv hv' t ht0 htT htT'
    by_cases h0 : t = 0
    · subst h0; rw [hv.1.initial, hv'.1.initial]
    have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm h0)
    have a1 := D.isParabolicSolution_of_le hv htpos htT (fun _ _ => rfl)
    have a2 := D.isParabolicSolution_of_le hv' htpos htT' (fun _ _ => rfl)
    exact solution_unique D hp g a1 a2 t ⟨ht0, le_rfl⟩
  let P : ℝ → Prop := fun T => ∃ v, D.IsParabolicSolution g u₀ T v
  let u : ℝ → SmoothCcTensor g r s := fun t =>
    if h : ∃ T, P T ∧ t ≤ T then (Classical.choose h.choose_spec.1) t else 0
  have hu : ∀ T, P T → D.IsParabolicSolution g u₀ T u := by
    intro T hT
    obtain ⟨v, hv⟩ := hT
    refine D.isParabolicSolution_of_le hv hv.1.pos le_rfl ?_
    intro t ht
    have h : ∃ T', P T' ∧ t ≤ T' := ⟨T, ⟨v, hv⟩, ht.2⟩
    simp only [u, dif_pos h]
    exact agree (Classical.choose_spec h.choose_spec.1) hv t ht.1
      h.choose_spec.2 ht.2
  refine ⟨u, hu, fun u' hu' T hT t ht => ?_⟩
  exact agree (hu' T hT) (hu T hT) t ht.1 ht.2 ht.2

end ShortTime
