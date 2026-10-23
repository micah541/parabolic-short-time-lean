import ShortTime.Nonlinear.FibreMap

/-!
# The nonlinearity of an equation as a fibre map

For equation data `D` on `T⁰_s M`, the map `F(t, ζ)` on covariant `2p`-jets is a smooth fibre map on
`⊕_{k ≤ 2p} T⁰_{s+k} M` (`EquationData.toFibreMap`), with a dummy parameter. Applied to the jets
`(∇^k u)_k` of a family `u`, it gives the family `F[u]`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set Filter Topology
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Analysis.Sobolev
open scoped Manifold ContDiff

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

namespace EquationData

variable {s p : ℕ}

/-- The ranks `s + k`, `k ≤ 2p`, of the components of a covariant `2p`-jet. -/
abbrev jetRanks (s p : ℕ) : Fin (2 * p + 1) → ℕ := fun k => s + (k : ℕ)

theorem prodBase_jetRanks (x₀ : M) :
    prodBase (I := I) (jetRanks s p) s x₀ = jetBase (I := I) 0 s (2 * p) x₀ := rfl

/-- **The nonlinearity as a fibre map**, with a dummy parameter in `ℝ`. -/
def toFibreMap (D : EquationData I M 0 s p) : FibreMap I M ℝ (jetRanks s p) s where
  T₀ := D.T₀
  dom _ := D.dom
  F _ := D.F
  dom_relOpen x₀ := by
    obtain ⟨U, hU, hdom⟩ := D.dom_relOpen x₀
    refine ⟨{q | (q.2.1, q.2.2.1, q.2.2.2) ∈ U}, ?_, ?_⟩
    · exact hU.preimage (continuous_snd.fst.prodMk (continuous_snd.snd.fst.prodMk
        continuous_snd.snd.snd))
    · ext q
      have h := congrArg (fun S => (q.2.1, q.2.2.1, q.2.2.2) ∈ S) hdom
      simp only [localDom, localSlab, mem_inter_iff, mem_setOf_eq, eq_iff_iff] at h
      simp only [prodSlab, mem_inter_iff, mem_setOf_eq, prodBase_jetRanks]
      constructor
      · rintro ⟨hs, hd⟩
        exact ⟨(h.mp ⟨hs, hd⟩).1, hs⟩
      · rintro ⟨hU', hs⟩
        exact ⟨hs, (h.mpr ⟨hU', hs⟩).2⟩
  smooth x₀ := by
    have hD := D.smooth x₀
    have hπ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, JetModel E 0 s (2 * p)))))
        (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, JetModel E 0 s (2 * p)))) ∞
        (fun q : ℝ × ℝ × M × JetModel E 0 s (2 * p) => q.2) := contMDiff_snd
    refine (hD.comp hπ.contMDiffOn ?_)
    rintro q ⟨hs, hd⟩
    exact ⟨hs, hd⟩

@[simp] theorem toFibreMap_F (D : EquationData I M 0 s p) (lam t : ℝ) (x : M) :
    D.toFibreMap.F lam t x = D.F t x := rfl

@[simp] theorem toFibreMap_dom (D : EquationData I M 0 s p) (lam t : ℝ) (x : M) :
    D.toFibreMap.dom lam t x = D.dom t x := rfl

/-- The jets `(∇^k u)_{k ≤ 2p}` of a family, as a tuple of families. -/
def jetFamily {g : SmoothRiemannianMetric I M} (u : ℝ → SmoothCcTensor g 0 s) :
    ∀ k : Fin (2 * p + 1), ℝ → SmoothCcTensor g 0 (jetRanks s p k) :=
  fun k t => iteratedCovGrad g 0 s k (u t)

theorem valAt_jetFamily {g : SmoothRiemannianMetric I M} (u : ℝ → SmoothCcTensor g 0 s) (t : ℝ)
    (x : M) :
    FibreMap.valAt (fun k => jetFamily (p := p) u k t) x = covJet g 0 s (2 * p) (u t) x := rfl

/-- **The family `F[u]`**, `t ↦ F(t, j^{2p} u(t))`. -/
def nonlinFamily (D : EquationData I M 0 s p) {g : SmoothRiemannianMetric I M}
    (u : ℝ → SmoothCcTensor g 0 s) : ℝ → SmoothCcTensor g 0 s :=
  D.toFibreMap.apply 0 (jetFamily u)

end EquationData

end ShortTime
