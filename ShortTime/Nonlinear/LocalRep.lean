import ShortTime.Setting.Equation
import ShortTime.Vendor.ParametricJets
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Equation data in a fixed trivialization

Jets read in the trivializations at a base point `x₀` (`trivJet`), and two smoothness facts used for
the linearized equation: jets of jointly smooth families are smooth in these coordinates
(`contMDiffOn_trivJet_covJet`), and the jet derivative of the local representative `localRep` is
smooth along smooth paths inside the domain (`contMDiffWithinAt_fderiv_localRep`).
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

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M] in
/-- Shifting time preserves joint smoothness. -/
theorem jointlySmoothOn_shift {r s : ℕ} {S S' : Set ℝ}
    {g : SmoothRiemannianMetric I M} {u : ℝ → SmoothCcTensor g r s} (hu : JointlySmoothOn g r s S u) (t₀ : ℝ)
    (hS : ∀ τ ∈ S', t₀ + τ ∈ S) :
    JointlySmoothOn g r s S' (fun τ => u (t₀ + τ)) := by
  unfold JointlySmoothOn at *
  have hφ : ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun q : M × ℝ => (q.1, t₀ + q.2)) :=
    contMDiff_fst.prodMk ((contDiff_const.add contDiff_id).contMDiff.comp contMDiff_snd)
  exact hu.comp hφ.contMDiffOn fun q hq => ⟨mem_univ _, hS _ hq.2⟩

namespace EquationData

/-- The coordinates of a jet in the trivializations at `x₀`. -/
def trivJet {r s N : ℕ} (x₀ y : M) (ζ : CovJetFiber I r s N y) : JetModel E r s N :=
  fun k => (trivAt I M r (s + k) x₀).continuousLinearMapAt ℝ y (ζ k)

theorem jetOfModel_trivJet {r s N : ℕ} {x₀ y : M} (hy : y ∈ jetBase (I := I) r s N x₀)
    (ζ : CovJetFiber I r s N y) : jetOfModel r s N x₀ y (trivJet x₀ y ζ) = ζ := by
  funext k
  exact Trivialization.symmL_continuousLinearMapAt _ (mem_iInter.mp hy.2 k) (ζ k)

theorem localRep_trivJet {r s p : ℕ} (D : EquationData I M r s p) {x₀ y : M}
    (hy : y ∈ jetBase (I := I) r s (2 * p) x₀) (t : ℝ) (ζ : CovJetFiber I r s (2 * p) y) :
    localRep r s (2 * p) D.F x₀ (t, y, trivJet x₀ y ζ) =
      (trivAt I M r s x₀).continuousLinearMapAt ℝ y (D.F t y ζ) := by
  simp only [localRep, jetOfModel_trivJet hy]

/-! ### Smoothness in the parameters -/

/-- The jets of a jointly smooth family, read in the trivializations at `x₀`, are jointly smooth. -/
theorem contMDiffOn_trivJet_covJet {r s N : ℕ} {g : SmoothRiemannianMetric I M} {S : Set ℝ}
    {u : ℝ → SmoothCcTensor g r s} (hu : JointlySmoothOn g r s S u) (x₀ : M) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, JetModel E r s N) ∞
      (fun q : M × ℝ => trivJet x₀ q.1 (covJet g r s N (u q.2) q.1))
      (jetBase (I := I) r s N x₀ ×ˢ S) := by
  rw [contMDiffOn_pi_space]
  intro k
  have hk := Vendor.covGrad_iter_joint (I := I) (M := M) g r s k u S hu
  have hk' : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r (s + k) ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r (s + k) ℝ E)
        (E := fun x : M => TensorRSSpace r (s + k) I x) q.1
        ((iteratedCovGrad g r s k (u q.2)).toSection q.1))
      (jetBase (I := I) r s N x₀ ×ˢ S) :=
    hk.mono (prod_mono (subset_univ _) le_rfl)
  rw [(trivAt I M r (s + k) x₀).contMDiffOn_iff
    (fun q hq => (trivAt I M r (s + k) x₀).mem_source.mpr (mem_iInter.mp hq.1.2 k))] at hk'
  refine hk'.2.congr fun q hq => ?_
  simp only [trivJet, covJet]
  rw [Trivialization.continuousLinearMapAt_apply,
    Trivialization.coe_linearMapAt_of_mem _ (mem_iInter.mp hq.1.2 k)]

/-- **The jet derivative of the local representative is smooth along smooth paths in the domain.**
-/
theorem contMDiffWithinAt_fderiv_localRep {r s p : ℕ} (D : EquationData I M r s p) (x₀ : M)
    {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] {HN : Type*} [TopologicalSpace HN]
    {J : ModelWithCorners ℝ EN HN} {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]
    [IsManifold J ∞ N] {φ : N → ℝ × M} {γ : N → JetModel E r s (2 * p)} {t : Set N} {n₀ : N}
    (hn₀ : n₀ ∈ t) (hφ : ContMDiffWithinAt J (𝓘(ℝ, ℝ).prod I) ∞ φ t n₀)
    (hγ : ContMDiffWithinAt J 𝓘(ℝ, JetModel E r s (2 * p)) ∞ γ t n₀)
    (hmem : ∀ n ∈ t, (φ n).1 ∈ Icc (0 : ℝ) D.T₀ ∧ (φ n).2 ∈ jetBase (I := I) r s (2 * p) x₀ ∧
      jetOfModel r s (2 * p) x₀ (φ n).2 (γ n) ∈ D.dom (φ n).1 (φ n).2) :
    ContMDiffWithinAt J 𝓘(ℝ, JetModel E r s (2 * p) →L[ℝ] TensorRSModel r s ℝ E) ∞
      (fun n => fderiv ℝ (fun z => localRep r s (2 * p) D.F x₀ ((φ n).1, (φ n).2, z)) (γ n))
      t n₀ := by
  obtain ⟨U, hU, hdom⟩ := D.dom_relOpen x₀
  have hloc : ∀ n ∈ t, ∀ z, ((φ n).1, (φ n).2, z) ∈ U →
      ((φ n).1, (φ n).2, z) ∈ localDom r s (2 * p) D.T₀ D.dom x₀ := by
    intro n hn z hz
    rw [hdom]
    exact ⟨hz, (hmem n hn).1, (hmem n hn).2.1⟩
  have hq₀ : ((φ n₀).1, (φ n₀).2, γ n₀) ∈ U := by
    have h : ((φ n₀).1, (φ n₀).2, γ n₀) ∈ localDom r s (2 * p) D.T₀ D.dom x₀ :=
      ⟨⟨(hmem n₀ hn₀).1, (hmem n₀ hn₀).2.1⟩, (hmem n₀ hn₀).2.2⟩
    rw [hdom] at h
    exact h.1
  -- a product neighbourhood inside `U`
  let Θ : (ℝ × M) × JetModel E r s (2 * p) → ℝ × M × JetModel E r s (2 * p) :=
    fun q => (q.1.1, q.1.2, q.2)
  have hΘ : Continuous Θ :=
    (continuous_fst.comp continuous_fst).prodMk ((continuous_snd.comp continuous_fst).prodMk
      continuous_snd)
  obtain ⟨A, B, hA, hφA, hB, hγB, hAB⟩ :=
    mem_nhds_prod_iff'.mp ((hU.preimage hΘ).mem_nhds (show Θ (φ n₀, γ n₀) ∈ U from hq₀))
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hB (γ n₀) hγB
  set u := Metric.ball (γ n₀) ε with hu_def
  set t' := t ∩ φ ⁻¹' A ∩ γ ⁻¹' u with ht'_def
  have ht' : t' ∈ 𝓝[t] n₀ :=
    inter_mem (inter_mem self_mem_nhdsWithin
      (hφ.continuousWithinAt.preimage_mem_nhdsWithin (hA.mem_nhds hφA)))
      (hγ.continuousWithinAt.preimage_mem_nhdsWithin
        (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε)))
  have hn₀' : n₀ ∈ t' := ⟨⟨hn₀, hφA⟩, Metric.mem_ball_self hε⟩
  -- the local representative along the path
  set f : N → JetModel E r s (2 * p) → TensorRSModel r s ℝ E :=
    fun n z => localRep r s (2 * p) D.F x₀ ((φ n).1, (φ n).2, z) with hf_def
  have hφ1 : ContMDiffWithinAt J 𝓘(ℝ, ℝ) ∞ (fun n => (φ n).1) t n₀ :=
    contMDiffWithinAt_fst.comp n₀ hφ (mapsTo_univ _ _)
  have hφ2 : ContMDiffWithinAt J I ∞ (fun n => (φ n).2) t n₀ :=
    contMDiffWithinAt_snd.comp n₀ hφ (mapsTo_univ _ _)
  have hΘ' : ContMDiffWithinAt (J.prod 𝓘(ℝ, JetModel E r s (2 * p)))
      (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, JetModel E r s (2 * p)))) ∞
      (fun q : N × JetModel E r s (2 * p) => ((φ q.1).1, (φ q.1).2, q.2)) (t' ×ˢ u) (n₀, γ n₀) :=
    ((hφ1.mono (inter_subset_left.trans inter_subset_left)).comp (n₀, γ n₀)
        contMDiffWithinAt_fst fun q hq => hq.1).prodMk
      (((hφ2.mono (inter_subset_left.trans inter_subset_left)).comp (n₀, γ n₀)
        contMDiffWithinAt_fst fun q hq => hq.1).prodMk contMDiffWithinAt_snd)
  have hmaps : MapsTo (fun q : N × JetModel E r s (2 * p) => ((φ q.1).1, (φ q.1).2, q.2))
      (t' ×ˢ u) (localDom r s (2 * p) D.T₀ D.dom x₀) := by
    intro q hq
    exact hloc q.1 hq.1.1.1 q.2 (hAB (mk_mem_prod hq.1.1.2 (hball hq.2)))
  have hfsm : ContMDiffWithinAt (J.prod 𝓘(ℝ, JetModel E r s (2 * p))) 𝓘(ℝ, TensorRSModel r s ℝ E) ∞
      (Function.uncurry f) (t' ×ˢ u) (n₀, γ n₀) :=
    ((D.smooth x₀) _ (hmaps ⟨hn₀', Metric.mem_ball_self hε⟩)).comp (n₀, γ n₀) hΘ' hmaps
  have key := ContMDiffWithinAt.mfderivWithin hfsm (hγ.mono (inter_subset_left.trans
    inter_subset_left)) hn₀' (fun n hn => hn.2) (by simp) Metric.isOpen_ball.uniqueMDiffOn
  refine (key.congr (fun n hn => ?_) ?_).mono_of_mem_nhdsWithin ht'
  · simp +unfoldPartialApp only [inTangentCoordinates]
    rw [mfderivWithin_eq_fderivWithin, fderivWithin_of_isOpen Metric.isOpen_ball hn.2]
    erw [inCoordinates_tangent_bundle_core_model_space]
  · simp +unfoldPartialApp only [inTangentCoordinates]
    rw [mfderivWithin_eq_fderivWithin, fderivWithin_of_isOpen Metric.isOpen_ball hn₀'.2]
    erw [inCoordinates_tangent_bundle_core_model_space]

end EquationData

end ShortTime
