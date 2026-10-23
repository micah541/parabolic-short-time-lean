import ShortTime.Linear.LimitSmooth
import ShortTime.Nonlinear.LocalRep

/-!
# A uniform tube around the jets of a smooth family lies in the domain

Let `w` be a jointly smooth family on `[0,T]` whose `2p`-jets lie in the domain of the equation.
Then there is `δ > 0` such that every jet `ζ` at `(x, t)` with `|ζ_k - ∇^k w(t, x)|² ≤ δ` for all
`k ≤ 2p` lies in the domain (`EquationData.exists_dom_tube`).

This is the openness of `𝒫^m_𝒟` in `cor:N`: the domain is relatively open, `M × [0,T]` is compact,
and on compact subsets of a chart the coordinates in the trivialization are bounded by the fibre norm
(`exists_norm_twist_le`).
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set Filter Topology
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral DifferentialGeometry.Analysis.Elliptic
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

theorem tube_arith {C δ ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) (h : δ = ε ^ 2 / (2 * (C + 1))) :
    C * δ < ε ^ 2 := by
  subst h
  have h1 : 0 < 2 * (C + 1) := by linarith
  rw [mul_div_assoc', div_lt_iff₀ h1]
  have h2 : 0 < ε ^ 2 := by positivity
  nlinarith

namespace EquationData

variable {s p : ℕ} (D : EquationData I M 0 s p)

/-- **The tube lemma near a point.** -/
theorem exists_dom_tube_local {T : ℝ} (hTD : T ≤ D.T₀) {w : ℝ → SmoothCcTensor g 0 s}
    (hw : JointlySmoothOn g 0 s (Icc 0 T) w)
    (hdom : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, covJet g 0 s (2 * p) (w t) x ∈ D.dom t x)
    (x₀ : M) (t₀ : ℝ) (ht₀ : t₀ ∈ Icc (0 : ℝ) T) :
    ∃ δ > 0, ∀ᶠ q : M × ℝ in 𝓝 (x₀, t₀), q.2 ∈ Icc (0 : ℝ) T →
      ∀ ζ : CovJetFiber I 0 s (2 * p) q.1,
        (∀ k : Fin (2 * p + 1), riemannianFiberNormSq (I := I) (M := M) g 0 (s + k) q.1
          (ζ k - covJet g 0 s (2 * p) (w q.2) q.1 k) ≤ δ) → ζ ∈ D.dom q.2 q.1 := by
  obtain ⟨U, hUo, hU⟩ := D.dom_relOpen x₀
  have hB : IsOpen (jetBase (I := I) 0 s (2 * p) x₀) :=
    (trivAt I M 0 s x₀).open_baseSet.inter
      (isOpen_iInter_of_finite fun k => (trivAt I M 0 (s + k) x₀).open_baseSet)
  have hx₀B : x₀ ∈ jetBase (I := I) 0 s (2 * p) x₀ :=
    ⟨mem_baseSet_trivializationAt _ _ x₀, mem_iInter.mpr fun _ => mem_baseSet_trivializationAt _ _ x₀⟩
  set S : Set ((M × ℝ) × JetModel E 0 s (2 * p)) :=
    (jetBase (I := I) 0 s (2 * p) x₀ ×ˢ Icc 0 T) ×ˢ univ with hS
  let Ψ : (M × ℝ) × JetModel E 0 s (2 * p) → ℝ × M × JetModel E 0 s (2 * p) :=
    fun q => (q.1.2, q.1.1, trivJet x₀ q.1.1 (covJet g 0 s (2 * p) (w q.1.2) q.1.1) + q.2)
  have hΨ : ContinuousOn Ψ S := by
    have h1 := (contMDiffOn_trivJet_covJet (N := 2 * p) hw x₀).continuousOn
    refine continuous_fst.snd.continuousOn.prodMk (continuous_fst.fst.continuousOn.prodMk ?_)
    exact (h1.comp continuous_fst.continuousOn fun q hq => hq.1).add continuous_snd.continuousOn
  have hin : Ψ ((x₀, t₀), 0) ∈ U := by
    have h : ((t₀, x₀, trivJet x₀ x₀ (covJet g 0 s (2 * p) (w t₀) x₀)) :
        ℝ × M × JetModel E 0 s (2 * p)) ∈ localDom 0 s (2 * p) D.T₀ D.dom x₀ := by
      refine ⟨⟨⟨ht₀.1, ht₀.2.trans hTD⟩, hx₀B⟩, ?_⟩
      change jetOfModel 0 s (2 * p) x₀ x₀ (trivJet x₀ x₀ (covJet g 0 s (2 * p) (w t₀) x₀)) ∈
        D.dom t₀ x₀
      rw [jetOfModel_trivJet hx₀B]
      exact hdom t₀ ht₀ x₀
    rw [hU] at h
    have e : Ψ ((x₀, t₀), 0) = (t₀, x₀, trivJet x₀ x₀ (covJet g 0 s (2 * p) (w t₀) x₀)) := by
      simp only [Ψ, add_zero]
    rw [e]
    exact h.1
  have hmem : Ψ ⁻¹' U ∈ 𝓝[S] ((x₀, t₀), (0 : JetModel E 0 s (2 * p))) :=
    (hΨ _ ⟨⟨hx₀B, ht₀⟩, mem_univ _⟩).preimage_mem_nhdsWithin (hUo.mem_nhds hin)
  obtain ⟨V, hV, hVS⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hmem
  obtain ⟨A, hA, Z, hZ, hAZ⟩ := mem_nhds_prod_iff.mp hV
  obtain ⟨ε, hε, hεZ⟩ := Metric.mem_nhds_iff.mp hZ
  obtain ⟨K, hKc, hx₀K, hKsub⟩ := exists_compact_subset ((chartAt H x₀).open_source.inter hB)
    ⟨mem_chart_source H x₀, hx₀B⟩
  have hKs : K ⊆ (chartAt H x₀).source := fun y hy => (hKsub hy).1
  choose C hC0 hC using fun k : Fin (2 * p + 1) =>
    exists_norm_twist_le (g := g) x₀ (s + k) hKc hKs
  have hCs : 0 ≤ ∑ k, C k := Finset.sum_nonneg fun k _ => hC0 k
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = ε ^ 2 / (2 * (∑ k, C k + 1)) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by
    rw [hδ]
    have : 0 < 2 * (∑ k, C k + 1) := by linarith
    positivity
  refine ⟨δ, hδ0, ?_⟩
  have hKn : ∀ᶠ q : M × ℝ in 𝓝 (x₀, t₀), q.1 ∈ interior K :=
    continuous_fst.continuousAt.eventually_mem (isOpen_interior.mem_nhds hx₀K)
  filter_upwards [hA, hKn] with q hqA hqK hqT ζ hζ
  have hqKs : q.1 ∈ (chartAt H x₀).source := hKs (interior_subset hqK)
  have hqB : q.1 ∈ jetBase (I := I) 0 s (2 * p) x₀ := (hKsub (interior_subset hqK)).2
  set z : JetModel E 0 s (2 * p) :=
    trivJet x₀ q.1 ζ - trivJet x₀ q.1 (covJet g 0 s (2 * p) (w q.2) q.1) with hz_def
  have hz : z ∈ Z := by
    apply hεZ
    rw [Metric.mem_ball, dist_zero_right]
    refine (pi_norm_lt_iff hε).2 fun k => ?_
    have e : z k = chartRSTwistInv (I := I) (M := M) x₀ q.1 0 (s + k)
        (TensorRSSpace.toModel (ζ k - covJet g 0 s (2 * p) (w q.2) q.1 k)) := by
      simp only [hz_def, Pi.sub_apply, trivJet]
      rw [← map_sub]
      exact triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel 0 (s + k) x₀ hqKs _
    have h1 := hC k q.1 (interior_subset hqK) (ζ k - covJet g 0 s (2 * p) (w q.2) q.1 k)
    rw [← e] at h1
    have h2 : C k * riemannianFiberNormSq (I := I) (M := M) g 0 (s + k) q.1
        (ζ k - covJet g 0 s (2 * p) (w q.2) q.1 k) ≤ (∑ k, C k) * δ :=
      (mul_le_mul_of_nonneg_left (hζ k) (hC0 k)).trans (mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun k _ => hC0 k) (Finset.mem_univ k)) hδ0.le)
    have h3 := tube_arith hCs hε hδ
    exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hε.le two_ne_zero).1
      (h1.trans_lt (h2.trans_lt h3))
  have hΨq : Ψ (q, z) ∈ U := hVS ⟨hAZ ⟨hqA, hz⟩, ⟨hqB, hqT⟩, mem_univ _⟩
  have e2 : Ψ (q, z) = (q.2, q.1, trivJet x₀ q.1 ζ) := by
    simp only [Ψ, hz_def, add_sub_cancel]
  rw [e2] at hΨq
  have h : ((q.2, q.1, trivJet x₀ q.1 ζ) : ℝ × M × JetModel E 0 s (2 * p)) ∈
      localDom 0 s (2 * p) D.T₀ D.dom x₀ := by
    rw [hU]
    exact ⟨hΨq, ⟨hqT.1, hqT.2.trans hTD⟩, hqB⟩
  have h2 := h.2
  change jetOfModel 0 s (2 * p) x₀ q.1 (trivJet x₀ q.1 ζ) ∈ D.dom q.2 q.1 at h2
  rwa [jetOfModel_trivJet hqB] at h2

/-- The jets `ζ` within `δ` of the jets of `w` at `q = (x, t)`, `t ∈ [0,T]`, lie in the domain. -/
def TubeGood (w : ℝ → SmoothCcTensor g 0 s) (T δ : ℝ) (q : M × ℝ) : Prop :=
  q.2 ∈ Icc (0 : ℝ) T → ∀ ζ : CovJetFiber I 0 s (2 * p) q.1,
    (∀ k : Fin (2 * p + 1), riemannianFiberNormSq (I := I) (M := M) g 0 (s + k) q.1
      (ζ k - covJet g 0 s (2 * p) (w q.2) q.1 k) ≤ δ) → ζ ∈ D.dom q.2 q.1

theorem tubeGood_mono (w : ℝ → SmoothCcTensor g 0 s) (T : ℝ) {δ δ' : ℝ} (h : δ' ≤ δ)
    {q : M × ℝ} (hq : D.TubeGood w T δ q) : D.TubeGood w T δ' q :=
  fun hT ζ hζ => hq hT ζ fun k => (hζ k).trans h

/-- **The tube lemma.** Around the jets of a smooth family `w` with jets in the domain on `[0,T]`,
a uniform pointwise tube (in the Riemannian fibre norms) lies in the domain. -/
theorem exists_dom_tube {T : ℝ} (hTD : T ≤ D.T₀) {w : ℝ → SmoothCcTensor g 0 s}
    (hw : JointlySmoothOn g 0 s (Icc 0 T) w)
    (hdom : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, covJet g 0 s (2 * p) (w t) x ∈ D.dom t x) :
    ∃ δ > 0, ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, ∀ ζ : CovJetFiber I 0 s (2 * p) x,
      (∀ k : Fin (2 * p + 1), riemannianFiberNormSq (I := I) (M := M) g 0 (s + k) x
        (ζ k - covJet g 0 s (2 * p) (w t) x k) ≤ δ) → ζ ∈ D.dom t x := by
  obtain ⟨Uf, hUf⟩ : ∃ Uf : {δ : ℝ // 0 < δ} → Set (M × ℝ),
      ∀ δ, Uf δ = interior {q | D.TubeGood w T δ.1 q} := ⟨_, fun _ => rfl⟩
  have hcov : (univ : Set M) ×ˢ Icc (0 : ℝ) T ⊆ ⋃ δ, Uf δ := by
    rintro ⟨x₀, t₀⟩ ⟨-, ht₀⟩
    obtain ⟨δ, hδ, hev⟩ := D.exists_dom_tube_local hTD hw hdom x₀ t₀ ht₀
    refine mem_iUnion.2 ⟨⟨δ, hδ⟩, ?_⟩
    rw [hUf]
    exact mem_interior_iff_mem_nhds.2 hev
  have hdir : Directed (· ⊆ ·) Uf := by
    intro a b
    refine ⟨⟨min a.1 b.1, lt_min a.2 b.2⟩, ?_, ?_⟩
    · rw [hUf, hUf]
      exact interior_mono fun q hq => D.tubeGood_mono w T (min_le_left _ _) hq
    · rw [hUf, hUf]
      exact interior_mono fun q hq => D.tubeGood_mono w T (min_le_right _ _) hq
  have : Nonempty {δ : ℝ // 0 < δ} := ⟨⟨1, one_pos⟩⟩
  obtain ⟨δ, hδ⟩ := (isCompact_univ.prod isCompact_Icc).elim_directed_cover Uf
    (fun δ => by rw [hUf]; exact isOpen_interior) hcov hdir
  refine ⟨δ.1, δ.2, fun t ht x ζ hζ => ?_⟩
  have h := hδ (show (x, t) ∈ (univ : Set M) ×ˢ Icc (0 : ℝ) T from ⟨mem_univ x, ht⟩)
  rw [hUf] at h
  exact interior_subset h ht ζ hζ

end EquationData

end ShortTime
