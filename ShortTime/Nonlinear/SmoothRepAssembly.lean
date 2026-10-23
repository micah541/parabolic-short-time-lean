import ShortTime.Nonlinear.SmoothRepSpatial

/-!
# A smooth representative from chart-level smoothness (`prop:regularity`, assembly)

* `rawJoint_of_chart`: a family of (not necessarily smooth) sections whose readings in the chart and
  trivialization at every point are `C^∞` on `[0, T] ×` (a ball around the chart centre) is jointly
  smooth on `M × [0, T]` (as in `rawJoint_limSec`).
* `secFam`: such a family, packaged as a jointly smooth family of smooth tensor fields.
* **`exists_smooth_rep`**: for `v ∈ 𝒫^m`, if at every point `σ ↦ Π_σ v` is `C^∞` near `0` for a
  frame with constant chart coordinates (Angenent's trick), and the continuous representative
  satisfies an evolution equation `∂ₜ v̂ = G` in charts whose right side `G` has the regularity of
  `v̂` (`SpatialReg.SpC`; this is the case for `G = F(t, x, jets of v̂)`), then `v̂` is the value of a
  jointly smooth family on `[0, T]`.
-/

noncomputable section

open Bundle Manifold Set Filter Topology Metric
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
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

variable {g : SmoothRiemannianMetric I M} {s p m : ℕ} {T : ℝ}

open ParabolicSpace HFlow

namespace SmoothRep

theorem mem_trivAt_baseSet_of_chart {a : ℕ} {α x : M} (hx : x ∈ (chartAt H α).source) :
    x ∈ (trivAt I M 0 a α).baseSet := by
  change x ∈ ((trivializationAt (Tensor0SBundle.Tensor0SModel 0 ℝ E)
      (fun y : M => Tensor0SBundle.Tensor0SSpace 0 I y) α).baseSet) ∩
      ((trivializationAt (Tensor0SBundle.Tensor0SModel a ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace a I y) α).baseSet)
  refine ⟨?_, ?_⟩ <;>
    · change x ∈ (trivializationAt E (TangentSpace I) α).baseSet
      rw [TangentBundle.trivializationAt_baseSet]
      exact hx

/-- **Joint smoothness from chart readings**: if, at every point `α`, the readings of the sections
`R t` in the chart and trivialization at `α` are `C^∞` on `[0, T] × B(chart α, ε)`, then `R` is
jointly smooth on `M × [0, T]`. -/
theorem rawJoint_of_chart_cover {a : ℕ} {R : ℝ → (x : M) → TensorRSSpace 0 a I x}
    (hR : ∀ x : M, ∃ α : M, ∃ ε > 0, x ∈ (chartAt H α).source ∧ extChartAt I α x ∈ Metric.ball (extChartAt I α α) ε ∧
      Metric.ball (extChartAt I α α) ε ⊆ (extChartAt I α).target ∧
      ContDiffOn ℝ ∞ (fun q : ℝ × E => (trivAt I M 0 a α).continuousLinearMapAt ℝ
        ((extChartAt I α).symm q.2) (R q.1 ((extChartAt I α).symm q.2)))
        (Icc 0 T ×ˢ Metric.ball (extChartAt I α α) ε)) :
    RawJoint 0 a (Icc 0 T) R := by
  intro p₀ hp₀
  have ht₀ : p₀.2 ∈ Icc 0 T := hp₀.2
  obtain ⟨α, r, hr, hxs, hxb, hball, hL⟩ := hR p₀.1
  set φ := extChartAt I α with hφ
  set U := (chartAt H α).source ∩ φ ⁻¹' Metric.ball (φ α) r with hU
  have hUo : IsOpen U := by
    have := (continuousOn_extChartAt (I := I) α).isOpen_inter_preimage (isOpen_extChartAt_source α)
      (Metric.isOpen_ball (x := φ α) (ε := r))
    rwa [extChartAt_source] at this
  have hαU : p₀.1 ∈ U := ⟨hxs, hxb⟩
  set Lc := fun q : ℝ × E => (trivAt I M 0 a α).continuousLinearMapAt ℝ
    ((extChartAt I α).symm q.2) (R q.1 ((extChartAt I α).symm q.2)) with hLc
  have hF : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, TensorRSModel 0 a ℝ E) ∞
      (fun p : M × ℝ => Lc (p.2, φ p.1)) (U ×ˢ Icc 0 T) p₀ := by
    have hmove : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ × E) ∞
        (fun q : M × ℝ => (q.2, φ q.1)) (U ×ˢ Icc 0 T) p₀ := by
      have hmoveOn : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞
          (fun q : M × ℝ => (q.2, φ q.1)) (U ×ˢ Icc 0 T) := by
        refine ContMDiffOn.prodMk contMDiffOn_snd ?_
        exact (contMDiffOn_extChartAt (I := I) (x := α)).comp contMDiffOn_fst
          (fun q hq => hq.1.1)
      have hm := hmoveOn p₀ ⟨hαU, ht₀⟩
      rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hm
      exact hm
    have hEuM : ContMDiffWithinAt 𝓘(ℝ, ℝ × E) 𝓘(ℝ, TensorRSModel 0 a ℝ E) ∞ Lc
        (Icc 0 T ×ˢ Metric.ball (φ α) r) (p₀.2, φ p₀.1) := by
      rw [contMDiffWithinAt_iff_contDiffWithinAt]
      exact hL _ ⟨ht₀, hxb⟩
    exact hEuM.comp p₀ hmove (fun q hq =>
      (⟨hq.2, hq.1.2⟩ : (q.2, φ q.1) ∈ Icc 0 T ×ˢ Metric.ball (φ α) r))
  have hval : ∀ p : M × ℝ, p ∈ U ×ˢ Icc 0 T →
      ((trivializationAt (TensorRSModel 0 a ℝ E) (fun y : M => TensorRSSpace 0 a I y) α)
        ⟨p.1, R p.2 p.1⟩).2 = Lc (p.2, φ p.1) := by
    intro p hp
    have hsrc : p.1 ∈ φ.source := by rw [hφ, extChartAt_source]; exact hp.1.1
    have e1 : ((trivializationAt (TensorRSModel 0 a ℝ E) (fun y : M => TensorRSSpace 0 a I y) α)
        ⟨p.1, R p.2 p.1⟩).2 =
        (trivAt I M 0 a α).continuousLinearMapAt ℝ p.1 (R p.2 p.1) := by
      rw [Bundle.Trivialization.continuousLinearMapAt_apply,
        Bundle.Trivialization.coe_linearMapAt_of_mem _ (mem_trivAt_baseSet_of_chart hp.1.1)]
    rw [e1, hLc]
    simp only
    rw [φ.left_inv hsrc]
  have hsource : (⟨p₀.1, R p₀.2 p₀.1⟩ : TotalSpace (TensorRSModel 0 a ℝ E)
      (fun y : M => TensorRSSpace 0 a I y)) ∈
      (trivializationAt (TensorRSModel 0 a ℝ E) (fun y : M => TensorRSSpace 0 a I y) α).source := by
    rw [Bundle.Trivialization.mem_source]
    exact mem_trivAt_baseSet_of_chart hxs
  have hfib : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, TensorRSModel 0 a ℝ E) ∞
      (fun p : M × ℝ => ((trivializationAt (TensorRSModel 0 a ℝ E)
        (fun y : M => TensorRSSpace 0 a I y) α) ⟨p.1, R p.2 p.1⟩).2) (U ×ˢ Icc 0 T) p₀ :=
    hF.congr_of_eventuallyEq (Filter.eventually_of_mem self_mem_nhdsWithin hval)
      (hval p₀ ⟨hαU, ht₀⟩)
  have h := (Bundle.Trivialization.contMDiffWithinAt_iff (IM := I.prod 𝓘(ℝ, ℝ)) (n := ∞)
    (f := fun p : M × ℝ => (⟨p.1, R p.2 p.1⟩ :
      TotalSpace (TensorRSModel 0 a ℝ E) (fun y : M => TensorRSSpace 0 a I y)))
    (s := U ×ˢ Icc 0 T) (x₀ := p₀)
    (e := trivializationAt (TensorRSModel 0 a ℝ E) (fun y : M => TensorRSSpace 0 a I y) α)
    hsource).mpr ⟨contMDiffWithinAt_fst, hfib⟩
  have hnhd : U ×ˢ (Set.univ : Set ℝ) ∈ 𝓝 p₀ :=
    (hUo.prod isOpen_univ).mem_nhds ⟨hαU, Set.mem_univ _⟩
  have hset : U ×ˢ Icc 0 T = ((Set.univ : Set M) ×ˢ Icc 0 T) ∩ U ×ˢ (Set.univ : Set ℝ) := by
    ext p; simp only [Set.mem_prod, Set.mem_inter_iff, Set.mem_univ, true_and, and_true]; tauto
  rw [hset] at h
  exact (contMDiffWithinAt_inter hnhd).mp h

theorem rawJoint_of_chart {a : ℕ} {R : ℝ → (x : M) → TensorRSSpace 0 a I x}
    (hR : ∀ α : M, ∃ ε > 0, Metric.ball (extChartAt I α α) ε ⊆ (extChartAt I α).target ∧
      ContDiffOn ℝ ∞ (fun q : ℝ × E => (trivAt I M 0 a α).continuousLinearMapAt ℝ
        ((extChartAt I α).symm q.2) (R q.1 ((extChartAt I α).symm q.2)))
        (Icc 0 T ×ˢ Metric.ball (extChartAt I α α) ε)) :
    RawJoint 0 a (Icc 0 T) R := by
  refine rawJoint_of_chart_cover fun x => ?_
  obtain ⟨ε, hε, hb, hc⟩ := hR x
  exact ⟨x, ε, hε, mem_chart_source H x, Metric.mem_ball_self hε, hb, hc⟩

variable (T) in
open Classical in
/-- A jointly smooth family of sections, as a family of smooth tensor fields (zero outside
`[0,T]` or if the family is not jointly smooth). -/
def secFam {a : ℕ} (R : ℝ → (x : M) → TensorRSSpace 0 a I x) (t : ℝ) : SmoothCcTensor g 0 a :=
  if h : RawJoint 0 a (Icc 0 T) R ∧ t ∈ Icc 0 T then
    { toSection := ⟨fun x => R t x, h.1.slice h.2⟩
      hasCompactSupport := HasCompactSupport.of_compactSpace _ }
  else 0

theorem secFam_toSection {a : ℕ} {R : ℝ → (x : M) → TensorRSSpace 0 a I x}
    (hR : RawJoint 0 a (Icc 0 T) R) {t : ℝ} (ht : t ∈ Icc 0 T) (x : M) :
    (secFam (g := g) T R t).toSection x = R t x := by
  unfold secFam
  rw [dif_pos ⟨hR, ht⟩]
  rfl

theorem jointlySmoothOn_secFam {a : ℕ} {R : ℝ → (x : M) → TensorRSSpace 0 a I x}
    (hR : RawJoint 0 a (Icc 0 T) R) : JointlySmoothOn g 0 a (Icc 0 T) (secFam T R) :=
  hR.congr fun q hq => by rw [secFam_toSection hR hq.2]

/-- The continuous representative of `v` as a family of sections. -/
def repSec (v : ParabolicSpace g s p m T) (t : ℝ) (x : M) : TensorRSSpace 0 s I x :=
  TensorRSSpace.ofModel (evalJet g s p m T 0 0 t x v)

/-- **The continuous representative is smooth** (assembly): if the representative is spatially smooth
near every chart centre with spatial derivatives continuous in `(t, y)` (`exists_spatialSmooth`
provides this from Angenent's trick), and it satisfies an evolution equation `∂ₜ v̂ = G` in charts
whose right side has the regularity of `v̂`, then it is jointly smooth. -/
theorem exists_smooth_rep_of_spatial (hT : 0 < T) (v : ParabolicSpace g s p m T)
    (hspat : ∀ α : M, ∃ ε > 0, Metric.ball (extChartAt I α α) ε ⊆ (extChartAt I α).target ∧
      ∀ n, SpatialReg.SpC 0 (Icc 0 T) (Metric.ball (extChartAt I α α) ε) n
        (TensorRSModel 0 s ℝ E) (repChart g s p m T α v))
    (htime : ∀ α : M, ∀ ε > 0, Metric.ball (extChartAt I α α) ε ⊆ (extChartAt I α).target →
      ∃ G : ℝ → E → TensorRSModel 0 s ℝ E,
        (∀ t ∈ Icc (0 : ℝ) T, ∀ y ∈ Metric.ball (extChartAt I α α) ε,
          HasDerivWithinAt (fun τ => repChart g s p m T α v τ y) (G t y) (Icc 0 T) t) ∧
        ∀ k, (∀ n, SpatialReg.SpC k (Icc 0 T) (Metric.ball (extChartAt I α α) ε) n
            (TensorRSModel 0 s ℝ E) (repChart g s p m T α v)) →
          ∀ n, SpatialReg.SpC k (Icc 0 T) (Metric.ball (extChartAt I α α) ε) n
            (TensorRSModel 0 s ℝ E) G) :
    ∃ (u : ℝ → SmoothCcTensor g 0 s) (_ : JointlySmoothOn g 0 s (Icc 0 T) u),
      ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
        evalJet g s p m T 0 0 t x v = TensorRSSpace.toModel ((u t).toSection x) := by
  have hR : RawJoint 0 s (Icc 0 T) (repSec v) := by
    refine rawJoint_of_chart fun α => ?_
    obtain ⟨ε, hε, hsub, h0⟩ := hspat α
    obtain ⟨G, hG, hGk⟩ := htime α ε hε hsub
    exact ⟨ε, hε, hsub, SpatialReg.contDiffOn_of_evolution hT Metric.isOpen_ball h0 hG hGk⟩
  refine ⟨secFam T (repSec v), jointlySmoothOn_secFam hR, fun t ht x => ?_⟩
  rw [secFam_toSection hR ht, repSec, TensorRSSpace.toModel_ofModel]

/-- **The continuous representative is smooth** (cover version): as `exists_smooth_rep_of_spatial`,
but the chart data may be taken at any centre `α` whose chart ball contains `x` (so that finitely many
centres suffice). -/
theorem exists_smooth_rep_cover (hT : 0 < T) (v : ParabolicSpace g s p m T)
    (hcov : ∀ x : M, ∃ α : M, ∃ ε > 0, x ∈ (chartAt H α).source ∧
      extChartAt I α x ∈ Metric.ball (extChartAt I α α) ε ∧
      Metric.ball (extChartAt I α α) ε ⊆ (extChartAt I α).target ∧
      (∀ n, SpatialReg.SpC 0 (Icc 0 T) (Metric.ball (extChartAt I α α) ε) n
        (TensorRSModel 0 s ℝ E) (repChart g s p m T α v)) ∧
      ∃ G : ℝ → E → TensorRSModel 0 s ℝ E,
        (∀ t ∈ Icc (0 : ℝ) T, ∀ y ∈ Metric.ball (extChartAt I α α) ε,
          HasDerivWithinAt (fun τ => repChart g s p m T α v τ y) (G t y) (Icc 0 T) t) ∧
        ∀ k, (∀ n, SpatialReg.SpC k (Icc 0 T) (Metric.ball (extChartAt I α α) ε) n
            (TensorRSModel 0 s ℝ E) (repChart g s p m T α v)) →
          ∀ n, SpatialReg.SpC k (Icc 0 T) (Metric.ball (extChartAt I α α) ε) n
            (TensorRSModel 0 s ℝ E) G) :
    ∃ (u : ℝ → SmoothCcTensor g 0 s) (_ : JointlySmoothOn g 0 s (Icc 0 T) u),
      ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
        evalJet g s p m T 0 0 t x v = TensorRSSpace.toModel ((u t).toSection x) := by
  have hR : RawJoint 0 s (Icc 0 T) (repSec v) := by
    refine rawJoint_of_chart_cover fun x => ?_
    obtain ⟨α, ε, hε, hxs, hxb, hsub, h0, G, hG, hGk⟩ := hcov x
    exact ⟨α, ε, hε, hxs, hxb, hsub,
      SpatialReg.contDiffOn_of_evolution hT Metric.isOpen_ball h0 hG hGk⟩
  refine ⟨secFam T (repSec v), jointlySmoothOn_secFam hR, fun t ht x => ?_⟩
  rw [secFam_toSection hR ht, repSec, TensorRSSpace.toModel_ofModel]

/-- **The smooth representative from Angenent's trick**: as `exists_smooth_rep_of_spatial`, with the
spatial smoothness derived from the smoothness of `σ ↦ Π_σ v` (`exists_spatialSmooth`). -/
theorem exists_smooth_rep (hT : 0 < T) (hm : 0 < m)
    (hk : Module.finrank ℝ E / 2 + 1 ≤ 2 * p * (m - 1)) (v : ParabolicSpace g s p m T)
    (hflow : ∀ α : M, ∃ r > 0,
      ∃ B : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯,
        Metric.closedBall (extChartAt I α α) r ⊆ (extChartAt I α).target ∧
        (∀ y ∈ Metric.closedBall (extChartAt I α α) r, ∀ k,
          trivToE I α ((extChartAt I α).symm y) (B k ((extChartAt I α).symm y)) =
            Module.finBasis ℝ E k) ∧
        ∃ ρ > 0, ContDiffOn ℝ ∞ (fun σ => iterPullExt g s p m T B σ v) (Metric.ball 0 ρ))
    (htime : ∀ α : M, ∀ ε > 0, Metric.ball (extChartAt I α α) ε ⊆ (extChartAt I α).target →
      ∃ G : ℝ → E → TensorRSModel 0 s ℝ E,
        (∀ t ∈ Icc (0 : ℝ) T, ∀ y ∈ Metric.ball (extChartAt I α α) ε,
          HasDerivWithinAt (fun τ => repChart g s p m T α v τ y) (G t y) (Icc 0 T) t) ∧
        ∀ k, (∀ n, SpatialReg.SpC k (Icc 0 T) (Metric.ball (extChartAt I α α) ε) n
            (TensorRSModel 0 s ℝ E) (repChart g s p m T α v)) →
          ∀ n, SpatialReg.SpC k (Icc 0 T) (Metric.ball (extChartAt I α α) ε) n
            (TensorRSModel 0 s ℝ E) G) :
    ∃ (u : ℝ → SmoothCcTensor g 0 s) (_ : JointlySmoothOn g 0 s (Icc 0 T) u),
      ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
        evalJet g s p m T 0 0 t x v = TensorRSSpace.toModel ((u t).toSection x) := by
  refine exists_smooth_rep_of_spatial hT v (fun α => ?_) htime
  obtain ⟨r, hr, B, hball, hB, ρ, hρ, hfl⟩ := hflow α
  obtain ⟨ε, hε, hsub, hS⟩ := exists_spatialSmooth (g := g) (s := s) (p := p) (m := m) (T := T) hT hm hk α hr hball hB hρ
  exact ⟨ε, hε, hsub, hS v hfl⟩

end SmoothRep

end ShortTime
