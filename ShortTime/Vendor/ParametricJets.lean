import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.CovariantDerivativeBounds.ChartPullbackFormula
import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.CovariantDerivativeBounds.SlotCorrection.Kernel
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Defs
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.ChartGeometry.GoodSetMeasure
import DifferentialGeometry.Bundle.ContinuousLinearMapSection.ParametricSmoothness
import DifferentialGeometry.Analysis.Sobolev.Embedding.CovariantDerivative.Cm
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Inner.TensorRSContRiemannianBundle
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberNorm.Inner
import DifferentialGeometry.Geometry.Metric.TensorInner.TensorRS.RiemannianBundle
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Joint smoothness of covariant derivatives of time-dependent families (vendored)

Verbatim copies of three files of the library `qinz1yang/differential-geometry` (v0.1.3),
`Analysis/Spectral/Tensor/CovGrad/Parametric/{ChartRepresentation, JointSmoothness, JetBounds}.lean`,
and the lemmas `joint_rs_add`, `joint_rs_sub` of `Parametric/JetIntegral.lean`,
moved to the namespace `ShortTime.Vendor`.

The library versions import two modules they do not use (`MetricPerturbationPath.Basic` and
`Parametric.CoefficientIntegral`), which pull in about 400 further modules. Copying the three files
with only the imports they need keeps the build of this project small. Only the header lines
(imports, `open`s, namespaces) were changed.

Main results: `covGrad_step_jointContMDiffOn`, `covGrad_iter_joint` (covariant derivatives of a
jointly smooth family are jointly smooth) and `joint_jet_bdd` (uniform bounds on compact time sets).
-/

section ChartRepresentation

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection


noncomputable section


open Bundle Manifold Set Filter MeasureTheory
open scoped Manifold Topology ContDiff BigOperators Interval

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.TensorRSNabla

namespace ShortTime.Vendor

open DifferentialGeometry DifferentialGeometry.Analysis DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance tensorRSModelNormedAddCommGroup_local0 (r s : ℕ) :
    NormedAddCommGroup (TensorRSModel r s ℝ E) :=
  Tensor0SBundle.tensorRSModelNormedAddCommGroup r s

private local instance tensorRSModelNormedSpace_local0 (r s : ℕ) :
    NormedSpace ℝ (TensorRSModel r s ℝ E) :=
  Tensor0SBundle.tensorRSModelNormedSpace r s

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem chartRepr_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : ℝ → SmoothCcTensor g₀ r s)
    (S : Set ℝ) (α : M)
    (hF : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) p.1
        ((F p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, TensorRSModel r s ℝ E) ∞
      (fun p : M × ℝ =>
        DifferentialGeometry.Geometry.Connection.tensorRSChartESectionRepr
          (I := I) r s α (fun z : M => (F p.2).toSection z) p.1)
      (((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).baseSet) ×ˢ S) := by
  have hrepr :
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, TensorRSModel r s ℝ E) ∞
        (fun p : M × ℝ =>
          ((trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α)
            ⟨p.1, (F p.2).toSection p.1⟩).2)
        (((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).baseSet) ×ˢ S) := by
    intro p hp
    obtain ⟨hx, hs⟩ := hp
    have hsub : (((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).baseSet) ×ˢ S) ⊆
        ((Set.univ : Set M) ×ˢ S) := by
      intro q hq; exact ⟨Set.mem_univ _, hq.2⟩
    have hFwithin : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
        (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
        (fun p : M × ℝ => (⟨p.1, (F p.2).toSection p.1⟩ :
          TotalSpace (TensorRSModel r s ℝ E)
            (fun z : M => TensorRSSpace r s I z)))
        (((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).baseSet) ×ˢ S) p :=
      (hF p (hsub ⟨hx, hs⟩)).mono hsub
    have hsource : (⟨p.1, (F p.2).toSection p.1⟩ :
        TotalSpace (TensorRSModel r s ℝ E)
          (fun z : M => TensorRSSpace r s I z)) ∈
        (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).source := by
      rw [Bundle.Trivialization.mem_source]
      exact hx
    exact ((Bundle.Trivialization.contMDiffWithinAt_iff
      (IM := I.prod 𝓘(ℝ, ℝ)) (n := ∞)
      (f := fun p : M × ℝ => (⟨p.1, (F p.2).toSection p.1⟩ :
        TotalSpace (TensorRSModel r s ℝ E)
          (fun z : M => TensorRSSpace r s I z)))
      (s := ((trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).baseSet) ×ˢ S)
      (x₀ := p)
      (e := trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α) hsource).mp hFwithin).2
  refine hrepr.congr ?_
  intro p hp
  obtain ⟨hx, _hs⟩ := hp
  rw [DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr_apply]
  change (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).linearMapAt ℝ p.1
      ((F p.2).toSection p.1) = _
  rw [Bundle.Trivialization.coe_linearMapAt_of_mem _ hx]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem chartRepr_euclid_jointContDiffWithinAt
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : ℝ → SmoothCcTensor g₀ r s)
    (S : Set ℝ) (α : M)
    (hF : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) p.1
        ((F p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S))
    {t₀ : ℝ} {y₀ : E} (ht₀ : t₀ ∈ S)
    (hy₀ : y₀ ∈ (extChartAt I α).target) :
    ContDiffWithinAt ℝ ∞
      (fun q : ℝ × E => DifferentialGeometry.Geometry.Connection.tensorRSChartESectionRepr
        (I := I) r s α (fun z : M => (F q.1).toSection z) ((extChartAt I α).symm q.2))
      (S ×ˢ (extChartAt I α).target) (t₀, y₀) := by
  classical
  have hbase := chartRepr_jointContMDiffOn (I := I) g₀ r s F S α hF
  have hbaseSet_eq :
      (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).baseSet =
        (chartAt H α).source := by
    change ((trivializationAt (Tensor0SBundle.Tensor0SModel r ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace r I y) α).baseSet) ∩
        ((trivializationAt (Tensor0SBundle.Tensor0SModel s ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace s I y) α).baseSet) =
          (chartAt H α).source
    change (trivializationAt E (TangentSpace I) α).baseSet ∩
          (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source
    rw [Set.inter_self]
    rfl
  rw [hbaseSet_eq] at hbase
  set φ := extChartAt I α with hφ
  have hx0src : φ.symm y₀ ∈ (chartAt H α).source := by
    have := φ.map_target hy₀
    rwa [extChartAt_source] at this
  have hsymm_on : ContMDiffOn 𝓘(ℝ, E) I ∞ φ.symm φ.target :=
    contMDiffOn_extChartAt_symm (I := I) (n := ∞) (x := α)
  have hmove : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun q : ℝ × E => ((φ.symm q.2 : M), q.1))
      (S ×ˢ φ.target) (t₀, y₀) := by
    refine ContMDiffWithinAt.prodMk ?_ ?_
    · have hsymm_w : ContMDiffWithinAt 𝓘(ℝ, E) I ∞ φ.symm φ.target y₀ := hsymm_on y₀ hy₀
      exact hsymm_w.comp (t₀, y₀) contMDiffWithinAt_snd (fun q hq => hq.2)
    · exact contMDiffWithinAt_fst
  have hbase_w : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, TensorRSModel r s ℝ E) ∞
      (fun p : M × ℝ => DifferentialGeometry.Geometry.Connection.tensorRSChartESectionRepr
        (I := I) r s α (fun z : M => (F p.2).toSection z) p.1)
      ((chartAt H α).source ×ˢ S) ((φ.symm y₀ : M), t₀) :=
    hbase ((φ.symm y₀ : M), t₀) ⟨hx0src, ht₀⟩
  have hmaps : Set.MapsTo (fun q : ℝ × E => ((φ.symm q.2 : M), q.1))
      (S ×ˢ φ.target) ((chartAt H α).source ×ˢ S) := by
    intro q hq
    obtain ⟨hqS, hqtgt⟩ := hq
    refine ⟨?_, hqS⟩
    have := φ.map_target hqtgt
    rwa [extChartAt_source] at this
  have hcomp : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E))
      𝓘(ℝ, TensorRSModel r s ℝ E) ∞
      (fun q : ℝ × E => DifferentialGeometry.Geometry.Connection.tensorRSChartESectionRepr
        (I := I) r s α (fun z : M => (F q.1).toSection z) (φ.symm q.2))
      (S ×ˢ φ.target) (t₀, y₀) :=
    hbase_w.comp (t₀, y₀) hmove hmaps
  have hself : ContMDiffWithinAt 𝓘(ℝ, ℝ × E) 𝓘(ℝ, TensorRSModel r s ℝ E) ∞
      (fun q : ℝ × E => DifferentialGeometry.Geometry.Connection.tensorRSChartESectionRepr
        (I := I) r s α (fun z : M => (F q.1).toSection z) (φ.symm q.2))
      (S ×ˢ φ.target) (t₀, y₀) := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hcomp
    exact hcomp
  rw [contMDiffWithinAt_iff_contDiffWithinAt] at hself
  exact hself


end ShortTime.Vendor

end

end ChartRepresentation

section JointSmoothness

open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection


noncomputable section


open Bundle Manifold Set Filter MeasureTheory
open scoped Manifold Topology ContDiff BigOperators Interval

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.TensorRSNabla

namespace ShortTime.Vendor

open DifferentialGeometry DifferentialGeometry.Analysis DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance tensorRSModelNormedAddCommGroup_local1 (r s : ℕ) :
    NormedAddCommGroup (TensorRSModel r s ℝ E) :=
  Tensor0SBundle.tensorRSModelNormedAddCommGroup r s

private local instance tensorRSModelNormedSpace_local1 (r s : ℕ) :
    NormedSpace ℝ (TensorRSModel r s ℝ E) :=
  Tensor0SBundle.tensorRSModelNormedSpace r s

omit [CompactSpace M] in
omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private theorem covApply_chartRepr_euclid_jointContDiffWithinAt
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : ℝ → SmoothCcTensor g₀ r s)
    (S : Set ℝ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hF : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) p.1
        ((F p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S))
    {t₀ : ℝ} {b : M} (ht₀ : t₀ ∈ S)
    (hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    ContDiffWithinAt ℝ ∞
      (fun q : ℝ × E =>
        DifferentialGeometry.Geometry.Connection.tensorRSChartESectionRepr (I := I) r s α
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
            B.toFun (fun z : M => (F q.1).toSection z)) ((extChartAt I α).symm q.2))
      (S ×ˢ (extChartAt I α).target) (t₀, extChartAt I α b) := by
  classical
  set φ := extChartAt I α with hφ
  set chartRep : ℝ → E → TensorRSModel r s ℝ E :=
    fun t y => DifferentialGeometry.Geometry.Connection.tensorRSChartESectionRepr (I := I) r s α
      (fun z : M => (F t).toSection z) (φ.symm y) with hchartRep
  set U : Set E := φ '' chartLeviCivitaGoodSet (I := I) α with hU_def
  have hU_open : IsOpen U := chartLeviCivitaGoodSet_image_isOpen (I := I) α
  have hx_mem : φ b ∈ U := ⟨b, hb_good, rfl⟩
  have hb_source : b ∈ (chartAt H α).source :=
    chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hb_good
  have hyb_target : φ b ∈ φ.target :=
    φ.map_source (by rw [hφ, extChartAt_source]; exact hb_source)
  have hchartRep_w : ∀ y₀ : E, y₀ ∈ φ.target →
      ContDiffWithinAt ℝ ∞ (fun q : ℝ × E => chartRep q.1 q.2) (S ×ˢ φ.target) (t₀, y₀) := by
    intro y₀ hy₀
    exact chartRepr_euclid_jointContDiffWithinAt (I := I) g₀ r s F S α hF ht₀ hy₀
  have hB_on : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (T% (B.toFun : Π x : M, TangentSpace I x))
      (chartLeviCivitaGoodSet (I := I) α) := B.contMDiff.contMDiffOn
  have hvec_cd : ContDiffOn ℝ ∞
      (DifferentialGeometry.Geometry.Connection.chartESectionRepr (I := I) α B.toFun ∘ φ.symm)
        U :=
    chartE_pullback_contDiffOn_goodSet (I := I) α hB_on
  have hvec_at : ContDiffAt ℝ ∞
      (DifferentialGeometry.Geometry.Connection.chartESectionRepr (I := I) α B.toFun ∘ φ.symm)
      (φ b) :=
    (hvec_cd (φ b) hx_mem).contDiffAt (hU_open.mem_nhds hx_mem)
  have hvec_q : ContDiffWithinAt ℝ ∞
      (fun q : ℝ × E => DifferentialGeometry.Geometry.Connection.chartESectionRepr
        (I := I) α B.toFun (φ.symm q.2)) (S ×ˢ φ.target) (t₀, φ b) :=
    (hvec_at.comp (t₀, φ b) contDiffAt_snd).contDiffWithinAt
  have h_intrinsic : ContDiffWithinAt ℝ ∞
      (fun q : ℝ × E => fderiv ℝ (fun y' : E => chartRep q.1 y') q.2
        (DifferentialGeometry.Geometry.Connection.chartESectionRepr (I := I) α B.toFun
          (φ.symm q.2)))
      (S ×ˢ φ.target) (t₀, φ b) := by
    have huncurry : ContDiffWithinAt ℝ ∞
        (Function.uncurry (fun (q : ℝ × E) (y' : E) => chartRep q.1 y'))
        ((S ×ˢ φ.target) ×ˢ φ.target)
        ((t₀, φ b), (fun q : ℝ × E => q.2) (t₀, φ b)) := by
      have hbrick : ContDiffWithinAt ℝ ∞ (fun r : ℝ × E => chartRep r.1 r.2)
          (S ×ˢ φ.target) (t₀, φ b) := hchartRep_w (φ b) hyb_target
      have hproj : ContDiffWithinAt ℝ ∞
          (fun r : (ℝ × E) × E => (r.1.1, r.2))
          ((S ×ˢ φ.target) ×ˢ φ.target) ((t₀, φ b), φ b) :=
        (contDiffWithinAt_fst.fst).prodMk contDiffWithinAt_snd
      refine hbrick.comp ((t₀, φ b), φ b) hproj ?_
      rintro ⟨⟨t, y⟩, y'⟩ ⟨⟨ht, _⟩, hy'⟩
      exact ⟨ht, hy'⟩
    have hg : ContDiffWithinAt ℝ ∞ (fun q : ℝ × E => q.2) (S ×ˢ φ.target) (t₀, φ b) :=
      contDiffWithinAt_snd
    have htgt_open : IsOpen φ.target := isOpen_extChartAt_target (I := I) α
    have hud : UniqueDiffOn ℝ φ.target := htgt_open.uniqueDiffOn
    have h_le : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by rw [ENat.coe_top_add_one]
    have hsub : (S ×ˢ φ.target) ⊆ (fun q : ℝ × E => q.2) ⁻¹' φ.target := by
      intro q hq; exact hq.2
    have hfdw := ContDiffWithinAt.fderivWithin huncurry hg hud h_le ⟨ht₀, hyb_target⟩ hsub
    have hfd_eq : ContDiffWithinAt ℝ ∞
        (fun q : ℝ × E => fderiv ℝ (fun y' : E => chartRep q.1 y') q.2) (S ×ˢ φ.target)
          (t₀, φ b) := by
      refine hfdw.congr_of_eventuallyEq ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with q hq
        exact (fderivWithin_of_isOpen htgt_open hq.2).symm
      · exact (fderivWithin_of_isOpen htgt_open hyb_target).symm
    exact hfd_eq.clm_apply hvec_q
  have hchartRep_q : ContDiffWithinAt ℝ ∞ (fun q : ℝ × E => chartRep q.1 q.2)
      (S ×ˢ φ.target) (t₀, φ b) := hchartRep_w (φ b) hyb_target
  have h_input : ∀ k : Fin r, ContDiffWithinAt ℝ ∞
      (fun q : ℝ × E =>
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
          (φ.symm q.2)
          (DifferentialGeometry.Geometry.Connection.chartTensorRSInputSlotCorrection (I := I) r s g₀
            α
            (fun z : M => (F q.1).toSection z) B.toFun (φ.symm q.2) k))
      (S ×ˢ φ.target) (t₀, φ b) := by
    intro k
    obtain ⟨Ker, hKer, hK_at⟩ :
        ∃ Ker : E → (TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E),
          (Ker = fun y : E => DifferentialGeometry.Analysis.Elliptic.inputSlotChartKernel
            (I := I) g₀ r s α B.toFun k (φ.symm y)) ∧
          ContDiffAt ℝ ∞ Ker (φ b) :=
      ⟨_, rfl, inputSlotChartKernel_contDiffAt_chart_pulled (I := I) (M := M) g₀ r s α B k hb_good⟩
    have hK_q : ContDiffWithinAt ℝ ∞ (fun q : ℝ × E => Ker q.2) (S ×ˢ φ.target) (t₀, φ b) :=
      (ContDiffAt.comp (t₀, φ b) hK_at contDiffAt_snd).contDiffWithinAt
    have h_apply : ContDiffWithinAt ℝ ∞
        (fun q : ℝ × E => Ker q.2 (chartRep q.1 q.2)) (S ×ˢ φ.target) (t₀, φ b) :=
      hK_q.clm_apply hchartRep_q
    refine h_apply.congr_of_eventuallyEq ?_ ?_
    · have hUprod : (Set.univ : Set ℝ) ×ˢ U ∈ nhds (t₀, φ b) :=
        (isOpen_univ.prod hU_open).mem_nhds ⟨Set.mem_univ _, hx_mem⟩
      refine Filter.eventually_of_mem (nhdsWithin_le_nhds hUprod) ?_
      rintro ⟨t, y⟩ hq
      have hy : y ∈ U := hq.2
      obtain ⟨x', hx'_good, hx'y⟩ := hy
      have hx'_source : x' ∈ (chartAt H α).source :=
        chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hx'_good
      have hx'_extsrc : x' ∈ φ.source := by rw [hφ, extChartAt_source]; exact hx'_source
      have hx'_inv : φ.symm y = x' := by rw [← hx'y]; exact φ.left_inv hx'_extsrc
      change _ = Ker y (chartRep t y)
      rw [hKer, hchartRep]
      simp only []
      exact (chartTensorRSInputSlotCorrection_chart_kernel_factorization (I := I) (M := M) g₀ r s α
        (fun b' : M => (F t).toSection b') B.toFun
        (b := φ.symm y) (by rw [hx'_inv]; exact hx'_source) k)
    · have hgood_inv : φ.symm (φ b) = b := φ.left_inv (by rw [hφ, extChartAt_source]; exact hb_source)
      change _ = Ker (φ b) (chartRep t₀ (φ b))
      rw [hKer, hchartRep]
      simp only []
      exact (chartTensorRSInputSlotCorrection_chart_kernel_factorization (I := I) (M := M) g₀ r s α
        (fun b' : M => (F t₀).toSection b') B.toFun
        (b := φ.symm (φ b)) (by rw [hgood_inv]; exact hb_source) k)
  have h_output : ∀ l : Fin s, ContDiffWithinAt ℝ ∞
      (fun q : ℝ × E =>
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
          (φ.symm q.2)
          (DifferentialGeometry.Geometry.Connection.chartTensorRSOutputSlotCorrection (I := I) r s
            g₀ α
            (fun z : M => (F q.1).toSection z) B.toFun (φ.symm q.2) l))
      (S ×ˢ φ.target) (t₀, φ b) := by
    intro l
    obtain ⟨Ker, hKer, hK_at⟩ :
        ∃ Ker : E → (TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E),
          (Ker = fun y : E => DifferentialGeometry.Analysis.Elliptic.outputSlotChartKernel
            (I := I) g₀ r s α B.toFun l (φ.symm y)) ∧
          ContDiffAt ℝ ∞ Ker (φ b) :=
      ⟨_, rfl, outputSlotChartKernel_contDiffAt_chart_pulled (I := I) (M := M) g₀ r s α B l hb_good⟩
    have hK_q : ContDiffWithinAt ℝ ∞ (fun q : ℝ × E => Ker q.2) (S ×ˢ φ.target) (t₀, φ b) :=
      (ContDiffAt.comp (t₀, φ b) hK_at contDiffAt_snd).contDiffWithinAt
    have h_apply : ContDiffWithinAt ℝ ∞
        (fun q : ℝ × E => Ker q.2 (chartRep q.1 q.2)) (S ×ˢ φ.target) (t₀, φ b) :=
      hK_q.clm_apply hchartRep_q
    refine h_apply.congr_of_eventuallyEq ?_ ?_
    · have hUprod : (Set.univ : Set ℝ) ×ˢ U ∈ nhds (t₀, φ b) :=
        (isOpen_univ.prod hU_open).mem_nhds ⟨Set.mem_univ _, hx_mem⟩
      refine Filter.eventually_of_mem (nhdsWithin_le_nhds hUprod) ?_
      rintro ⟨t, y⟩ hq
      have hy : y ∈ U := hq.2
      obtain ⟨x', hx'_good, hx'y⟩ := hy
      have hx'_source : x' ∈ (chartAt H α).source :=
        chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hx'_good
      have hx'_extsrc : x' ∈ φ.source := by rw [hφ, extChartAt_source]; exact hx'_source
      have hx'_inv : φ.symm y = x' := by rw [← hx'y]; exact φ.left_inv hx'_extsrc
      change _ = Ker y (chartRep t y)
      rw [hKer, hchartRep]
      simp only []
      exact (chartTensorRSOutputSlotCorrection_chart_kernel_factorization (I := I) (M := M) g₀ r s α
        (fun b' : M => (F t).toSection b') B.toFun
        (b := φ.symm y) (by rw [hx'_inv]; exact hx'_source) l)
    · have hgood_inv : φ.symm (φ b) = b := φ.left_inv (by rw [hφ, extChartAt_source]; exact hb_source)
      change _ = Ker (φ b) (chartRep t₀ (φ b))
      rw [hKer, hchartRep]
      simp only []
      exact (chartTensorRSOutputSlotCorrection_chart_kernel_factorization (I := I) (M := M) g₀ r s α
        (fun b' : M => (F t₀).toSection b') B.toFun
        (b := φ.symm (φ b)) (by rw [hgood_inv]; exact hb_source) l)
  have h_sum : ContDiffWithinAt ℝ ∞
      (fun q : ℝ × E =>
        fderiv ℝ (fun y' : E => chartRep q.1 y') q.2
          (DifferentialGeometry.Geometry.Connection.chartESectionRepr (I := I) α B.toFun
            (φ.symm q.2))
        + (∑ k : Fin r,
            (trivializationAt (TensorRSModel r s ℝ E)
                (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
              (φ.symm q.2)
              (DifferentialGeometry.Geometry.Connection.chartTensorRSInputSlotCorrection (I := I) r
                s g₀ α
                (fun z : M => (F q.1).toSection z) B.toFun (φ.symm q.2) k))
        - (∑ l : Fin s,
            (trivializationAt (TensorRSModel r s ℝ E)
                (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
              (φ.symm q.2)
              (DifferentialGeometry.Geometry.Connection.chartTensorRSOutputSlotCorrection (I := I) r
                s g₀ α
                (fun z : M => (F q.1).toSection z) B.toFun (φ.symm q.2) l)))
      (S ×ˢ φ.target) (t₀, φ b) := by
    refine (h_intrinsic.add (ContDiffWithinAt.sum (fun k _ => h_input k))).sub
      (ContDiffWithinAt.sum (fun l _ => h_output l))
  refine h_sum.congr_of_eventuallyEq ?_ ?_
  · have hUprod : (Set.univ : Set ℝ) ×ˢ U ∈ nhds (t₀, φ b) :=
      (isOpen_univ.prod hU_open).mem_nhds ⟨Set.mem_univ _, hx_mem⟩
    refine Filter.eventually_of_mem (nhdsWithin_le_nhds hUprod) ?_
    rintro ⟨t, y⟩ hq
    have hy : y ∈ U := hq.2
    obtain ⟨x', hx'_good, hx'y⟩ := hy
    have hx'_extsrc : x' ∈ φ.source := by
      rw [hφ, extChartAt_source]; exact chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hx'_good
    have hy_target : y ∈ φ.target := hx'y ▸ φ.map_source hx'_extsrc
    have hy_good : φ.symm y ∈ chartLeviCivitaGoodSet (I := I) α := by
      rw [← hx'y, φ.left_inv hx'_extsrc]; exact hx'_good
    have hform := chart_pulled_covApply_explicit_formula_target_smoothCc (I := I) (M := M)
      g₀ r s α (F t) B hy_target hy_good
    change DifferentialGeometry.Geometry.Connection.tensorRSChartESectionRepr (I := I) r s α
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
          B.toFun (fun z : M => (F t).toSection z)) (φ.symm y) = _
    rw [hchartRep]
    simp only [Function.comp_apply] at hform
    exact hform
  · have hgood_inv : φ.symm (φ b) = b := φ.left_inv (by rw [hφ, extChartAt_source]; exact hb_source)
    have hform := chart_pulled_covApply_explicit_formula_target_smoothCc (I := I) (M := M)
      g₀ r s α (F t₀) B hyb_target (by rw [hgood_inv]; exact hb_good)
    change DifferentialGeometry.Geometry.Connection.tensorRSChartESectionRepr (I := I) r s α
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
          B.toFun (fun z : M => (F t₀).toSection z)) (φ.symm (φ b)) = _
    rw [hchartRep]
    simp only [Function.comp_apply] at hform
    exact hform

omit [CompactSpace M] in
omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private theorem covApply_chartRepr_manifold_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : ℝ → SmoothCcTensor g₀ r s)
    (S : Set ℝ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hF : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) p.1
        ((F p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, TensorRSModel r s ℝ E) ∞
      (fun p : M × ℝ =>
        DifferentialGeometry.Geometry.Connection.tensorRSChartESectionRepr (I := I) r s α
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
            B.toFun (fun z : M => (F p.2).toSection z)) p.1)
      ((chartAt H α).source ×ˢ S) := by
  classical
  set φ := extChartAt I α with hφ
  intro p hp
  obtain ⟨hpx, hps⟩ := hp
  have hpx_good : p.1 ∈ chartLeviCivitaGoodSet (I := I) α := by
    rw [chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α, extChartAt_source]; exact hpx
  have hEu := covApply_chartRepr_euclid_jointContDiffWithinAt (I := I) g₀ r s F S α B hF hps
    hpx_good
  have hmove : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ × E) ∞
      (fun q : M × ℝ => (q.2, φ q.1))
      ((chartAt H α).source ×ˢ S) p := by
    have hmoveOn : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞
        (fun q : M × ℝ => (q.2, φ q.1))
        ((chartAt H α).source ×ˢ S) := by
      refine ContMDiffOn.prodMk contMDiffOn_snd ?_
      exact (contMDiffOn_extChartAt (I := I) (x := α)).comp contMDiffOn_fst (fun q hq => hq.1)
    have hm := hmoveOn p ⟨hpx, hps⟩
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hm
    exact hm
  have hEuM : ContMDiffWithinAt 𝓘(ℝ, ℝ × E) 𝓘(ℝ, TensorRSModel r s ℝ E) ∞
      (fun q : ℝ × E =>
        DifferentialGeometry.Geometry.Connection.tensorRSChartESectionRepr (I := I) r s α
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
            B.toFun (fun z : M => (F q.1).toSection z)) (φ.symm q.2))
      (S ×ˢ φ.target) (p.2, φ p.1) := by
    rw [contMDiffWithinAt_iff_contDiffWithinAt]
    exact hEu
  have hmaps : Set.MapsTo (fun q : M × ℝ => (q.2, φ q.1))
      ((chartAt H α).source ×ˢ S) (S ×ˢ φ.target) := by
    intro q hq
    obtain ⟨hqx, hqs⟩ := hq
    refine ⟨hqs, ?_⟩
    exact φ.map_source (by rw [hφ, extChartAt_source]; exact hqx)
  have hcomp := hEuM.comp p hmove hmaps
  refine hcomp.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with q hq
    obtain ⟨hqx, _⟩ := hq
    have hqsrc : q.1 ∈ φ.source := by rw [hφ, extChartAt_source]; exact hqx
    simp only [Function.comp_apply]
    rw [φ.left_inv hqsrc]
  · simp only [Function.comp_apply]
    have hpsrc : p.1 ∈ φ.source := by rw [hφ, extChartAt_source]; exact hpx
    rw [φ.left_inv hpsrc]

omit [CompactSpace M] in
omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem covApply_section_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : ℝ → SmoothCcTensor g₀ r s)
    (S : Set ℝ)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hF : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) p.1
        ((F p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) p.1
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
          B.toFun (fun z : M => (F p.2).toSection z) p.1))
      ((Set.univ : Set M) ×ˢ S) := by
  classical
  refine contMDiffOn_of_locally_contMDiffOn ?_
  rintro ⟨x₀, s₀⟩ ⟨-, hs₀⟩
  refine ⟨(chartAt H x₀).source ×ˢ (Set.univ : Set ℝ),
    (chartAt H x₀).open_source.prod isOpen_univ,
    ⟨mem_chart_source H x₀, Set.mem_univ _⟩, ?_⟩
  set α : M := x₀ with hα
  have hsub_eq : ((Set.univ : Set M) ×ˢ S) ∩ ((chartAt H x₀).source ×ˢ (Set.univ : Set ℝ)) =
      (chartAt H x₀).source ×ˢ S := by
    ext ⟨y, u⟩
    simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, true_and, and_true]
    tauto
  rw [hsub_eq]
  have hCR : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, TensorRSModel r s ℝ E) ∞
      (fun p : M × ℝ =>
        DifferentialGeometry.Geometry.Connection.tensorRSChartESectionRepr (I := I) r s α
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
            B.toFun (fun z : M => (F p.2).toSection z)) p.1)
      ((chartAt H α).source ×ˢ S) :=
    covApply_chartRepr_manifold_jointContMDiffOn (I := I) g₀ r s F S α B hF
  intro p₀ hp₀
  obtain ⟨hx₀source, hs₀'⟩ := hp₀
  have hbaseSet : p₀.1 ∈ (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).baseSet := by
    change p₀.1 ∈ ((trivializationAt (Tensor0SBundle.Tensor0SModel r ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace r I y) α).baseSet) ∩
        ((trivializationAt (Tensor0SBundle.Tensor0SModel s ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace s I y) α).baseSet)
    refine ⟨?_, ?_⟩ <;>
      · change p₀.1 ∈ (trivializationAt E (TangentSpace I) α).baseSet
        rw [show (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source from
          TangentBundle.trivializationAt_baseSet (I := I) α]
        rw [hα]; exact hx₀source
  have hsource : (⟨p₀.1,
      covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
        B.toFun (fun z : M => (F p₀.2).toSection z) p₀.1⟩ :
      TotalSpace (TensorRSModel r s ℝ E)
        (fun z : M => TensorRSSpace r s I z)) ∈
      (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).source := by
    rw [Bundle.Trivialization.mem_source]; exact hbaseSet
  have hfib : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, TensorRSModel r s ℝ E) ∞
      (fun p : M × ℝ =>
        ((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α)
          ⟨p.1,
            covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
              B.toFun (fun z : M => (F p.2).toSection z) p.1⟩).2)
      ((chartAt H α).source ×ˢ S) p₀ := by
    refine (hCR p₀ ⟨hx₀source, hs₀'⟩).congr_of_eventuallyEq ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with p hp
      obtain ⟨hpx, _⟩ := hp
      have hpbase : p.1 ∈ (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).baseSet := by
        change p.1 ∈ ((trivializationAt (Tensor0SBundle.Tensor0SModel r ℝ E)
            (fun y : M => Tensor0SBundle.Tensor0SSpace r I y) α).baseSet) ∩
            ((trivializationAt (Tensor0SBundle.Tensor0SModel s ℝ E)
              (fun y : M => Tensor0SBundle.Tensor0SSpace s I y) α).baseSet)
        refine ⟨?_, ?_⟩ <;>
          · change p.1 ∈ (trivializationAt E (TangentSpace I) α).baseSet
            rw [show (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source from
              TangentBundle.trivializationAt_baseSet (I := I) α]
            exact hpx
      rw [DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr_apply,
        Bundle.Trivialization.continuousLinearMapAt_apply,
        Bundle.Trivialization.coe_linearMapAt_of_mem _ hpbase]
    · rw [DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr_apply,
        Bundle.Trivialization.continuousLinearMapAt_apply,
        Bundle.Trivialization.coe_linearMapAt_of_mem _ hbaseSet]
  refine ((Bundle.Trivialization.contMDiffWithinAt_iff
    (IM := I.prod 𝓘(ℝ, ℝ)) (n := ∞)
    (f := fun p : M × ℝ => (⟨p.1,
      covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
        B.toFun (fun z : M => (F p.2).toSection z) p.1⟩ :
      TotalSpace (TensorRSModel r s ℝ E)
        (fun z : M => TensorRSSpace r s I z)))
    (s := (chartAt H α).source ×ˢ S) (x₀ := p₀)
    (e := trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α) hsource).mpr
    ⟨contMDiffWithinAt_fst, hfib⟩)

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
theorem covGrad_step_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (r sIdx : ℕ)
    (Ψ : ℝ → SmoothCcTensor g₀ r sIdx) (S : Set ℝ)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r sIdx ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r sIdx ℝ E)
        (E := fun z : M => TensorRSSpace r sIdx I z) q.1 ((Ψ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r (sIdx + 1) ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r (sIdx + 1) ℝ E)
        (E := fun z : M => TensorRSSpace r (sIdx + 1) I z) q.1
        ((covGrad (I := I) (M := M) g₀ r sIdx (Ψ q.2)).toSection q.1))
      ((Set.univ : Set M) ×ˢ S) := by
  classical
  set φfield : ∀ p : M × ℝ, TangentSpace I p.1 →L[ℝ] TensorRSSpace r sIdx I p.1 :=
    fun p => tensorRSCovariantDerivative I M r sIdx (LeviCivita (I := I) g₀)
      (fun y : M => (Ψ p.2).toSection y) p.1 with hφfield
  have hCLM : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r sIdx ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] TensorRSModel r sIdx ℝ E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TensorRSSpace r sIdx I x) p.1 (φfield p))
      ((Set.univ : Set M) ×ˢ S) := by
    refine contMDiffOn_clm_section_of_apply (I := I)
      (F₁ := E) (V₁ := fun x : M => TangentSpace I x)
      (F₂ := TensorRSModel r sIdx ℝ E) (V₂ := fun x : M => TensorRSSpace r sIdx I x)
      (φ := φfield) (S := S) ?_
    intro Y
    have hYapply := covApply_section_jointContMDiffOn (I := I) g₀ r sIdx Ψ S Y hjoint
    refine hYapply.congr ?_
    rintro ⟨x, t⟩ -
    rfl
  have hcomp := (covGradBundleSmoothEquiv (I := I) (M := M) r
    sIdx).toDiffeomorph.contMDiff.comp_contMDiffOn
    hCLM
  refine hcomp.congr ?_
  rintro ⟨x, t⟩ -
  rw [Function.comp_apply,
    covGradBundleSmoothEquiv_toDiffeomorph_apply (I := I) (M := M) r sIdx x (φfield (x, t))]
  rw [covGrad_toSection_apply]


end ShortTime.Vendor

end

end JointSmoothness

section JetBounds

open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set Filter MeasureTheory
open scoped Manifold Topology ContDiff

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.TensorRSNabla

namespace ShortTime.Vendor

open DifferentialGeometry DifferentialGeometry.Analysis DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M] in
omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem joint_riemannianFiberNormSq_cont
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s) {S K : Set ℝ}
    (hKS : K ⊆ S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) p.1
        ((Φ p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ContinuousOn (fun p : ℝ × M =>
      riemannianFiberNormSq (I := I) (M := M) g₀ r s p.2
        ((Φ p.1).toSection p.2))
      (K ×ˢ (Set.univ : Set M)) := by
  have hsub : (K ×ˢ (Set.univ : Set M)) ⊆
      (fun p : ℝ × M => (p.2, p.1)) ⁻¹' ((Set.univ : Set M) ×ˢ S) := by
    rintro ⟨t, x⟩ ⟨ht, -⟩
    exact ⟨Set.mem_univ x, hKS ht⟩
  have hswap : Continuous (fun p : ℝ × M => (p.2, p.1)) := by
    fun_prop
  have hv : ContinuousOn
      (fun p : ℝ × M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) p.2
        ((Φ p.1).toSection p.2))
      (K ×ˢ (Set.univ : Set M)) := by
    refine (hjoint.continuousOn.comp hswap.continuousOn hsub).congr ?_
    rintro ⟨t, x⟩ -
    rfl
  have hinner : ContinuousOn
      (fun p : ℝ × M => TotalSpace.mk'
        (TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E →L[ℝ] ℝ)
        (E := fun x : M =>
          TensorRSSpace r s I x →L[ℝ] TensorRSSpace r s I x →L[ℝ] ℝ)
        p.2
        (DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM
          (I := I) (M := M) g₀ r s p.2))
      (K ×ˢ (Set.univ : Set M)) :=
    ((tensorRSRiemannianInnerCLM_continuous
      (I := I) (M := M) g₀ r s).comp continuous_snd).continuousOn
  have happ : ContinuousOn
      (fun p : ℝ × M => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) p.2
        (DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM
          (I := I) (M := M) g₀ r s p.2
          ((Φ p.1).toSection p.2) ((Φ p.1).toSection p.2)))
      (K ×ˢ (Set.univ : Set M)) :=
    ContinuousOn.clm_bundle_apply₂
      (F₁ := TensorRSModel r s ℝ E) (F₂ := TensorRSModel r s ℝ E)
      (F₃ := ℝ) (b := fun p : ℝ × M => p.2) hinner hv hv
  have hscalar : ContinuousOn
      (fun p : ℝ × M =>
        DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM
          (I := I) (M := M) g₀ r s p.2
          ((Φ p.1).toSection p.2) ((Φ p.1).toSection p.2))
      (K ×ˢ (Set.univ : Set M)) := by
    intro p hp
    exact ((FiberBundle.continuousWithinAt_totalSpace ℝ
      (fun p : ℝ × M => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) p.2
        (DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM
          (I := I) (M := M) g₀ r s p.2
          ((Φ p.1).toSection p.2) ((Φ p.1).toSection p.2)))).mp
      (happ p hp)).2
  refine hscalar.congr ?_
  rintro ⟨t, x⟩ -
  simp only
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise
    (I := I) (M := M) g₀ r s x ((Φ t).toSection x),
    DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM_apply]

omit [CompactSpace M] [SigmaCompactSpace M] in
omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem covGrad_iter_joint
    (g₀ : SmoothRiemannianMetric I M) (r s i : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s) (S : Set ℝ)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) p.1
        ((Φ p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel r (s + i) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r (s + i) ℝ E)
        (E := fun z : M => TensorRSSpace r (s + i) I z) p.1
        ((iteratedCovGrad (I := I) g₀ r s i (Φ p.2)).toSection p.1))
      ((Set.univ : Set M) ×ˢ S) := by
  induction i with
  | zero => exact hjoint
  | succ j ih =>
      exact covGrad_step_jointContMDiffOn (I := I) (M := M) g₀ r (s + j)
        (fun t => iteratedCovGrad (I := I) g₀ r s j (Φ t)) S ih

omit [CompactSpace M] [SigmaCompactSpace M] in
omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem joint_jet_riemannianFiberNormSq
    (g₀ : SmoothRiemannianMetric I M) (r s i : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s) {S K : Set ℝ}
    (hKS : K ⊆ S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) p.1
        ((Φ p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ContinuousOn (fun p : ℝ × M =>
      riemannianFiberNormSq (I := I) (M := M) g₀ r (s + i) p.2
        ((iteratedCovGrad (I := I) g₀ r s i (Φ p.1)).toSection p.2))
      (K ×ˢ (Set.univ : Set M)) :=
  joint_riemannianFiberNormSq_cont (I := I) (M := M) g₀ r (s + i)
    (fun t => iteratedCovGrad (I := I) g₀ r s i (Φ t)) hKS
    (covGrad_iter_joint (I := I) (M := M) g₀ r s i Φ S hjoint)

omit [T2Space M] [SigmaCompactSpace M] in
private theorem joint_small
    (f : ℝ → M → ℝ) {S : Set ℝ} {t₀ : ℝ}
    (hS : S ∈ 𝓝 t₀)
    (hf : ContinuousOn (fun p : ℝ × M => f p.1 p.2)
      (S ×ˢ (Set.univ : Set M)))
    (hzero : ∀ x : M, f t₀ x = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in 𝓝 t₀, ∀ x : M, f t x < ε := by
  classical
  have hpatch (x : M) :
      ∃ V : Set ℝ, V ∈ 𝓝 t₀ ∧
        ∃ W : Set M, IsOpen W ∧ x ∈ W ∧
          ∀ t ∈ V, ∀ y ∈ W, f t y < ε := by
    let F : ℝ × M → ℝ := fun p => f p.1 p.2
    have hdom : S ×ˢ (Set.univ : Set M) ∈ 𝓝 (t₀, x) :=
      prod_mem_nhds hS Filter.univ_mem
    have hFcont : ContinuousAt F (t₀, x) := by
      simpa only [F] using
        (hf (t₀, x) ⟨mem_of_mem_nhds hS, Set.mem_univ x⟩).continuousAt hdom
    have hsmall : {p : ℝ × M | F p < ε} ∈ 𝓝 (t₀, x) := by
      exact hFcont.eventually_lt_const (by simpa only [F, hzero x] using hε)
    obtain ⟨V, W, hVOpen, htV, hWOpen, hxW, hVW⟩ :=
      mem_nhds_prod_iff'.mp hsmall
    refine ⟨V, hVOpen.mem_nhds htV, W, hWOpen, hxW, ?_⟩
    intro t ht y hy
    have hty : (t, y) ∈ V ×ˢ W := ⟨ht, hy⟩
    have h := hVW hty
    change f t y < ε at h
    exact h
  choose V hV W hWOpen hxW hloc using hpatch
  obtain ⟨F, _, hF⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set M)).elim_nhds_subcover W
      (fun x _ => (hWOpen x).mem_nhds (hxW x))
  have htime :
      ∀ᶠ t in 𝓝 t₀, ∀ x ∈ F, t ∈ V x := by
    exact
      (Finset.eventually_all
        (I := F)
        (l := 𝓝 t₀)
        (p := fun x t => t ∈ V x)).2
        (fun x _ => hV x)
  filter_upwards [htime] with t ht
  intro y
  obtain ⟨x, hxF, hyW⟩ := Set.mem_iUnion₂.mp (hF (Set.mem_univ y))
  exact hloc x t (ht x hxF) y hyW

omit [SigmaCompactSpace M] in
omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem joint_jet_small
    (g₀ : SmoothRiemannianMetric I M) (r s p : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s) {S : Set ℝ} {t₀ : ℝ}
    (hS : S ∈ 𝓝 t₀) (hzero : Φ t₀ = 0)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) q.1
        ((Φ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in 𝓝 t₀, ∀ i : ℕ, i ≤ p → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ r (s + i) x
        ((iteratedCovGrad (I := I) g₀ r s i (Φ t)).toSection x) < ε := by
  classical
  have hiter0 (i : ℕ) :
      iteratedCovGrad (I := I) g₀ r s i (0 : SmoothCcTensor g₀ r s) = 0 := by
    induction i with
    | zero => rw [iteratedCovGrad_zero]
    | succ j ih => rw [iteratedCovGrad_succ, ih, covGrad_zero]
  have hi (i : ℕ) :
      ∀ᶠ t in 𝓝 t₀, ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ r (s + i) x
          ((iteratedCovGrad (I := I) g₀ r s i (Φ t)).toSection x) < ε := by
    apply joint_small (f := fun t x =>
      riemannianFiberNormSq (I := I) (M := M) g₀ r (s + i) x
        ((iteratedCovGrad (I := I) g₀ r s i (Φ t)).toSection x)) hS
    · exact joint_jet_riemannianFiberNormSq (I := I) (M := M) g₀ r s i Φ
        (S := S) (K := S) (fun _ ht => ht) hjoint
    · intro x
      rw [hzero, hiter0 i]
      rw [show ((0 : SmoothCcTensor g₀ r (s + i)).toSection x) =
        (0 : TensorRSSpace r (s + i) I x) from by
          rw [SmoothCcTensor.toSection_zero]
          rfl]
      exact riemannianFiberNormSq_zero (I := I) (M := M) g₀ r (s + i) x
    · exact hε
  have htime :
      ∀ᶠ t in 𝓝 t₀, ∀ i ∈ Finset.range (p + 1), ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ r (s + i) x
          ((iteratedCovGrad (I := I) g₀ r s i (Φ t)).toSection x) < ε := by
    exact
      (Finset.eventually_all
        (I := Finset.range (p + 1))
        (l := 𝓝 t₀)
        (p := fun i t => ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ r (s + i) x
            ((iteratedCovGrad (I := I) g₀ r s i (Φ t)).toSection x) < ε)).2
        (fun i _ => hi i)
  filter_upwards [htime] with t ht
  intro i hip x
  exact ht i (by simp only [Finset.mem_range]; omega) x

omit [SigmaCompactSpace M] in
omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem joint_jet_bdd
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s) {S K : Set ℝ}
    (hK : IsCompact K) (hKS : K ⊆ S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) p.1
        ((Φ p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ∃ B : ℕ → ℝ, (∀ i, 0 ≤ B i) ∧
      ∀ i t, t ∈ K → ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ r (s + i) x
          ((iteratedCovGrad (I := I) g₀ r s i (Φ t)).toSection x) ≤ B i := by
  classical
  have hprod : IsCompact (K ×ˢ (Set.univ : Set M)) :=
    hK.prod isCompact_univ
  have hex : ∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ t, t ∈ K → ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ r (s + i) x
          ((iteratedCovGrad (I := I) g₀ r s i (Φ t)).toSection x) ≤ C := by
    intro i
    let F : ℝ × M → ℝ := fun p =>
      riemannianFiberNormSq (I := I) (M := M) g₀ r (s + i) p.2
        ((iteratedCovGrad (I := I) g₀ r s i (Φ p.1)).toSection p.2)
    have hcont : ContinuousOn F (K ×ˢ (Set.univ : Set M)) :=
      joint_jet_riemannianFiberNormSq (I := I) (M := M) g₀ r s i Φ hKS hjoint
    obtain ⟨C₀, hC₀⟩ := (hprod.image_of_continuousOn hcont).bddAbove
    refine ⟨max C₀ 0, le_max_right _ _, ?_⟩
    intro t ht x
    refine le_trans (hC₀ ?_) (le_max_left _ _)
    exact ⟨(t, x), ⟨ht, Set.mem_univ x⟩, rfl⟩
  choose B hB_nonneg hB using hex
  exact ⟨B, hB_nonneg, hB⟩

end ShortTime.Vendor

end

end JetBounds

section JointAlgebra

noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter Topology Bundle Manifold DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

namespace ShortTime.Vendor

open DifferentialGeometry DifferentialGeometry.Integral.L2

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance instCompleteSpaceE : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem joint_rs_sub {r s : ℕ} {S : Set ℝ}
    (A B : ∀ p : M × ℝ, TensorRSSpace r s I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) p.1 (A p)) ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) p.1 (B p)) ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) p.1 (A p - B p))
      ((Set.univ : Set M) ×ˢ S) := by
  let := tensorRSBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (TensorRSModel r s ℝ E)
    (fun z : M => TensorRSSpace r s I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := TensorRSModel r s ℝ E)
    (E := fun z : M => TensorRSSpace r s I z)).mp (hA p₀ hp₀)
  have hB' := (Bundle.contMDiffWithinAt_totalSpace (F := TensorRSModel r s ℝ E)
    (E := fun z : M => TensorRSSpace r s I z)).mp (hB p₀ hp₀)
  refine (hA'.2.sub hB'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S),
        p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_sub (A p) (B p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_sub
      (A p₀) (B p₀)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem joint_rs_add {r s : ℕ} {S : Set ℝ}
    (A B : ∀ p : M × ℝ, TensorRSSpace r s I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) p.1 (A p)) ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) p.1 (B p)) ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) p.1 (A p + B p))
      ((Set.univ : Set M) ×ˢ S) := by
  let := tensorRSBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (TensorRSModel r s ℝ E)
    (fun z : M => TensorRSSpace r s I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := TensorRSModel r s ℝ E)
    (E := fun z : M => TensorRSSpace r s I z)).mp (hA p₀ hp₀)
  have hB' := (Bundle.contMDiffWithinAt_totalSpace (F := TensorRSModel r s ℝ E)
    (E := fun z : M => TensorRSSpace r s I z)).mp (hB p₀ hp₀)
  refine (hA'.2.add hB'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S),
        p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_add (A p) (B p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_add
      (A p₀) (B p₀)


end ShortTime.Vendor

end

end JointAlgebra
