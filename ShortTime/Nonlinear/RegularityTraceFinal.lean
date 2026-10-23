import ShortTime.Nonlinear.RegularityFinal
import ShortTime.Nonlinear.RegularityTrace
import ShortTime.Nonlinear.SmoothRepTimeTrace
import ShortTime.Nonlinear.TraceRegularityStatement

/-!
# Regularity with an initial trace: assembly by a finite cover (`thm:C`, Step 2)

As `regularity_of_time` (`RegularityFinal.lean`), for solutions `U ∈ 𝒫^m` near `ofSmooth w` that need
not vanish at `t = 0`, but whose trace is smooth (`U - ofSmooth b ∈ 𝒫^m_0`):

* for each `α` the chart patch `(r_α, B_α)`, the neighbourhood `V_α` and radius `ρ_α` of
  `exists_iterPull_contDiffOn_trace`, and the spatial radius `ε_α` of `exists_spatialSmooth`;
* the time part `smoothRep_time_trace` supplies `V_t` and radii `ε^t_α ≤ r_α`;
* finitely many chart balls cover `M`; `V = V_t ∩ ⋂ V_{α_i}`.

`EquationData.regularity_of_time_trace` is the result, and `EquationData.traceRegularity` states it
in the form `TraceRegularity` used for `cor:C`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set Filter Topology Metric
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff

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

variable {s p : ℕ}

open ParabolicSpace HFlow SmoothRep

/-- **Regularity with an initial trace.** In the setting of `parabolicSpace_solution_smooth`, there
is a neighbourhood `V` of `ofSmooth w` in `𝒫^m` such that every `U ∈ V` with smooth trace
(`U - ofSmooth b ∈ 𝒫^m_0`) and `∂ₜU - 𝒩 U = ofSmooth f` is a smooth family. -/
theorem regularity_of_time_trace (D : EquationData I M 0 s p) (hp : 1 ≤ p)
    {m : ℕ} (hm : Module.finrank ℝ E / (2 * p) + 4 ≤ m) (hm1 : 1 ≤ m)
    {T₁ : ℝ} (hT₁ : 0 < T₁) (hT₁D : T₁ ≤ D.T₀) {lam : ℝ}
    {w : ℝ → SmoothCcTensor g 0 s} (hw : JointlySmoothOn g 0 s (Icc 0 T₁) w)
    (hleg : ∀ t ∈ Icc (0 : ℝ) T₁, ∀ x : M, covJet g 0 s (2 * p) (w t) x ∈ D.dom t x ∧
      LegendreAt g 0 s p x (D.principal t x (covJet g 0 s (2 * p) (w t) x)) lam)
    {δ : ℝ} (hδ : 0 < δ)
    {𝒩 : ParabolicSpace g s p m T₁ → ParabolicSpace g s p (m - 1) T₁}
    (h𝒩 : ContDiffAt ℝ ∞ 𝒩 (ofSmooth w hw))
    (hagree : ∀ u (hu : JointlySmoothOn g 0 s (Icc 0 T₁) u),
      dist (ofSmooth (p := p) (m := m) u hu) (ofSmooth w hw) < δ →
      (∀ t ∈ Icc (0 : ℝ) T₁, ∀ x : M, covJet g 0 s (2 * p) (u t) x ∈ D.dom t x) ∧
      ∃ hF, 𝒩 (ofSmooth u hu) = ofSmooth (D.nonlinFamily u) hF)
    (hL : ∃ L : LinearOp g s p T₁, L.IsParabolic lam ∧
      (∀ k t, t ∈ Icc (0 : ℝ) T₁ → ∀ x,
        opFieldHom ((L.coeff k t).toSection x) =
          D.partialDeriv k t x (covJet g 0 s (2 * p) (w t) x)) ∧
      ∀ h (hh : JointlySmoothOn g 0 s (Icc 0 T₁) h), ∃ hL,
        fderiv ℝ 𝒩 (ofSmooth w hw) (ofSmooth h hh) =
          ofSmooth (fun t => L.apply t (h t)) hL) :
    ∃ V ∈ 𝓝 (ofSmooth (p := p) (m := m) w hw), ∀ U ∈ V,
      ∀ (f : ℝ → SmoothCcTensor g 0 s) (hf : JointlySmoothOn g 0 s (Icc 0 T₁) f)
        (b : ℝ → SmoothCcTensor g 0 s) (hb : JointlySmoothOn g 0 s (Icc 0 T₁) b),
        U - ofSmooth b hb ∈ zeroAtStart g s p m T₁ →
        timeDerivExt hT₁ hm1 U - 𝒩 U = ofSmooth f hf →
        ∃ (vt : ℝ → SmoothCcTensor g 0 s) (hvt : JointlySmoothOn g 0 s (Icc 0 T₁) vt),
          U = ofSmooth vt hvt := by
  classical
  obtain ⟨Vt, hVt, htm⟩ := smoothRep_time_trace D hp hm hm1 hT₁ hT₁D hw
    (fun t ht x => (hleg t ht x).1) hδ h𝒩 hagree
  have hk : Module.finrank ℝ E / 2 + 1 ≤ 2 * p * (m - 1) := spatial_index_aux hp hm
  have hm0 : 0 < m := hm1
  choose r hr B hball hB using fun α : M => exists_chart_patch (I := I) (M := M) α
  have hAng := fun α : M => exists_iterPull_contDiffOn_trace D hp hm hm1 hT₁ hT₁D hw hleg hδ h𝒩
    hagree hL (B α)
  choose V hV ρ hρ hflow using hAng
  have hSp := fun α : M => exists_spatialSmooth (g := g) (s := s) (p := p) (m := m) (T := T₁)
    hT₁ hm0 hk α (hr α) (hball α) (hB α) (hρ α)
  choose εs hεs hsub hS using hSp
  have hGt := fun α : M => htm α (r α) (hr α) (B α) (hball α) (hB α)
  choose εt hεt hG using hGt
  set ε' : M → ℝ := fun α => min (εs α) (εt α) with hε'
  set O : M → Set M := fun α =>
    (chartAt H α).source ∩ extChartAt I α ⁻¹' Metric.ball (extChartAt I α α) (ε' α) with hO
  have hOo : ∀ α, IsOpen (O α) := fun α => by
    have := (continuousOn_extChartAt (I := I) α).isOpen_inter_preimage
      (isOpen_extChartAt_source α) (Metric.isOpen_ball (x := extChartAt I α α) (ε := ε' α))
    rwa [extChartAt_source] at this
  have hε'pos : ∀ α, 0 < ε' α := fun α => lt_min (hεs α) (hεt α).1
  obtain ⟨A, hA⟩ := isCompact_univ.elim_finite_subcover O hOo
    (fun x _ => mem_iUnion.2 ⟨x, ⟨mem_chart_source H x, Metric.mem_ball_self (hε'pos x)⟩⟩)
  refine ⟨Vt ∩ ⋂ α ∈ A, V α, inter_mem hVt ((Filter.biInter_finset_mem A).2 fun α _ => hV α),
    fun U hU f hf b hb hUb heq => ?_⟩
  have hvt : U ∈ Vt := hU.1
  have hvV : ∀ α ∈ A, U ∈ V α := fun α hα => mem_iInter₂.1 hU.2 α hα
  obtain ⟨u, hu, hev⟩ := exists_smooth_rep_cover (g := g) (s := s) (p := p) (m := m) (T := T₁) hT₁
    U (fun x => by
    obtain ⟨α, hαA, hxO⟩ := mem_iUnion₂.1 (hA (mem_univ x))
    have hle1 : Metric.ball (extChartAt I α α) (ε' α) ⊆ Metric.ball (extChartAt I α α) (εs α) :=
      Metric.ball_subset_ball (min_le_left _ _)
    have hle2 : Metric.ball (extChartAt I α α) (ε' α) ⊆ Metric.ball (extChartAt I α α) (εt α) :=
      Metric.ball_subset_ball (min_le_right _ _)
    obtain ⟨G, hG1, hG2⟩ := hG α U hvt f hf heq
    refine ⟨α, ε' α, hε'pos α, hxO.1, hxO.2, hle1.trans (hsub α), fun n => ?_, G,
      fun t ht y hy => hG1 t ht y (hle2 hy), hG2 (ε' α) (min_le_right _ _)⟩
    exact SpatialReg.SpC.mono_set hle1 n
      (hS α U (hflow α U (hvV α hαA) f hf heq b hb hUb) n))
  exact ⟨u, hu, ParabolicSpace.eq_ofSmooth_of_evalJet_eq hT₁ hm1 hk _ hu hev⟩

/-- `regularity_of_time_trace` in the form `TraceRegularity` (for `cor:C`). -/
theorem traceRegularity (D : EquationData I M 0 s p) (g : SmoothRiemannianMetric I M) :
    D.TraceRegularity g := by
  intro hp m hm hm1 T₁ hT₁ hT₁D lam hlam w hw hleg δ hδ 𝒩 h𝒩 hagree hL
  obtain ⟨V, hV, H⟩ := regularity_of_time_trace D hp hm hm1 hT₁ hT₁D hw hleg hδ h𝒩 hagree hL
  exact ⟨V, hV, fun U hU f hf b hb hUb heq => H U hU f hf b hb hUb heq⟩

end EquationData

end ShortTime
