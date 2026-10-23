import ShortTime.Nonlinear.RegularityAngenent
import ShortTime.Nonlinear.SmoothRepAssembly
import ShortTime.Nonlinear.SmoothRepTimeAnalysis
import ShortTime.Nonlinear.Closable

/-!
# Regularity of the abstract solution: assembly by a finite cover (`prop:regularity`)

The neighbourhood `V` of `exists_iterPull_contDiffOn` depends on the frame `B`, and
`SmoothRep.exists_spatialSmooth` needs a frame with constant chart coordinates near each point. As in
the paper, finitely many frames suffice, by compactness of `M`:

* for each `α` take a chart patch `(r_α, B_α)` (`exists_chart_patch`), the neighbourhood `V_α` and
  radius `ρ_α` of Angenent's trick, and the spatial radius `ε_α` of `exists_spatialSmooth` (which does
  not depend on `v`);
* the time part supplies a neighbourhood `V_t` (uniform in `α`: smallness of `v` only) and, for each
  patch, a radius `ε^t_α ≤ r_α` independent of `v`;
* the balls `B(chart α, min ε_α ε^t_α)` around finitely many `α_i` cover `M`; take `V = V_t ∩ ⋂ V_{α_i}`;
* `SmoothRep.exists_smooth_rep_cover` gives a jointly smooth representative, and
  `eq_ofSmooth_of_evalJet_eq` identifies it with `v`.

The time part is the hypothesis `htime` of `regularity_of_time`.
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

theorem spatial_index_aux {n p m : ℕ} (hp : 1 ≤ p) (hm : n / (2 * p) + 4 ≤ m) :
    n / 2 + 1 ≤ 2 * p * (m - 1) := by
  have h1 := Nat.lt_mul_div_succ n (show 0 < 2 * p by omega)
  have h2 : 2 * p * (n / (2 * p) + 1) ≤ 2 * p * (m - 1) := Nat.mul_le_mul_left _ (by omega)
  generalize 2 * p * (n / (2 * p) + 1) = X at h1 h2
  generalize 2 * p * (m - 1) = Y at h2
  omega

/-- **Regularity, given the time part.** The finite-cover assembly of `prop:regularity`: the
hypothesis `htime` is the time bootstrap (a neighbourhood `V_t` of `0`, uniform in the point, and for
each chart patch `(α, r, B)` a radius `ε^t ≤ r` independent of `v`, such that for `v ∈ V_t` solving the
equation with smooth right side, `repChart` is differentiable in time with a right side `G` that has
the regularity of `repChart`, on every ball of radius `≤ ε^t`). -/
theorem regularity_of_time (D : EquationData I M 0 s p) (hp : 1 ≤ p)
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
          ofSmooth (fun t => L.apply t (h t)) hL)
    (htime : ∃ Vt ∈ 𝓝 (0 : zeroAtStart g s p m T₁),
      ∀ (α : M) (r : ℝ), 0 < r →
        ∀ (B : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
          Metric.closedBall (extChartAt I α α) r ⊆ (extChartAt I α).target →
          (∀ y ∈ Metric.closedBall (extChartAt I α α) r, ∀ k,
            trivToE I α ((extChartAt I α).symm y) (B k ((extChartAt I α).symm y)) =
              Module.finBasis ℝ E k) →
          ∃ εt : ℝ, 0 < εt ∧ εt ≤ r ∧ ∀ v ∈ Vt,
            ∀ (f : ℝ → SmoothCcTensor g 0 s) (hf : JointlySmoothOn g 0 s (Icc 0 T₁) f),
              existenceMap hT₁ hm1 𝒩 (ofSmooth w hw) v = ofSmooth f hf →
              ∃ G : ℝ → E → TensorRSModel 0 s ℝ E,
                (∀ t ∈ Icc (0 : ℝ) T₁, ∀ y ∈ Metric.ball (extChartAt I α α) εt,
                  HasDerivWithinAt
                    (fun τ => repChart g s p m T₁ α (v : ParabolicSpace g s p m T₁) τ y)
                    (G t y) (Icc 0 T₁) t) ∧
                ∀ ε, ε ≤ εt → ∀ k,
                  (∀ n, SpatialReg.SpC k (Icc 0 T₁) (Metric.ball (extChartAt I α α) ε) n
                    (TensorRSModel 0 s ℝ E)
                    (repChart g s p m T₁ α (v : ParabolicSpace g s p m T₁))) →
                  ∀ n, SpatialReg.SpC k (Icc 0 T₁) (Metric.ball (extChartAt I α α) ε) n
                    (TensorRSModel 0 s ℝ E) G) :
    ∃ V ∈ 𝓝 (0 : zeroAtStart g s p m T₁), ∀ v ∈ V,
      ∀ (f : ℝ → SmoothCcTensor g 0 s) (hf : JointlySmoothOn g 0 s (Icc 0 T₁) f),
        existenceMap hT₁ hm1 𝒩 (ofSmooth w hw) v = ofSmooth f hf →
        ∃ (vt : ℝ → SmoothCcTensor g 0 s) (hvt : JointlySmoothOn g 0 s (Icc 0 T₁) vt),
          (v : ParabolicSpace g s p m T₁) = ofSmooth vt hvt := by
  classical
  obtain ⟨Vt, hVt, htm⟩ := htime
  have hk : Module.finrank ℝ E / 2 + 1 ≤ 2 * p * (m - 1) := spatial_index_aux hp hm
  have hm0 : 0 < m := hm1
  choose r hr B hball hB using fun α : M => exists_chart_patch (I := I) (M := M) α
  have hAng := fun α : M => exists_iterPull_contDiffOn D hp hm hm1 hT₁ hT₁D hw hleg hδ h𝒩 hagree
    hL (B α)
  choose V hV ρ hρ hflow using hAng
  have hSp := fun α : M => exists_spatialSmooth (g := g) (s := s) (p := p) (m := m) (T := T₁)
    hT₁ hm0 hk α (hr α) (hball α) (hB α) (hρ α)
  choose εs hεs hsub hS using hSp
  have hGt := fun α : M => htm α (r α) (hr α) (B α) (hball α) (hB α)
  choose εt hεt hεtr hG using hGt
  set ε' : M → ℝ := fun α => min (εs α) (εt α) with hε'
  set O : M → Set M := fun α =>
    (chartAt H α).source ∩ extChartAt I α ⁻¹' Metric.ball (extChartAt I α α) (ε' α) with hO
  have hOo : ∀ α, IsOpen (O α) := fun α => by
    have := (continuousOn_extChartAt (I := I) α).isOpen_inter_preimage
      (isOpen_extChartAt_source α) (Metric.isOpen_ball (x := extChartAt I α α) (ε := ε' α))
    rwa [extChartAt_source] at this
  have hε'pos : ∀ α, 0 < ε' α := fun α => lt_min (hεs α) (hεt α)
  obtain ⟨A, hA⟩ := isCompact_univ.elim_finite_subcover O hOo
    (fun x _ => mem_iUnion.2 ⟨x, ⟨mem_chart_source H x, Metric.mem_ball_self (hε'pos x)⟩⟩)
  refine ⟨Vt ∩ ⋂ α ∈ A, V α, inter_mem hVt ((Filter.biInter_finset_mem A).2 fun α _ => hV α),
    fun v hv f hf heq => ?_⟩
  have hvt : v ∈ Vt := hv.1
  have hvV : ∀ α ∈ A, v ∈ V α := fun α hα => mem_iInter₂.1 hv.2 α hα
  obtain ⟨u, hu, hev⟩ := exists_smooth_rep_cover (g := g) (s := s) (p := p) (m := m) (T := T₁) hT₁
    (v : ParabolicSpace g s p m T₁) (fun x => by
    obtain ⟨α, hαA, hxO⟩ := mem_iUnion₂.1 (hA (mem_univ x))
    have hle1 : Metric.ball (extChartAt I α α) (ε' α) ⊆ Metric.ball (extChartAt I α α) (εs α) :=
      Metric.ball_subset_ball (min_le_left _ _)
    have hle2 : Metric.ball (extChartAt I α α) (ε' α) ⊆ Metric.ball (extChartAt I α α) (εt α) :=
      Metric.ball_subset_ball (min_le_right _ _)
    obtain ⟨G, hG1, hG2⟩ := hG α v hvt f hf heq
    refine ⟨α, ε' α, hε'pos α, hxO.1, hxO.2, hle1.trans (hsub α), fun n => ?_, G,
      fun t ht y hy => hG1 t ht y (hle2 hy), hG2 (ε' α) (min_le_right _ _)⟩
    exact SpatialReg.SpC.mono_set hle1 n
      (hS α (v : ParabolicSpace g s p m T₁) (hflow α v (hvV α hαA) f hf heq) n))
  exact ⟨u, hu, ParabolicSpace.eq_ofSmooth_of_evalJet_eq hT₁ hm1 hk _ hu hev⟩

end EquationData

end ShortTime
