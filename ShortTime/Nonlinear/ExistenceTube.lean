import ShortTime.Nonlinear.Tube

/-!
# Parabolicity of a smooth family for a short time (`lem:legendre-basic` (iii))

The tube lemma of `Tube.lean` (`EquationData.exists_parabolic_segment`) is stated for two parabolic
solutions, but its proof only uses their smoothness and the parabolicity of one of them at the
initial time. Here it is restated under exactly these hypotheses
(`EquationData.exists_parabolic_segment_of_smooth`), and specialized to a single smooth family:
if the jets of `w` are parabolic at `t = 0`, they stay in the domain and satisfy the Legendre condition
with a uniform constant on a short interval `[0, η]` (`EquationData.exists_legendre_interval`).
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set Filter
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Elliptic DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff Topology BigOperators

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

variable (g : SmoothRiemannianMetric I M)

namespace EquationData

variable [CompleteSpace E] {s p : ℕ} (D : EquationData I M 0 s p)

/-- **The tube lemma at a point**, for smooth families (`EquationData.tube_local` without the
equation). Near `x₀` and for a short time after `t₀`, the jets on the segment between two smooth
families that agree at `t₀`, where the jets of the first are parabolic, lie in the domain and satisfy
the Legendre condition with a uniform constant. -/
theorem tube_local_of_smooth {T : ℝ} {u v : ℝ → SmoothCcTensor g 0 s}
    (hus : JointlySmoothOn g 0 s (Icc 0 T) u) (hvs : JointlySmoothOn g 0 s (Icc 0 T) v)
    (hTT₀ : T ≤ D.T₀) {t₀ : ℝ} (ht₀ : t₀ ∈ Ico 0 T)
    (hpar : ∀ x, D.IsParabolicAt g t₀ x (covJet g 0 s (2 * p) (u t₀) x))
    (h : u t₀ = v t₀) (x₀ : M) :
    ∃ lam > 0, ∃ N ∈ 𝓝 x₀, ∃ ε > 0, ∀ y ∈ N, ∀ τ ∈ Icc (0 : ℝ) ε, τ ≤ T - t₀ →
      ∀ σ ∈ Icc (0 : ℝ) 1,
        covJet g 0 s (2 * p) (v (t₀ + τ) + σ • (u (t₀ + τ) - v (t₀ + τ))) y ∈ D.dom (t₀ + τ) y ∧
        LegendreAt g 0 s p y (D.principal (t₀ + τ) y
          (covJet g 0 s (2 * p) (v (t₀ + τ) + σ • (u (t₀ + τ) - v (t₀ + τ))) y)) lam := by
  have hηT : t₀ + (T - t₀) ≤ T := by linarith
  set R0 : Set ((M × ℝ) × ℝ) :=
    (jetBase (I := I) 0 s (2 * p) x₀ ×ˢ Icc 0 (T - t₀)) ×ˢ Icc (0 : ℝ) 1 with hR0
  have hγ := D.contMDiffOn_trivJet_segment hus hvs hTT₀ ht₀.1 hηT x₀
  have hJ₀ : ∀ (y : M) (σ : ℝ), covJet g 0 s (2 * p)
      (v (t₀ + 0) + σ • (u (t₀ + 0) - v (t₀ + 0))) y = covJet g 0 s (2 * p) (u t₀) y := by
    intro y σ
    simp [h]
  have hm₀R0 : ∀ σ ∈ Icc (0 : ℝ) 1, ((x₀, (0 : ℝ)), σ) ∈ R0 := fun σ hσ =>
    mk_mem_prod (mk_mem_prod (mem_jetBase_self 0 s (2 * p) x₀) ⟨le_rfl, by linarith [ht₀.2]⟩) hσ
  /- Step 1: the segment stays in the domain. -/
  obtain ⟨U, hUo, hU⟩ := D.dom_relOpen x₀
  let Fd : (M × ℝ) × ℝ → ℝ × M × JetModel E 0 s (2 * p) := fun z =>
    (t₀ + z.1.2, z.1.1, trivJet x₀ z.1.1 (covJet g 0 s (2 * p)
      (v (t₀ + z.1.2) + z.2 • (u (t₀ + z.1.2) - v (t₀ + z.1.2))) z.1.1))
  have hFd : ∀ z ∈ R0, Fd z ∈ U → covJet g 0 s (2 * p)
      (v (t₀ + z.1.2) + z.2 • (u (t₀ + z.1.2) - v (t₀ + z.1.2))) z.1.1 ∈
        D.dom (t₀ + z.1.2) z.1.1 := by
    intro z hz hzU
    have hmem : ((t₀ + z.1.2, z.1.1, trivJet x₀ z.1.1 (covJet g 0 s (2 * p)
        (v (t₀ + z.1.2) + z.2 • (u (t₀ + z.1.2) - v (t₀ + z.1.2))) z.1.1)) :
          ℝ × M × JetModel E 0 s (2 * p)) ∈ localDom 0 s (2 * p) D.T₀ D.dom x₀ := by
      rw [hU]
      exact ⟨hzU, ⟨by linarith [hz.1.2.1, ht₀.1], by linarith [hz.1.2.2]⟩, hz.1.1⟩
    have h2 : jetOfModel 0 s (2 * p) x₀ z.1.1 (trivJet x₀ z.1.1 (covJet g 0 s (2 * p)
        (v (t₀ + z.1.2) + z.2 • (u (t₀ + z.1.2) - v (t₀ + z.1.2))) z.1.1)) ∈
          D.dom (t₀ + z.1.2) z.1.1 := hmem.2
    rwa [jetOfModel_trivJet hz.1.1] at h2
  have hstep1 : ∀ σ ∈ Icc (0 : ℝ) 1, ∀ᶠ z : (M × ℝ) × ℝ in 𝓝 ((x₀, (0 : ℝ)), σ),
      (z.1, z.2) ∈ R0 → Fd (z.1, z.2) ∈ U := by
    intro σ hσ
    have hc : ContinuousWithinAt Fd R0 ((x₀, 0), σ) :=
      (continuousWithinAt_const.add (continuous_snd.comp continuous_fst).continuousWithinAt).prodMk
        ((continuous_fst.comp continuous_fst).continuousWithinAt.prodMk
          (hγ _ (hm₀R0 σ hσ)).continuousWithinAt)
    have hin : Fd ((x₀, 0), σ) ∈ U := by
      have hmem : ((t₀ + 0, x₀, trivJet x₀ x₀ (covJet g 0 s (2 * p)
          (v (t₀ + 0) + σ • (u (t₀ + 0) - v (t₀ + 0))) x₀)) : ℝ × M × JetModel E 0 s (2 * p)) ∈
            localDom 0 s (2 * p) D.T₀ D.dom x₀ := by
        refine ⟨⟨⟨by linarith [ht₀.1], by linarith [ht₀.2]⟩, mem_jetBase_self 0 s (2 * p) x₀⟩, ?_⟩
        change jetOfModel 0 s (2 * p) x₀ x₀ (trivJet x₀ x₀ (covJet g 0 s (2 * p)
          (v (t₀ + 0) + σ • (u (t₀ + 0) - v (t₀ + 0))) x₀)) ∈ D.dom (t₀ + 0) x₀
        rw [jetOfModel_trivJet (mem_jetBase_self 0 s (2 * p) x₀), hJ₀, add_zero]
        exact (hpar x₀).1
      rw [hU] at hmem
      exact hmem.1
    filter_upwards [eventually_nhdsWithin_iff.mp
      (hc.preimage_mem_nhdsWithin (hUo.mem_nhds hin))] with z hz hzR
    exact hz hzR
  have hdomEv := isCompact_Icc.eventually_forall_of_forall_eventually
    (P := fun q σ => (q, σ) ∈ R0 → Fd (q, σ) ∈ U) hstep1
  obtain ⟨O, hOsub, hOo, hO0⟩ := eventually_nhds_iff.mp hdomEv
  set R1 : Set ((M × ℝ) × ℝ) := R0 ∩ (O ×ˢ univ) with hR1
  have hdomR1 : ∀ m ∈ R1, covJet g 0 s (2 * p)
      (v (t₀ + m.1.2) + m.2 • (u (t₀ + m.1.2) - v (t₀ + m.1.2))) m.1.1 ∈
        D.dom (t₀ + m.1.2) m.1.1 :=
    fun m hm => hFd m hm.1 (hOsub m.1 hm.2.1 m.2 hm.1.2 hm.1)
  have hm₀R1 : ∀ σ ∈ Icc (0 : ℝ) 1, ((x₀, (0 : ℝ)), σ) ∈ R1 := fun σ hσ =>
    ⟨hm₀R0 σ hσ, mk_mem_prod hO0 (mem_univ _)⟩
  /- Step 2: the Legendre condition, in coordinates at `x₀`. -/
  obtain ⟨Λ, Bf, hΛ, hBf, hev⟩ := exists_legendre_coord (s := s) (p := p) g x₀
  obtain ⟨A, hA⟩ : ∃ A : (M × ℝ) × ℝ →
      (TensorRSModel 0 (s + 2 * p) ℝ E →L[ℝ] TensorRSModel 0 s ℝ E),
      ∀ m, A m = avgIntegrand D u v t₀ x₀ (Fin.last (2 * p)) m.1 m.2 :=
    ⟨fun m => avgIntegrand D u v t₀ x₀ (Fin.last (2 * p)) m.1 m.2, fun _ => rfl⟩
  have hAc : ContinuousOn A R1 :=
    (D.contMDiffOn_avgIntegrand_of_subset hus hvs hTT₀ ht₀.1 hηT x₀ inter_subset_left hdomR1
      (Fin.last (2 * p))).continuousOn.congr fun m _ => hA m
  obtain ⟨-, lam₁, hL₁⟩ := hpar x₀
  have hlam₁ : 0 < lam₁ := hL₁.1
  have hstep2 : ∀ w ∈ Icc (0 : ℝ) 1 ×ˢ Metric.sphere (0 : TensorRSModel 0 (s + p) ℝ E) 1,
      ∀ᶠ z : (M × ℝ) × (ℝ × TensorRSModel 0 (s + p) ℝ E) in 𝓝 ((x₀, (0 : ℝ)), w),
        (z.1, z.2.1) ∈ R1 →
          lam₁ / 2 * Bf z.1.1 z.2.2 < (-1) ^ (p + 1) * Λ z.1.1 (A (z.1, z.2.1)) z.2.2 := by
    rintro ⟨σ, z⟩ ⟨hσ, hz⟩
    have hz1 : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp hz
    have hm₀ := hm₀R1 σ hσ
    -- the gap function is continuous
    have hA' : ContinuousWithinAt (A ∘ fun z : (M × ℝ) × (ℝ × TensorRSModel 0 (s + p) ℝ E) =>
        (z.1, z.2.1)) {z | (z.1, z.2.1) ∈ R1} ((x₀, 0), (σ, z)) :=
      ContinuousWithinAt.comp (g := A)
        (f := fun z : (M × ℝ) × (ℝ × TensorRSModel 0 (s + p) ℝ E) => (z.1, z.2.1))
        (x := ((x₀, 0), (σ, z))) (hAc _ hm₀)
        (continuous_fst.prodMk (continuous_fst.comp continuous_snd)).continuousWithinAt
        fun z hz => hz
    have h11 : Continuous fun z : (M × ℝ) × (ℝ × TensorRSModel 0 (s + p) ℝ E) => z.1.1 :=
      continuous_fst.fst
    have h22 : Continuous fun z : (M × ℝ) × (ℝ × TensorRSModel 0 (s + p) ℝ E) => z.2.2 :=
      continuous_snd.snd
    have hΛc : ContinuousWithinAt
        (fun z : (M × ℝ) × (ℝ × TensorRSModel 0 (s + p) ℝ E) => Λ z.1.1 (A (z.1, z.2.1)) z.2.2)
        {z | (z.1, z.2.1) ∈ R1} ((x₀, 0), (σ, z)) :=
      hΛ.continuousAt.comp_continuousWithinAt
        (h11.continuousWithinAt.prodMk (hA'.prodMk h22.continuousWithinAt))
    have hBc : ContinuousWithinAt
        (fun z : (M × ℝ) × (ℝ × TensorRSModel 0 (s + p) ℝ E) => Bf z.1.1 z.2.2)
        {z | (z.1, z.2.1) ∈ R1} ((x₀, 0), (σ, z)) :=
      hBf.continuousAt.comp_continuousWithinAt
        (h11.continuousWithinAt.prodMk h22.continuousWithinAt)
    have hGc : ContinuousWithinAt
        (fun z : (M × ℝ) × (ℝ × TensorRSModel 0 (s + p) ℝ E) =>
          (-1) ^ (p + 1) * Λ z.1.1 (A (z.1, z.2.1)) z.2.2 - lam₁ / 2 * Bf z.1.1 z.2.2)
        {z | (z.1, z.2.1) ∈ R1} ((x₀, 0), (σ, z)) :=
      (continuousWithinAt_const.mul hΛc).sub (continuousWithinAt_const.mul hBc)
    -- the gap is positive at `(x₀, t₀)`, by the Legendre condition for `u`
    have hpos : 0 < (-1) ^ (p + 1) * Λ x₀ (A ((x₀, 0), σ)) z - lam₁ / 2 * Bf x₀ z := by
      obtain ⟨hΛx, hBx⟩ := hev.self_of_nhds (A ((x₀, 0), σ)) z
      have hJdom := hdomR1 _ hm₀
      have hcoord : A ((x₀, 0), σ) = coordP x₀ x₀ (D.partialDeriv (Fin.last (2 * p)) (t₀ + 0) x₀
          (covJet g 0 s (2 * p) (v (t₀ + 0) + σ • (u (t₀ + 0) - v (t₀ + 0))) x₀)) := by
        rw [hA, D.coordP_partialDeriv_segment (mem_jetBase_self 0 s (2 * p) x₀)
          ⟨by linarith [ht₀.1], by linarith [ht₀.2]⟩ hJdom]
      have hL : LegendreAt g 0 s p x₀ (D.principal (t₀ + 0) x₀
          (covJet g 0 s (2 * p) (v (t₀ + 0) + σ • (u (t₀ + 0) - v (t₀ + 0))) x₀)) lam₁ := by
        rw [hJ₀ x₀ σ, add_zero]
        exact hL₁
      have key := hL.2 ((trivAt I M 0 (s + p) x₀).symmL ℝ x₀ z)
      rw [D.principal_eq_fibMap (mem_jetBase_self 0 s (2 * p) x₀), ← hcoord, hΛx, hBx] at key
      have hBpos : 0 < Bf x₀ z := by
        rw [← hBx]
        refine (Tensor.TensorRSRiemannianBundle.tensorRSRiemannianMetric (I := I) (M := M) g 0
          (s + p)).pos x₀ _ fun h0 => ?_
        have h1 := congrArg ((trivAt I M 0 (s + p) x₀).continuousLinearMapAt ℝ x₀) h0
        rw [Trivialization.continuousLinearMapAt_symmL _ (mem_baseSet_trivializationAt _ _ x₀),
          map_zero] at h1
        rw [h1, norm_zero] at hz1
        exact zero_ne_one hz1
      nlinarith [mul_pos hlam₁ hBpos]
    filter_upwards [eventually_nhdsWithin_iff.mp
      (hGc.preimage_mem_nhdsWithin (Ioi_mem_nhds hpos))] with w hw hwR
    have := hw hwR
    simp only [mem_Ioi] at this
    linarith
  have hLegEv := (isCompact_Icc.prod
    (isCompact_sphere (0 : TensorRSModel 0 (s + p) ℝ E) 1)).eventually_forall_of_forall_eventually
    (P := fun q w => (q, w.1) ∈ R1 →
      lam₁ / 2 * Bf q.1 w.2 < (-1) ^ (p + 1) * Λ q.1 (A (q, w.1)) w.2) hstep2
  /- Step 3: a product neighbourhood of `(x₀, 0)`. -/
  have hall : ∀ᶠ q : M × ℝ in 𝓝 (x₀, 0), q ∈ O ∧
      (∀ w ∈ Icc (0 : ℝ) 1 ×ˢ Metric.sphere (0 : TensorRSModel 0 (s + p) ℝ E) 1,
        (q, w.1) ∈ R1 → lam₁ / 2 * Bf q.1 w.2 < (-1) ^ (p + 1) * Λ q.1 (A (q, w.1)) w.2) ∧
      (∀ Q z, legendreForm g 0 s p q.1 ((fibMap I (s + 2 * p) s x₀ q.1 Q).comp
          (EquationData.castIdx (r := 0) (by omega : s + p + p = s + 2 * p)
            q.1).toContinuousLinearMap)
          ((trivAt I M 0 (s + p) x₀).symmL ℝ q.1 z) ((trivAt I M 0 (s + p) x₀).symmL ℝ q.1 z) =
            Λ q.1 Q z ∧
        fiberInner g 0 (s + p) q.1 ((trivAt I M 0 (s + p) x₀).symmL ℝ q.1 z)
          ((trivAt I M 0 (s + p) x₀).symmL ℝ q.1 z) = Bf q.1 z) ∧
      q.1 ∈ jetBase (I := I) 0 s (2 * p) x₀ :=
    Filter.Eventually.and (hOo.mem_nhds hO0) (hLegEv.and
      (((continuous_fst.tendsto (x₀, (0 : ℝ))).eventually hev).and
        ((continuous_fst.tendsto (x₀, (0 : ℝ))).eventually
          ((isOpen_jetBase 0 s (2 * p) x₀).mem_nhds (mem_jetBase_self 0 s (2 * p) x₀)))))
  obtain ⟨N, hN, V, hV, hNV⟩ := mem_nhds_prod_iff.mp hall
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.mp hV
  refine ⟨lam₁ / 2, half_pos hlam₁, N, hN, ε / 2, half_pos hε, fun y hy τ hτ hτT σ hσ => ?_⟩
  have hτV : τ ∈ V := hεV (by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hτ.1]
    linarith [hτ.2])
  obtain ⟨hqO, hqLeg, hqev, hqJ⟩ := hNV (mk_mem_prod hy hτV)
  have hmR1 : ((y, τ), σ) ∈ R1 := ⟨mk_mem_prod (mk_mem_prod hqJ ⟨hτ.1, hτT⟩) hσ,
    mk_mem_prod hqO (mem_univ _)⟩
  have hdomJ := hdomR1 _ hmR1
  refine ⟨hdomJ, half_pos hlam₁, fun ξ => ?_⟩
  have hcoord : A ((y, τ), σ) = coordP x₀ y (D.partialDeriv (Fin.last (2 * p)) (t₀ + τ) y
      (covJet g 0 s (2 * p) (v (t₀ + τ) + σ • (u (t₀ + τ) - v (t₀ + τ))) y)) := by
    rw [hA, D.coordP_partialDeriv_segment hqJ
      ⟨by linarith [ht₀.1, hτ.1], by linarith [hτT]⟩ hdomJ]
  rw [D.principal_eq_fibMap hqJ, ← hcoord]
  have hyb : y ∈ (trivAt I M 0 (s + p) x₀).baseSet :=
    mem_iInter.mp hqJ.2 ⟨p, by omega⟩
  have hξ : ξ = (trivAt I M 0 (s + p) x₀).symmL ℝ y
      ((trivAt I M 0 (s + p) x₀).continuousLinearMapAt ℝ y ξ) :=
    (Trivialization.symmL_continuousLinearMapAt _ hyb ξ).symm
  by_cases hz0 : (trivAt I M 0 (s + p) x₀).continuousLinearMapAt ℝ y ξ = 0
  · rw [hz0, map_zero] at hξ
    subst hξ
    rw [show (0 : TensorRSSpace 0 (s + p) I y) = (0 : ℝ) • (0 : TensorRSSpace 0 (s + p) I y) from
      (zero_smul ℝ _).symm, legendreForm_smul_smul, fiberInner_smul_smul]
    simp
  · set z := (trivAt I M 0 (s + p) x₀).continuousLinearMapAt ℝ y ξ with hz
    have hzh : ‖z‖⁻¹ • z ∈ Metric.sphere (0 : TensorRSModel 0 (s + p) ℝ E) 1 := by
      rw [mem_sphere_zero_iff_norm]
      exact norm_smul_inv_norm hz0
    have hlt : lam₁ / 2 * fiberInner g 0 (s + p) y
          ((trivAt I M 0 (s + p) x₀).symmL ℝ y (‖z‖⁻¹ • z))
          ((trivAt I M 0 (s + p) x₀).symmL ℝ y (‖z‖⁻¹ • z)) <
        (-1) ^ (p + 1) * legendreForm g 0 s p y ((fibMap I (s + 2 * p) s x₀ y (A ((y, τ), σ))).comp
          (EquationData.castIdx (r := 0) (by omega : s + p + p = s + 2 * p) y).toContinuousLinearMap)
          ((trivAt I M 0 (s + p) x₀).symmL ℝ y (‖z‖⁻¹ • z))
          ((trivAt I M 0 (s + p) x₀).symmL ℝ y (‖z‖⁻¹ • z)) := by
      have h1 := hqLeg (σ, ‖z‖⁻¹ • z) ⟨hσ, hzh⟩ hmR1
      obtain ⟨hΛy, hBy⟩ := hqev (A ((y, τ), σ)) (‖z‖⁻¹ • z)
      dsimp only at h1 hΛy hBy
      rw [hΛy, hBy]
      exact h1
    have hξ' : ξ = ‖z‖ • (trivAt I M 0 (s + p) x₀).symmL ℝ y (‖z‖⁻¹ • z) := by
      rw [← map_smul, smul_inv_smul₀ (norm_ne_zero_iff.mpr hz0)]
      exact hξ
    rw [hξ', legendreForm_smul_smul, fiberInner_smul_smul]
    have hn : 0 < ‖z‖ ^ 2 := by positivity
    exact mul_le_mul_of_lt_aux hn hlt

/-- **The segment between the jets stays parabolic** (tube lemma, `lem:legendre-basic` (iii)), for
smooth families. If two smooth families agree at `t₀ < T` and the jets of the first are parabolic at
`t₀`, then for a short time the jets on the segment between them lie in the domain and satisfy the
Legendre condition with a uniform constant. -/
theorem exists_parabolic_segment_of_smooth {T : ℝ} {u v : ℝ → SmoothCcTensor g 0 s}
    (hus : JointlySmoothOn g 0 s (Icc 0 T) u) (hvs : JointlySmoothOn g 0 s (Icc 0 T) v)
    (hTT₀ : T ≤ D.T₀) {t₀ : ℝ} (ht₀ : t₀ ∈ Ico 0 T)
    (hpar : ∀ x, D.IsParabolicAt g t₀ x (covJet g 0 s (2 * p) (u t₀) x))
    (h : u t₀ = v t₀) :
    ∃ η > 0, t₀ + η ≤ T ∧ ∃ lam > 0, ∀ t ∈ Icc t₀ (t₀ + η), ∀ x : M, ∀ σ ∈ Icc (0 : ℝ) 1,
      covJet g 0 s (2 * p) (v t + σ • (u t - v t)) x ∈ D.dom t x ∧
        LegendreAt g 0 s p x
          (D.principal t x (covJet g 0 s (2 * p) (v t + σ • (u t - v t)) x)) lam := by
  classical
  choose lamf hlamf Nf hNf εf hεf hgood using fun x₀ => D.tube_local_of_smooth g hus hvs hTT₀ ht₀ hpar h x₀
  obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover Nf fun x _ => hNf x
  set η := (insert (T - t₀) (t.image εf)).min' (Finset.insert_nonempty _ _) with hη
  set lam := (insert 1 (t.image lamf)).min' (Finset.insert_nonempty _ _) with hlam
  have hηpos : 0 < η := by
    rw [hη, Finset.lt_min'_iff]
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · linarith [ht₀.2]
    · obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp ha
      exact hεf x
  have hlampos : 0 < lam := by
    rw [hlam, Finset.lt_min'_iff]
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact one_pos
    · obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp ha
      exact hlamf x
  have hηT : η ≤ T - t₀ := Finset.min'_le _ _ (Finset.mem_insert_self _ _)
  refine ⟨η, hηpos, by linarith, lam, hlampos, fun t' ht' x σ hσ => ?_⟩
  obtain ⟨x₀, hx₀t, hx⟩ : ∃ x₀ ∈ t, x ∈ Nf x₀ := by
    simpa using ht (mem_univ x)
  have hηle : η ≤ εf x₀ :=
    Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hx₀t))
  have hlamle : lam ≤ lamf x₀ :=
    Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hx₀t))
  have hgood' := hgood x₀ x hx (t' - t₀) ⟨by linarith [ht'.1], by linarith [ht'.2]⟩
    (by linarith [ht'.2]) σ hσ
  rw [add_sub_cancel] at hgood'
  exact ⟨hgood'.1, LegendreAt.mono g hgood'.2 hlampos hlamle⟩

/-- **A smooth family that is parabolic at `t = 0` stays parabolic for a short time**, with a
uniform Legendre constant (`lem:legendre-basic` (iii)). -/
theorem exists_legendre_interval {T : ℝ} (hT : 0 < T) (hTD : T ≤ D.T₀)
    {w : ℝ → SmoothCcTensor g 0 s} (hw : JointlySmoothOn g 0 s (Icc 0 T) w)
    (h0 : ∀ x, D.IsParabolicAt g 0 x (covJet g 0 s (2 * p) (w 0) x)) :
    ∃ η > 0, η ≤ T ∧ ∃ lam > 0, ∀ t ∈ Icc (0 : ℝ) η, ∀ x : M,
      covJet g 0 s (2 * p) (w t) x ∈ D.dom t x ∧
        LegendreAt g 0 s p x (D.principal t x (covJet g 0 s (2 * p) (w t) x)) lam := by
  obtain ⟨η, hη, hηT, lam, hlam, H⟩ :=
    D.exists_parabolic_segment_of_smooth g hw hw hTD ⟨le_rfl, hT⟩ h0 rfl
  refine ⟨η, hη, by linarith, lam, hlam, fun t ht x => ?_⟩
  have h := H t (by rwa [zero_add]) x 0 ⟨le_rfl, zero_le_one⟩
  simpa only [zero_smul, add_zero] using h

end EquationData

end ShortTime
