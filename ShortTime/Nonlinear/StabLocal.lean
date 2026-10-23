import ShortTime.Nonlinear.ExistenceTube

/-!
# Stability of parabolicity at a point (`lem:legendre-basic` (iii), quantitative)

`EquationData.stab_local`: if a jet `ζ₀ = jetOfModel x₀ x₀ J₀` over `x₀` is parabolic at time `t₀`
(Legendre constant `lam₁`), then there are a neighbourhood `N` of `x₀`, a radius `ε > 0` and a
constant `lam > 0` such that every jet over `y ∈ N` whose coordinates in the trivializations at `x₀`
are `ε`-close to `J₀`, at every time `t ∈ [0, T₀]` with `|t - t₀| < ε`, lies in the domain and
satisfies the Legendre condition with constant `lam`.

The proof is that of the tube lemma (`tube_local_of_smooth`), with the jet as an extra variable:
the coordinates of `D_{2p}F` are continuous in `(y, t, J)` on the domain.
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

/-- The coordinates of `trivJet x₀ y (jetOfModel x₀ y J)` are `J`. -/
theorem trivJet_jetOfModel {x₀ y : M} (hy : y ∈ jetBase (I := I) 0 s (2 * p) x₀)
    (J : JetModel E 0 s (2 * p)) : trivJet (I := I) x₀ y (jetOfModel 0 s (2 * p) x₀ y J) = J := by
  funext k
  simp only [trivJet, jetOfModel]
  exact Trivialization.continuousLinearMapAt_symmL _ (mem_iInter.mp hy.2 k) (J k)

/-- The coordinates of `D_k F` at a jet are the jet derivative of the local representative. -/
theorem coordP_partialDeriv_jet {x₀ y : M} (hy : y ∈ jetBase (I := I) 0 s (2 * p) x₀) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) D.T₀) (J : JetModel E 0 s (2 * p))
    (hζ : jetOfModel 0 s (2 * p) x₀ y J ∈ D.dom t y) (k : Fin (2 * p + 1)) :
    coordP x₀ y (D.partialDeriv k t y (jetOfModel 0 s (2 * p) x₀ y J)) =
      (fderiv ℝ (fun z => localRep 0 s (2 * p) D.F x₀ (t, y, z)) J).comp
        (ContinuousLinearMap.single ℝ (fun j : Fin (2 * p + 1) => TensorRSModel 0 (s + (j : ℕ)) ℝ E)
          k) :=
  ContinuousLinearMap.ext fun μ => by
    simp only [coordP, ContinuousLinearMap.coe_comp, Function.comp_apply]
    rw [trivAt_partialDeriv D hy ht hζ k, Trivialization.continuousLinearMapAt_symmL _
      (show y ∈ (trivAt I M 0 (s + k) x₀).baseSet from mem_iInter.mp hy.2 k),
      trivJet_jetOfModel hy]
    rfl

set_option maxHeartbeats 3200000 in
/-- **Stability of parabolicity at a point.** -/
theorem stab_local (x₀ : M) {t₀ : ℝ} (ht₀ : t₀ ∈ Icc (0 : ℝ) D.T₀) (J₀ : JetModel E 0 s (2 * p))
    (hdom₀ : jetOfModel 0 s (2 * p) x₀ x₀ J₀ ∈ D.dom t₀ x₀) {lam₁ : ℝ}
    (hL : LegendreAt g 0 s p x₀ (D.principal t₀ x₀ (jetOfModel 0 s (2 * p) x₀ x₀ J₀)) lam₁) :
    ∃ lam > 0, ∃ N ∈ 𝓝 x₀, ∃ ε > 0, ∀ y ∈ N, ∀ t ∈ Icc (0 : ℝ) D.T₀, |t - t₀| < ε →
      ∀ J : JetModel E 0 s (2 * p), ‖J - J₀‖ < ε →
        jetOfModel 0 s (2 * p) x₀ y J ∈ D.dom t y ∧
          LegendreAt g 0 s p y (D.principal t y (jetOfModel 0 s (2 * p) x₀ y J)) lam := by
  classical
  have hlam₁ : 0 < lam₁ := hL.1
  have hx₀J : x₀ ∈ jetBase (I := I) 0 s (2 * p) x₀ := mem_jetBase_self 0 s (2 * p) x₀
  set q₀ : (M × ℝ) × JetModel E 0 s (2 * p) := ((x₀, t₀), J₀) with hq₀
  -- the set `S` where the local representative is defined
  set S : Set ((M × ℝ) × JetModel E 0 s (2 * p)) :=
    {q | q.1.1 ∈ jetBase (I := I) 0 s (2 * p) x₀ ∧ q.1.2 ∈ Icc (0 : ℝ) D.T₀ ∧
      jetOfModel 0 s (2 * p) x₀ q.1.1 q.2 ∈ D.dom q.1.2 q.1.1} with hS
  have hq₀S : q₀ ∈ S := ⟨hx₀J, ht₀, hdom₀⟩
  -- Step 1: the domain is open
  obtain ⟨U, hUo, hU⟩ := D.dom_relOpen x₀
  let Θ : (M × ℝ) × JetModel E 0 s (2 * p) → ℝ × M × JetModel E 0 s (2 * p) :=
    fun q => (q.1.2, q.1.1, q.2)
  have hΘ : Continuous Θ :=
    (continuous_snd.comp continuous_fst).prodMk
      ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
  have hΘq₀ : Θ q₀ ∈ U := by
    have h : Θ q₀ ∈ localDom 0 s (2 * p) D.T₀ D.dom x₀ := ⟨⟨ht₀, hx₀J⟩, hdom₀⟩
    rw [hU] at h
    exact h.1
  have hdomS : ∀ q : (M × ℝ) × JetModel E 0 s (2 * p), Θ q ∈ U →
      q.1.1 ∈ jetBase (I := I) 0 s (2 * p) x₀ → q.1.2 ∈ Icc (0 : ℝ) D.T₀ → q ∈ S := by
    intro q hqU hqb hqt
    have h : Θ q ∈ localDom 0 s (2 * p) D.T₀ D.dom x₀ := by
      rw [hU]
      exact ⟨hqU, hqt, hqb⟩
    exact ⟨hqb, hqt, h.2⟩
  -- Step 2: the Legendre condition in coordinates
  obtain ⟨Λ, Bf, hΛ, hBf, hev⟩ := exists_legendre_coord (s := s) (p := p) g x₀
  set A : (M × ℝ) × JetModel E 0 s (2 * p) →
      (TensorRSModel 0 (s + 2 * p) ℝ E →L[ℝ] TensorRSModel 0 s ℝ E) :=
    fun q => (fderiv ℝ (fun z => localRep 0 s (2 * p) D.F x₀ (q.1.2, q.1.1, z)) q.2).comp
      (ContinuousLinearMap.single ℝ
        (fun j : Fin (2 * p + 1) => TensorRSModel 0 (s + (j : ℕ)) ℝ E) (Fin.last (2 * p))) with hA
  have hAc : ∀ q ∈ S, ContinuousWithinAt A S q := by
    intro q hq
    have hφ : ContMDiffWithinAt ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, JetModel E 0 s (2 * p)))
        (𝓘(ℝ, ℝ).prod I) ∞ (fun n : (M × ℝ) × JetModel E 0 s (2 * p) => (n.1.2, n.1.1)) S q :=
      (((contMDiff_snd.comp contMDiff_fst).prodMk (contMDiff_fst.comp contMDiff_fst)) q).contMDiffWithinAt
    have hγ : ContMDiffWithinAt ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, JetModel E 0 s (2 * p)))
        𝓘(ℝ, JetModel E 0 s (2 * p)) ∞ (fun n : (M × ℝ) × JetModel E 0 s (2 * p) => n.2) S q :=
      (contMDiff_snd q).contMDiffWithinAt
    have hmem : ∀ n ∈ S, ((n.1.2, n.1.1) : ℝ × M).1 ∈ Icc (0 : ℝ) D.T₀ ∧
        ((n.1.2, n.1.1) : ℝ × M).2 ∈ jetBase (I := I) 0 s (2 * p) x₀ ∧
        jetOfModel 0 s (2 * p) x₀ ((n.1.2, n.1.1) : ℝ × M).2 n.2 ∈
          D.dom ((n.1.2, n.1.1) : ℝ × M).1 ((n.1.2, n.1.1) : ℝ × M).2 :=
      fun n hn => ⟨hn.2.1, hn.1, hn.2.2⟩
    exact ((D.contMDiffWithinAt_fderiv_localRep x₀ hq hφ hγ hmem).clm_comp
      contMDiffWithinAt_const).continuousWithinAt
  obtain ⟨-, hlamL⟩ := hL
  have hstep2 : ∀ w ∈ Metric.sphere (0 : TensorRSModel 0 (s + p) ℝ E) 1,
      ∀ᶠ z : ((M × ℝ) × JetModel E 0 s (2 * p)) × TensorRSModel 0 (s + p) ℝ E in 𝓝 (q₀, w),
        z.1 ∈ S →
          lam₁ / 2 * Bf z.1.1.1 z.2 < (-1) ^ (p + 1) * Λ z.1.1.1 (A z.1) z.2 := by
    intro w hw
    have hz1 : ‖w‖ = 1 := mem_sphere_zero_iff_norm.mp hw
    have hA' : ContinuousWithinAt (A ∘ fun z : ((M × ℝ) × JetModel E 0 s (2 * p)) ×
        TensorRSModel 0 (s + p) ℝ E => z.1) {z | z.1 ∈ S} (q₀, w) :=
      ContinuousWithinAt.comp (g := A)
        (f := fun z : ((M × ℝ) × JetModel E 0 s (2 * p)) × TensorRSModel 0 (s + p) ℝ E => z.1)
        (x := (q₀, w)) (hAc _ hq₀S) continuous_fst.continuousWithinAt fun z hz => hz
    have h11 : Continuous fun z : ((M × ℝ) × JetModel E 0 s (2 * p)) ×
        TensorRSModel 0 (s + p) ℝ E => z.1.1.1 := continuous_fst.fst.fst
    have h22 : Continuous fun z : ((M × ℝ) × JetModel E 0 s (2 * p)) ×
        TensorRSModel 0 (s + p) ℝ E => z.2 := continuous_snd
    have hΛc : ContinuousWithinAt (fun z : ((M × ℝ) × JetModel E 0 s (2 * p)) ×
        TensorRSModel 0 (s + p) ℝ E => Λ z.1.1.1 (A z.1) z.2) {z | z.1 ∈ S} (q₀, w) :=
      hΛ.continuousAt.comp_continuousWithinAt
        (h11.continuousWithinAt.prodMk (hA'.prodMk h22.continuousWithinAt))
    have hBc : ContinuousWithinAt (fun z : ((M × ℝ) × JetModel E 0 s (2 * p)) ×
        TensorRSModel 0 (s + p) ℝ E => Bf z.1.1.1 z.2) {z | z.1 ∈ S} (q₀, w) :=
      hBf.continuousAt.comp_continuousWithinAt
        (h11.continuousWithinAt.prodMk h22.continuousWithinAt)
    have hGc : ContinuousWithinAt (fun z : ((M × ℝ) × JetModel E 0 s (2 * p)) ×
        TensorRSModel 0 (s + p) ℝ E =>
          (-1) ^ (p + 1) * Λ z.1.1.1 (A z.1) z.2 - lam₁ / 2 * Bf z.1.1.1 z.2)
        {z | z.1 ∈ S} (q₀, w) :=
      (continuousWithinAt_const.mul hΛc).sub (continuousWithinAt_const.mul hBc)
    have hpos : 0 < (-1) ^ (p + 1) * Λ x₀ (A q₀) w - lam₁ / 2 * Bf x₀ w := by
      obtain ⟨hΛx, hBx⟩ := hev.self_of_nhds (A q₀) w
      have hcoord : A q₀ = coordP x₀ x₀ (D.partialDeriv (Fin.last (2 * p)) t₀ x₀
          (jetOfModel 0 s (2 * p) x₀ x₀ J₀)) :=
        (D.coordP_partialDeriv_jet hx₀J ht₀ J₀ hdom₀ (Fin.last (2 * p))).symm
      have key := hlamL ((trivAt I M 0 (s + p) x₀).symmL ℝ x₀ w)
      rw [D.principal_eq_fibMap hx₀J, ← hcoord, hΛx, hBx] at key
      have hBpos : 0 < Bf x₀ w := by
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
      (hGc.preimage_mem_nhdsWithin (Ioi_mem_nhds hpos))] with z hz hzS
    have := hz hzS
    simp only [mem_Ioi] at this
    linarith
  have hLegEv := (isCompact_sphere (0 : TensorRSModel 0 (s + p) ℝ E) 1).eventually_forall_of_forall_eventually
    (P := fun q (w : TensorRSModel 0 (s + p) ℝ E) => q ∈ S →
      lam₁ / 2 * Bf q.1.1 w < (-1) ^ (p + 1) * Λ q.1.1 (A q) w) hstep2
  -- Step 3: a neighbourhood of the centre
  have hfst : Tendsto (fun q : (M × ℝ) × JetModel E 0 s (2 * p) => q.1.1) (𝓝 q₀) (𝓝 x₀) :=
    (continuous_fst.comp continuous_fst).tendsto q₀
  have hall : ∀ᶠ q : (M × ℝ) × JetModel E 0 s (2 * p) in 𝓝 q₀, Θ q ∈ U ∧
      (∀ w ∈ Metric.sphere (0 : TensorRSModel 0 (s + p) ℝ E) 1, q ∈ S →
        lam₁ / 2 * Bf q.1.1 w < (-1) ^ (p + 1) * Λ q.1.1 (A q) w) ∧
      (∀ Q z, legendreForm g 0 s p q.1.1 ((fibMap I (s + 2 * p) s x₀ q.1.1 Q).comp
          (EquationData.castIdx (r := 0) (by omega : s + p + p = s + 2 * p)
            q.1.1).toContinuousLinearMap)
          ((trivAt I M 0 (s + p) x₀).symmL ℝ q.1.1 z) ((trivAt I M 0 (s + p) x₀).symmL ℝ q.1.1 z) =
            Λ q.1.1 Q z ∧
        fiberInner g 0 (s + p) q.1.1 ((trivAt I M 0 (s + p) x₀).symmL ℝ q.1.1 z)
          ((trivAt I M 0 (s + p) x₀).symmL ℝ q.1.1 z) = Bf q.1.1 z) ∧
      q.1.1 ∈ jetBase (I := I) 0 s (2 * p) x₀ :=
    Filter.Eventually.and ((hUo.preimage hΘ).mem_nhds hΘq₀) (hLegEv.and
      ((hfst.eventually hev).and
        (hfst.eventually ((isOpen_jetBase 0 s (2 * p) x₀).mem_nhds hx₀J))))
  obtain ⟨W1, hW1, W2, hW2, hW⟩ := mem_nhds_prod_iff.mp hall
  obtain ⟨N, hN, V, hV, hNV⟩ := mem_nhds_prod_iff.mp hW1
  obtain ⟨ε₁, hε₁, hε₁V⟩ := Metric.mem_nhds_iff.mp hV
  obtain ⟨ε₂, hε₂, hε₂W⟩ := Metric.mem_nhds_iff.mp hW2
  refine ⟨lam₁ / 2, half_pos hlam₁, N, hN, min ε₁ ε₂, lt_min hε₁ hε₂,
    fun y hy t ht htε J hJ => ?_⟩
  have htV : t ∈ V := hε₁V (by
    rw [Metric.mem_ball, Real.dist_eq]
    exact lt_of_lt_of_le htε (min_le_left _ _))
  have hJW : J ∈ W2 := hε₂W (by
    rw [Metric.mem_ball, dist_eq_norm]
    exact lt_of_lt_of_le hJ (min_le_right _ _))
  obtain ⟨hqU, hqLeg, hqev, hqJ⟩ := hW (mk_mem_prod (hNV (mk_mem_prod hy htV)) hJW)
  have hqS := hdomS ((y, t), J) hqU hqJ ht
  have hdomJ := hqS.2.2
  refine ⟨hdomJ, half_pos hlam₁, fun ξ => ?_⟩
  have hcoord : A ((y, t), J) = coordP x₀ y (D.partialDeriv (Fin.last (2 * p)) t y
      (jetOfModel 0 s (2 * p) x₀ y J)) :=
    (D.coordP_partialDeriv_jet hqJ ht J hdomJ (Fin.last (2 * p))).symm
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
        (-1) ^ (p + 1) * legendreForm g 0 s p y ((fibMap I (s + 2 * p) s x₀ y (A ((y, t), J))).comp
          (EquationData.castIdx (r := 0) (by omega : s + p + p = s + 2 * p) y).toContinuousLinearMap)
          ((trivAt I M 0 (s + p) x₀).symmL ℝ y (‖z‖⁻¹ • z))
          ((trivAt I M 0 (s + p) x₀).symmL ℝ y (‖z‖⁻¹ • z)) := by
      have h1 := hqLeg (‖z‖⁻¹ • z) hzh hqS
      obtain ⟨hΛy, hBy⟩ := hqev (A ((y, t), J)) (‖z‖⁻¹ • z)
      dsimp only at h1 hΛy hBy
      rw [hΛy, hBy]
      exact h1
    have hξ' : ξ = ‖z‖ • (trivAt I M 0 (s + p) x₀).symmL ℝ y (‖z‖⁻¹ • z) := by
      rw [← map_smul, smul_inv_smul₀ (norm_ne_zero_iff.mpr hz0)]
      exact hξ
    rw [hξ', legendreForm_smul_smul, fiberInner_smul_smul]
    have hn : 0 < ‖z‖ ^ 2 := by positivity
    exact mul_le_mul_of_lt_aux hn hlt

end EquationData

end ShortTime
