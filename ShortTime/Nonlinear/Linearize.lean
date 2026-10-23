import ShortTime.Nonlinear.ModelCoords
import ShortTime.Nonlinear.OpField
import ShortTime.Nonlinear.LocalRep
import ShortTime.Analysis.ParamIntegralManifold

/-!
# The difference of two solutions solves a linear parabolic equation

Let `u, v` be solutions of `∂ₜu = F(t, j^{2p}u)` on a covariant bundle `T⁰_s M`, and suppose the
segment between their jets stays in the domain and satisfies the Legendre condition. Then
`h = u - v` solves `∂ₜh = Σ_k Ã_k(t) ∇^k h` with the averaged coefficients
`Ã_k(t) = ∫₀¹ D_k F(t, j(v + σh)) dσ`, and this operator is parabolic (`exists_linearized`).

The smoothness of the equation data is read in local trivializations: `contDiffAt_Fmod` (fibrewise)
and `exists_avg_coeff` (the averaged coefficients are jointly smooth). The calculus along the
segment is in `ShortTime.Nonlinear.ModelCoords`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set MeasureTheory
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open scoped Manifold ContDiff BigOperators Topology

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-! ### The linearized operator -/

namespace EquationData

variable {s p : ℕ} (D : EquationData I M 0 s p) {g : SmoothRiemannianMetric I M}

/-- `F` is smooth on the fibres of its domain (read in the model). -/
theorem contDiffAt_Fmod {r s p : ℕ} (D : EquationData I M r s p) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) D.T₀) (x : M) {ζ : CovJetFiber I r s (2 * p) x} (hζ : ζ ∈ D.dom t x) :
    ContDiffAt ℝ ∞ (D.Fmod t x) (jetIso I r s (2 * p) x ζ) := by
  -- the trivializations at `x` itself
  have hx₀ : x ∈ (trivAt I M r s x).baseSet := mem_baseSet_trivializationAt _ _ x
  have hxk : ∀ k : Fin (2 * p + 1), x ∈ (trivAt I M r (s + k) x).baseSet :=
    fun k => mem_baseSet_trivializationAt _ _ x
  have hxJ : x ∈ jetBase (I := I) r s (2 * p) x := ⟨hx₀, mem_iInter.mpr hxk⟩
  -- the linear changes of coordinates between the model and the trivializations
  let Ψ : TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E :=
    (tensorRSSpaceContinuousLinearEquiv (I := I) r s x).toContinuousLinearMap.comp
      ((trivAt I M r s x).symmL ℝ x)
  let Φ : JetModel E r s (2 * p) →L[ℝ] JetModel E r s (2 * p) :=
    ContinuousLinearMap.pi fun k => ((trivAt I M r (s + k) x).continuousLinearMapAt ℝ x).comp
      ((tensorRSSpaceContinuousLinearEquiv (I := I) r (s + k) x).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.proj k))
  have hjet : ∀ z, jetOfModel r s (2 * p) x x (Φ z) = (jetIso I r s (2 * p) x).symm z := by
    intro z
    funext k
    simp only [jetOfModel, Φ, ContinuousLinearMap.pi_apply, ContinuousLinearMap.coe_comp,
      Function.comp_apply, ContinuousLinearMap.proj_apply, ContinuousLinearEquiv.coe_coe]
    rw [Trivialization.symmL_continuousLinearMapAt _ (hxk k)]
    rfl
  -- `Fmod` is the local representative, between the two linear maps
  let G : JetModel E r s (2 * p) → TensorRSModel r s ℝ E :=
    fun z' => localRep r s (2 * p) D.F x (t, x, z')
  have hFG : D.Fmod t x = Ψ ∘ G ∘ Φ := by
    funext z
    simp only [Function.comp_apply, G, localRep, Ψ, ContinuousLinearMap.coe_comp,
      ContinuousLinearEquiv.coe_coe]
    rw [hjet, Trivialization.symmL_continuousLinearMapAt _ hx₀]
    rfl
  -- smoothness of the local representative in the jet variable
  let ι : JetModel E r s (2 * p) → ℝ × M × JetModel E r s (2 * p) := fun z' => (t, x, z')
  have hι : ContMDiff 𝓘(ℝ, JetModel E r s (2 * p)) (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, JetModel E r s (2 * p))))
      ∞ ι :=
    contMDiff_const.prodMk (contMDiff_const.prodMk contMDiff_id)
  obtain ⟨U, hU, hdom⟩ := D.dom_relOpen x
  have hpre : ι ⁻¹' localDom r s (2 * p) D.T₀ D.dom x = ι ⁻¹' U := by
    ext z
    simp only [mem_preimage, hdom, mem_inter_iff, and_iff_left_iff_imp]
    exact fun _ => ⟨ht, hxJ⟩
  have hGon : ContMDiffOn 𝓘(ℝ, JetModel E r s (2 * p)) 𝓘(ℝ, TensorRSModel r s ℝ E) ∞ G
      (ι ⁻¹' localDom r s (2 * p) D.T₀ D.dom x) :=
    (D.smooth x).comp hι.contMDiffOn fun z hz => hz
  have hz₀ : Φ (jetIso I r s (2 * p) x ζ) ∈ ι ⁻¹' localDom r s (2 * p) D.T₀ D.dom x := by
    refine ⟨⟨ht, hxJ⟩, ?_⟩
    change jetOfModel r s (2 * p) x x (Φ (jetIso I r s (2 * p) x ζ)) ∈ D.dom t x
    rw [hjet, LinearIsometryEquiv.symm_apply_apply]
    exact hζ
  have hnhds : ι ⁻¹' localDom r s (2 * p) D.T₀ D.dom x ∈ 𝓝 (Φ (jetIso I r s (2 * p) x ζ)) := by
    rw [hpre]
    rw [hpre] at hz₀
    exact (hU.preimage (continuous_const.prodMk (continuous_const.prodMk continuous_id))).mem_nhds
      hz₀
  have hG : ContDiffAt ℝ ∞ G (Φ (jetIso I r s (2 * p) x ζ)) :=
    contMDiffAt_iff_contDiffAt.mp (hGon.contMDiffAt hnhds)
  rw [hFG]
  exact Ψ.contDiff.contDiffAt.comp _ (hG.comp _ Φ.contDiff.contDiffAt)

/-! ### The partial derivatives in a trivialization -/

/-- **The pinned partial derivatives in a trivialization**: they are the partial derivatives of the
local representative `localRep` in the jet variable. -/
theorem trivAt_partialDeriv {r s p : ℕ} (D : EquationData I M r s p) {x₀ y : M}
    (hy : y ∈ jetBase (I := I) r s (2 * p) x₀) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) D.T₀)
    {ζ : CovJetFiber I r s (2 * p) y} (hζ : ζ ∈ D.dom t y) (k : Fin (2 * p + 1))
    (w : TensorRSSpace r (s + (k : ℕ)) I y) :
    (trivAt I M r s x₀).continuousLinearMapAt ℝ y (D.partialDeriv k t y ζ w) =
      fderiv ℝ (fun z => localRep r s (2 * p) D.F x₀ (t, y, z)) (trivJet x₀ y ζ)
        (Pi.single k ((trivAt I M r (s + k) x₀).continuousLinearMapAt ℝ y w)) := by
  have hyk : ∀ k : Fin (2 * p + 1), y ∈ (trivAt I M r (s + k) x₀).baseSet :=
    fun k => mem_iInter.mp hy.2 k
  let Ψ : TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E :=
    ((trivAt I M r s x₀).continuousLinearMapAt ℝ y).comp
      (tensorRSSpaceContinuousLinearEquiv (I := I) r s y).symm.toContinuousLinearMap
  let Φ : JetModel E r s (2 * p) →L[ℝ] JetModel E r s (2 * p) :=
    ContinuousLinearMap.pi fun k => (tensorRSSpaceContinuousLinearEquiv (I := I) r (s + k)
      y).toContinuousLinearMap.comp (((trivAt I M r (s + k) x₀).symmL ℝ y).comp
        (ContinuousLinearMap.proj k))
  have hΦ : ∀ z, (jetIso I r s (2 * p) y).symm (Φ z) = jetOfModel r s (2 * p) x₀ y z := by
    intro z
    funext k
    rw [jetIso_symm_apply]
    exact (tensorRSSpaceContinuousLinearEquiv (I := I) r (s + k) y).symm_apply_apply _
  have hG : (fun z => localRep r s (2 * p) D.F x₀ (t, y, z)) = Ψ ∘ D.Fmod t y ∘ Φ := by
    funext z
    simp only [Function.comp_apply, Ψ, ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe,
      EquationData.Fmod, hΦ]
    rw [fibIso_apply]
    simp only [localRep]
    congr 1
  have hz₀ : Φ (trivJet x₀ y ζ) = jetIso I r s (2 * p) y ζ := by
    apply (jetIso I r s (2 * p) y).symm.injective
    rw [hΦ, LinearIsometryEquiv.symm_apply_apply, jetOfModel_trivJet hy]
  have hdiff : DifferentiableAt ℝ (D.Fmod t y) (Φ (trivJet x₀ y ζ)) := by
    rw [hz₀]
    exact (D.contDiffAt_Fmod ht y hζ).differentiableAt (by simp)
  have hderiv : HasFDerivAt (Ψ ∘ D.Fmod t y ∘ Φ)
      (Ψ.comp ((fderiv ℝ (D.Fmod t y) (Φ (trivJet x₀ y ζ))).comp Φ)) (trivJet x₀ y ζ) :=
    Ψ.hasFDerivAt.comp _ (hdiff.hasFDerivAt.comp _ Φ.hasFDerivAt)
  have hΦs : Φ (Pi.single k ((trivAt I M r (s + k) x₀).continuousLinearMapAt ℝ y w)) =
      Pi.single k (fibIso I r (s + k) y w) := by
    funext j
    simp only [Φ, ContinuousLinearMap.pi_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.proj_apply, ContinuousLinearEquiv.coe_coe]
    by_cases h : j = k
    · subst h
      simp only [Pi.single_eq_same]
      rw [Trivialization.symmL_continuousLinearMapAt _ (hyk j)]
      rfl
    · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, map_zero, map_zero]
  rw [hG, hderiv.fderiv]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, hΦs, hz₀]
  rw [← fibIso_partialDeriv]
  simp only [Ψ, ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearEquiv.coe_coe,
    fibIso_apply]
  congr 1

/-! ### The averaged coefficients -/

theorem trivJet_segment {r s N : ℕ} (x₀ y : M) (ζ₀ ζ₁ : CovJetFiber I r s N y) (σ : ℝ) :
    trivJet x₀ y (ζ₀ + σ • (ζ₁ - ζ₀)) =
      trivJet x₀ y ζ₀ + σ • (trivJet x₀ y ζ₁ - trivJet x₀ y ζ₀) := by
  funext k
  simp only [trivJet, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, map_add, map_smul, map_sub]

/-- The integrand of the averaged coefficients, in the trivializations at `x₀`. -/
def avgIntegrand {s p : ℕ} (D : EquationData I M 0 s p) {g : SmoothRiemannianMetric I M}
    (u v : ℝ → SmoothCcTensor g 0 s) (t₀ : ℝ) (x₀ : M) (k : Fin (2 * p + 1)) (q : M × ℝ)
    (σ : ℝ) : TensorRSModel 0 (s + (k : ℕ)) ℝ E →L[ℝ] TensorRSModel 0 s ℝ E :=
  (fderiv ℝ (fun z => localRep 0 s (2 * p) D.F x₀ (t₀ + q.2, q.1, z))
    (trivJet x₀ q.1 (covJet g 0 s (2 * p) (v (t₀ + q.2) + σ • (u (t₀ + q.2) - v (t₀ + q.2)))
      q.1))).comp
    (ContinuousLinearMap.single ℝ (fun j : Fin (2 * p + 1) => TensorRSModel 0 (s + (j : ℕ)) ℝ E) k)

theorem avgIntegrand_apply {s p : ℕ} (D : EquationData I M 0 s p) {g : SmoothRiemannianMetric I M}
    (u v : ℝ → SmoothCcTensor g 0 s) (t₀ : ℝ) (x₀ y : M) (k : Fin (2 * p + 1)) (τ σ : ℝ)
    (μ : TensorRSModel 0 (s + (k : ℕ)) ℝ E) :
    avgIntegrand D u v t₀ x₀ k (y, τ) σ μ =
      fderiv ℝ (fun z => localRep 0 s (2 * p) D.F x₀ (t₀ + τ, y, z))
        (trivJet x₀ y (covJet g 0 s (2 * p) (v (t₀ + τ) + σ • (u (t₀ + τ) - v (t₀ + τ))) y))
        (Pi.single k μ) :=
  rfl

/-- The coordinates of `D_k F` at a jet of the segment are the integrand `avgIntegrand`. -/
theorem coordP_partialDeriv_segment {u v : ℝ → SmoothCcTensor g 0 s} {t₀ τ σ : ℝ} {x₀ y : M}
    (hy : y ∈ jetBase (I := I) 0 s (2 * p) x₀) (hT : t₀ + τ ∈ Icc (0 : ℝ) D.T₀)
    (hζ : covJet g 0 s (2 * p) (v (t₀ + τ) + σ • (u (t₀ + τ) - v (t₀ + τ))) y ∈ D.dom (t₀ + τ) y)
    (k : Fin (2 * p + 1)) :
    coordP x₀ y (D.partialDeriv k (t₀ + τ) y
        (covJet g 0 s (2 * p) (v (t₀ + τ) + σ • (u (t₀ + τ) - v (t₀ + τ))) y)) =
      avgIntegrand D u v t₀ x₀ k (y, τ) σ :=
  ContinuousLinearMap.ext fun μ => by
    simp only [coordP, ContinuousLinearMap.coe_comp, Function.comp_apply]
    rw [trivAt_partialDeriv D hy hT hζ k, Trivialization.continuousLinearMapAt_symmL _
      (show y ∈ (trivAt I M 0 (s + k) x₀).baseSet from mem_iInter.mp hy.2 k), avgIntegrand_apply]

/-- The jets on the segment between two solutions, in the trivializations at `x₀`, are jointly
smooth in `(x, τ, σ)`. -/
theorem contMDiffOn_trivJet_segment {T : ℝ}
    {u v : ℝ → SmoothCcTensor g 0 s}
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u) (hv : JointlySmoothOn g 0 s (Icc 0 T) v)
    (_hTD : T ≤ D.T₀)
    {t₀ η : ℝ} (ht₀ : 0 ≤ t₀) (hηT : t₀ + η ≤ T) (x₀ : M) :
    ContMDiffOn ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, JetModel E 0 s (2 * p)) ∞
      (fun n : (M × ℝ) × ℝ => trivJet x₀ n.1.1 (covJet g 0 s (2 * p)
        (v (t₀ + n.1.2) + n.2 • (u (t₀ + n.1.2) - v (t₀ + n.1.2))) n.1.1))
      ((jetBase (I := I) 0 s (2 * p) x₀ ×ˢ Icc 0 η) ×ˢ Icc (0 : ℝ) 1) := by
  have hmaps : ∀ τ ∈ Icc (0 : ℝ) η, t₀ + τ ∈ Icc (0 : ℝ) T :=
    fun τ hτ => ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  have hus := contMDiffOn_trivJet_covJet (N := 2 * p)
    (jointlySmoothOn_shift hu t₀ hmaps) x₀
  have hvs := contMDiffOn_trivJet_covJet (N := 2 * p)
    (jointlySmoothOn_shift hv t₀ hmaps) x₀
  intro n hn
  have hfst : ContMDiffWithinAt ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) ∞
      (Prod.fst : (M × ℝ) × ℝ → M × ℝ)
      ((jetBase (I := I) 0 s (2 * p) x₀ ×ˢ Icc 0 η) ×ˢ Icc (0 : ℝ) 1) n :=
    contMDiffWithinAt_fst
  have hzu := (hus n.1 hn.1).comp n hfst fun m hm => hm.1
  have hzv := (hvs n.1 hn.1).comp n hfst fun m hm => hm.1
  have hσ : ContMDiffWithinAt ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun m : (M × ℝ) × ℝ => m.2)
      ((jetBase (I := I) 0 s (2 * p) x₀ ×ˢ Icc 0 η) ×ˢ Icc (0 : ℝ) 1) n :=
    contMDiffWithinAt_snd
  refine (hzv.add (hσ.smul (hzu.sub hzv))).congr (fun m _ => ?_) ?_
  · simp only [Function.comp_apply, covJet_segment, trivJet_segment, Pi.add_apply,
      Pi.smul_apply']
  · simp only [Function.comp_apply, covJet_segment, trivJet_segment, Pi.add_apply,
      Pi.smul_apply']

/-- The integrand is smooth on any set `R ⊆ (W × [0, η]) × [0, 1]` on which the jets of the segment
lie in the domain. -/
theorem contMDiffOn_avgIntegrand_of_subset {T : ℝ}
    {u v : ℝ → SmoothCcTensor g 0 s}
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u) (hv : JointlySmoothOn g 0 s (Icc 0 T) v)
    (hTD : T ≤ D.T₀)
    {t₀ η : ℝ} (ht₀ : 0 ≤ t₀) (hηT : t₀ + η ≤ T) (x₀ : M) {R : Set ((M × ℝ) × ℝ)}
    (hR : R ⊆ (jetBase (I := I) 0 s (2 * p) x₀ ×ˢ Icc 0 η) ×ˢ Icc (0 : ℝ) 1)
    (hdomR : ∀ m ∈ R, covJet g 0 s (2 * p)
      (v (t₀ + m.1.2) + m.2 • (u (t₀ + m.1.2) - v (t₀ + m.1.2))) m.1.1 ∈ D.dom (t₀ + m.1.2) m.1.1)
    (k : Fin (2 * p + 1)) :
    ContMDiffOn ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, TensorRSModel 0 (s + (k : ℕ)) ℝ E →L[ℝ] TensorRSModel 0 s ℝ E) ∞
      (fun n : (M × ℝ) × ℝ => avgIntegrand D u v t₀ x₀ k n.1 n.2) R := by
  have hγ := D.contMDiffOn_trivJet_segment hu hv hTD ht₀ hηT x₀
  intro n hn
  have hφ : ContMDiffWithinAt ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod I) ∞
      (fun n : (M × ℝ) × ℝ => (t₀ + n.1.2, n.1.1)) R n :=
    ((((contDiff_const.add contDiff_id).contMDiff.comp (contMDiff_snd.comp contMDiff_fst)).prodMk
        (contMDiff_fst.comp contMDiff_fst)) n).contMDiffWithinAt
  have hmem : ∀ m ∈ R,
      ((t₀ + m.1.2, m.1.1) : ℝ × M).1 ∈ Icc (0 : ℝ) D.T₀ ∧
        ((t₀ + m.1.2, m.1.1) : ℝ × M).2 ∈ jetBase (I := I) 0 s (2 * p) x₀ ∧
        jetOfModel 0 s (2 * p) x₀ ((t₀ + m.1.2, m.1.1) : ℝ × M).2
          (trivJet x₀ m.1.1 (covJet g 0 s (2 * p)
            (v (t₀ + m.1.2) + m.2 • (u (t₀ + m.1.2) - v (t₀ + m.1.2))) m.1.1)) ∈
          D.dom ((t₀ + m.1.2, m.1.1) : ℝ × M).1 ((t₀ + m.1.2, m.1.1) : ℝ × M).2 := by
    intro m hm
    have hm' := hR hm
    refine ⟨⟨by linarith [hm'.1.2.1], by linarith [hm'.1.2.2, hTD]⟩, hm'.1.1, ?_⟩
    rw [jetOfModel_trivJet hm'.1.1]
    exact hdomR m hm
  exact (D.contMDiffWithinAt_fderiv_localRep x₀ hn hφ ((hγ n (hR hn)).mono hR) hmem).clm_comp
    contMDiffWithinAt_const

/-- The integrand is smooth on `(W × [0, η]) × [0, 1]`, `W` the jet trivialization domain at `x₀`.
-/
theorem contMDiffOn_avgIntegrand {T : ℝ}
    {u v : ℝ → SmoothCcTensor g 0 s}
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u) (hv : JointlySmoothOn g 0 s (Icc 0 T) v)
    (hTD : T ≤ D.T₀)
    {t₀ η : ℝ} (ht₀ : 0 ≤ t₀) (hηT : t₀ + η ≤ T)
    (hdom : ∀ t ∈ Icc t₀ (t₀ + η), ∀ x : M, ∀ σ ∈ Icc (0 : ℝ) 1,
      covJet g 0 s (2 * p) (v t + σ • (u t - v t)) x ∈ D.dom t x)
    (x₀ : M) (k : Fin (2 * p + 1)) :
    ContMDiffOn ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, TensorRSModel 0 (s + (k : ℕ)) ℝ E →L[ℝ] TensorRSModel 0 s ℝ E) ∞
      (fun n : (M × ℝ) × ℝ => avgIntegrand D u v t₀ x₀ k n.1 n.2)
      ((jetBase (I := I) 0 s (2 * p) x₀ ×ˢ Icc 0 η) ×ˢ Icc (0 : ℝ) 1) :=
  D.contMDiffOn_avgIntegrand_of_subset hu hv hTD ht₀ hηT x₀ subset_rfl
    (fun m hm => hdom _ ⟨by linarith [hm.1.2.1], by linarith [hm.1.2.2]⟩ _ _ hm.2) k

/-- The coordinates of the averaged coefficient are the integral of `avgIntegrand`. -/
theorem coordP_avg {T : ℝ}
    {u v : ℝ → SmoothCcTensor g 0 s}
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u) (hv : JointlySmoothOn g 0 s (Icc 0 T) v)
    (hTD : T ≤ D.T₀)
    {t₀ η : ℝ} (ht₀ : 0 ≤ t₀) (hηT : t₀ + η ≤ T)
    (hdom : ∀ t ∈ Icc t₀ (t₀ + η), ∀ x : M, ∀ σ ∈ Icc (0 : ℝ) 1,
      covJet g 0 s (2 * p) (v t + σ • (u t - v t)) x ∈ D.dom t x)
    {x₀ y : M} (hy : y ∈ jetBase (I := I) 0 s (2 * p) x₀) (k : Fin (2 * p + 1)) {τ : ℝ}
    (hτ : τ ∈ Icc (0 : ℝ) η) :
    coordP x₀ y (avgFib (fun σ => D.partialDeriv k (t₀ + τ) y
        (covJet g 0 s (2 * p) (v (t₀ + τ) + σ • (u (t₀ + τ) - v (t₀ + τ))) y))) =
      ∫ σ in (0 : ℝ)..1, avgIntegrand D u v t₀ x₀ k (y, τ) σ := by
  have ht : t₀ + τ ∈ Icc t₀ (t₀ + η) := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  have hT₀ : t₀ + τ ∈ Icc (0 : ℝ) D.T₀ := ⟨by linarith [hτ.1], by linarith [hτ.2, hTD]⟩
  have hdom' : ∀ σ ∈ Icc (0 : ℝ) 1, covJet g 0 s (2 * p)
      (v (t₀ + τ) + σ • (u (t₀ + τ) - v (t₀ + τ))) y ∈ D.dom (t₀ + τ) y :=
    fun σ hσ => hdom _ ht y σ hσ
  -- the partial derivatives along the segment are continuous
  have hC1 : ∀ σ ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 1 (D.Fmod (t₀ + τ) y) (jetIso I 0 s (2 * p) y
      (covJet g 0 s (2 * p) (v (t₀ + τ)) y + σ • (covJet g 0 s (2 * p) (u (t₀ + τ)) y -
        covJet g 0 s (2 * p) (v (t₀ + τ)) y))) := by
    intro σ hσ
    have h := hdom' σ hσ
    rw [covJet_segment] at h
    exact (D.contDiffAt_Fmod hT₀ y h).of_le (by norm_num)
  have hcont := D.continuousOn_partialDeriv_segment hC1 k
  simp_rw [← covJet_segment] at hcont
  -- the integrand is continuous in `σ`
  have hGc : ContinuousOn (fun σ => avgIntegrand D u v t₀ x₀ k (y, τ) σ) (Icc 0 1) := by
    have hf : ContinuousOn (fun σ : ℝ => (((y, τ) : M × ℝ), σ)) (Icc (0 : ℝ) 1) :=
      (continuous_const.prodMk continuous_id).continuousOn
    have h := (D.contMDiffOn_avgIntegrand hu hv hTD ht₀ hηT hdom x₀ k).continuousOn.comp hf
      fun σ hσ => mk_mem_prod (mk_mem_prod hy hτ) hσ
    simp only [Function.comp_def] at h
    exact h
  have hGi : IntervalIntegrable (fun σ => avgIntegrand D u v t₀ x₀ k (y, τ) σ) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rwa [uIcc_of_le zero_le_one]
  refine ContinuousLinearMap.ext fun μ => ?_
  let Ψ : TensorRSModel 0 s ℝ E →L[ℝ] TensorRSModel 0 s ℝ E :=
    ((trivAt I M 0 s x₀).continuousLinearMapAt ℝ y).comp
      (tensorRSSpaceContinuousLinearEquiv (I := I) 0 s y).symm.toContinuousLinearMap
  have hΨ : ∀ T : TensorRSSpace 0 s I y,
      (trivAt I M 0 s x₀).continuousLinearMapAt ℝ y T = Ψ (TensorRSSpace.toModel T) := by
    intro T
    simp only [Ψ, ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearEquiv.coe_coe]
    congr 1
  have hint : IntervalIntegrable (fun σ => TensorRSSpace.toModel (D.partialDeriv k (t₀ + τ) y
      (covJet g 0 s (2 * p) (v (t₀ + τ) + σ • (u (t₀ + τ) - v (t₀ + τ))) y)
      ((trivAt I M 0 (s + k) x₀).symmL ℝ y μ))) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    exact hcont _
  simp only [coordP, ContinuousLinearMap.coe_comp, Function.comp_apply]
  rw [hΨ, avgFib_apply hcont, ← ContinuousLinearMap.intervalIntegral_comp_comm Ψ hint,
    ContinuousLinearMap.intervalIntegral_apply hGi]
  refine intervalIntegral.integral_congr fun σ hσ => ?_
  rw [uIcc_of_le zero_le_one] at hσ
  rw [← hΨ, trivAt_partialDeriv D hy hT₀ (hdom' σ hσ) k,
    Trivialization.continuousLinearMapAt_symmL _
      (show y ∈ (trivAt I M 0 (s + k) x₀).baseSet from mem_iInter.mp hy.2 k), avgIntegrand_apply]

/-- **The averaged coefficients are jointly smooth.** Along a segment of jets inside the domain,
the operator fields with values `∫₀¹ D_kF(t, j(v + σ(u - v))) dσ` are jointly smooth. -/
theorem contMDiffOn_opFieldOf_avg {T : ℝ}
    {u v : ℝ → SmoothCcTensor g 0 s}
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u) (hv : JointlySmoothOn g 0 s (Icc 0 T) v)
    (hTD : T ≤ D.T₀)
    {t₀ η : ℝ} (ht₀ : 0 ≤ t₀) (hη : 0 < η) (hηT : t₀ + η ≤ T)
    (hdom : ∀ t ∈ Icc t₀ (t₀ + η), ∀ x : M, ∀ σ ∈ Icc (0 : ℝ) 1,
      covJet g 0 s (2 * p) (v t + σ • (u t - v t)) x ∈ D.dom t x) (k : Fin (2 * p + 1)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel (s + (k : ℕ)) s ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel (s + (k : ℕ)) s ℝ E)
        (E := fun x : M => TensorRSSpace (s + (k : ℕ)) s I x) q.1
        (opFieldOf (avgFib (fun σ => D.partialDeriv k (t₀ + q.2) q.1
          (covJet g 0 s (2 * p) (v (t₀ + q.2) + σ • (u (t₀ + q.2) - v (t₀ + q.2))) q.1)))))
      ((univ : Set M) ×ˢ Icc 0 η) := by
  rintro ⟨x₀, τ₀⟩ ⟨-, hτ₀⟩
  rw [contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  -- the trivialization domain at `x₀`
  set W := (trivializationAt E (TangentSpace I) x₀).baseSet ∩ jetBase (I := I) 0 s (2 * p) x₀
    with hW
  have hWo : IsOpen W := by
    refine (trivializationAt E (TangentSpace I) x₀).open_baseSet.inter ?_
    exact (trivAt I M 0 s x₀).open_baseSet.inter (isOpen_iInter_of_finite fun k =>
      (trivAt I M 0 (s + k) x₀).open_baseSet)
  have hx₀W : x₀ ∈ W := ⟨mem_baseSet_trivializationAt _ _ x₀,
    mem_baseSet_trivializationAt _ _ x₀,
    mem_iInter.mpr fun k => mem_baseSet_trivializationAt _ _ x₀⟩
  -- the integral of the integrand is smooth
  have hG := (D.contMDiffOn_avgIntegrand hu hv hTD ht₀ hηT hdom x₀ k).mono
    (t := (W ×ˢ Icc (0 : ℝ) η) ×ˢ Icc (0 : ℝ) 1)
    (prod_mono (prod_mono inter_subset_right le_rfl) le_rfl)
  have hI := contMDiffOn_integral_Icc
    (f := fun y τ σ => avgIntegrand D u v t₀ x₀ k (y, τ) σ) hWo (convex_Icc 0 η)
    (uniqueDiffOn_Icc hη) hG
  have hsm : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, TensorRSModel (s + (k : ℕ)) s ℝ E) ∞
      (fun q : M × ℝ =>
        opFieldCoord (s + k) s (∫ σ in (0 : ℝ)..1, avgIntegrand D u v t₀ x₀ k q σ))
      (W ×ˢ Icc 0 η) (x₀, τ₀) :=
    contMDiffWithinAt_const.clm_comp
      ((hI _ (mk_mem_prod hx₀W hτ₀)).clm_comp contMDiffWithinAt_const)
  have hnhds : W ×ˢ Icc 0 η ∈ 𝓝[(univ : Set M) ×ˢ Icc 0 η] (x₀, τ₀) := by
    refine Filter.mem_of_superset
      (inter_mem_nhdsWithin _ (prod_mem_nhds (hWo.mem_nhds hx₀W) Filter.univ_mem)) ?_
    rintro ⟨y, τ⟩ ⟨⟨-, hτ⟩, hy, -⟩
    exact ⟨hy, hτ⟩
  refine (hsm.mono_of_mem_nhdsWithin hnhds).congr_of_eventuallyEq ?_ ?_
  · filter_upwards [hnhds] with q hq
    rw [trivAt_opFieldOf hq.1.1, D.coordP_avg hu hv hTD ht₀ hηT hdom hq.1.2 k hq.2]
  · rw [trivAt_opFieldOf hx₀W.1, D.coordP_avg hu hv hTD ht₀ hηT hdom hx₀W.2 k hτ₀]

/-- **The averaged coefficients are jointly smooth operator fields.** -/
theorem exists_avg_coeff {T : ℝ}
    {u v : ℝ → SmoothCcTensor g 0 s}
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u) (hv : JointlySmoothOn g 0 s (Icc 0 T) v)
    (hTD : T ≤ D.T₀)
    {t₀ η : ℝ} (ht₀ : 0 ≤ t₀) (hη : 0 < η) (hηT : t₀ + η ≤ T)
    (hdom : ∀ t ∈ Icc t₀ (t₀ + η), ∀ x : M, ∀ σ ∈ Icc (0 : ℝ) 1,
      covJet g 0 s (2 * p) (v t + σ • (u t - v t)) x ∈ D.dom t x) :
    ∃ A : ∀ k : Fin (2 * p + 1), ℝ → SmoothCcTensor g (s + k) s,
      (∀ k : Fin (2 * p + 1), JointlySmoothOn g (s + k) s (Icc 0 η) (A k)) ∧
      ∀ k : Fin (2 * p + 1), ∀ τ ∈ Icc (0 : ℝ) η, ∀ x : M,
        opFieldHom ((A k τ).toSection x) = avgFib (fun σ => D.partialDeriv k (t₀ + τ) x
          (covJet g 0 s (2 * p) (v (t₀ + τ) + σ • (u (t₀ + τ) - v (t₀ + τ))) x)) := by
  classical
  have hsm := D.contMDiffOn_opFieldOf_avg hu hv hTD ht₀ hη hηT hdom
  let A : ∀ k : Fin (2 * p + 1), ℝ → SmoothCcTensor g (s + k) s := fun k τ =>
    if hτ : τ ∈ Icc (0 : ℝ) η then
      { toSection :=
          { toFun := fun x => opFieldOf (avgFib (fun σ => D.partialDeriv k (t₀ + τ) x
              (covJet g 0 s (2 * p) (v (t₀ + τ) + σ • (u (t₀ + τ) - v (t₀ + τ))) x)))
            contMDiff_toFun := fun x =>
              contMDiffWithinAt_univ.mp ((hsm k (x, τ) (mk_mem_prod (mem_univ x) hτ)).comp x
                (contMDiffWithinAt_id.prodMk contMDiffWithinAt_const)
                fun y _ => mk_mem_prod (mem_univ y) hτ) }
        hasCompactSupport := HasCompactSupport.of_compactSpace _ }
    else 0
  refine ⟨A, fun k => ?_, fun k τ hτ x => ?_⟩
  · refine (hsm k).congr fun q hq => ?_
    simp only [A, dif_pos hq.2]
    rfl
  · simp only [A, dif_pos hτ]
    exact opFieldHom_opFieldOf _

/-- **The difference of two solutions solves a linear parabolic equation.** Along a parabolic
segment, `h = u - v` satisfies `∂ₜh = Σ_k Ã_k ∇^k h` with `Ã_k = ∫₀¹ D_k F(t, j(v + σh)) dσ`; this is
a parabolic `LinearOp` (time shifted to start at `t₀`). -/
theorem exists_linearized {u₀ u₀' : SmoothCcTensor g 0 s} {T : ℝ}
    {u v : ℝ → SmoothCcTensor g 0 s}
    (hu : D.IsSolution g u₀ T u) (hv : D.IsSolution g u₀' T v)
    {t₀ η lam : ℝ} (ht₀ : 0 ≤ t₀) (hη : 0 < η) (hηT : t₀ + η ≤ T) (hlam : 0 < lam)
    (hseg : ∀ t ∈ Icc t₀ (t₀ + η), ∀ x : M, ∀ σ ∈ Icc (0 : ℝ) 1,
      covJet g 0 s (2 * p) (v t + σ • (u t - v t)) x ∈ D.dom t x ∧
        LegendreAt g 0 s p x
          (D.principal t x (covJet g 0 s (2 * p) (v t + σ • (u t - v t)) x)) lam) :
    ∃ L : LinearOp g s p η, L.IsParabolic lam ∧
      ∀ τ ∈ Icc (0 : ℝ) η, ∀ x : M,
        (L.apply τ (u (t₀ + τ) - v (t₀ + τ))).toSection x =
          D.F (t₀ + τ) x (covJet g 0 s (2 * p) (u (t₀ + τ)) x) -
            D.F (t₀ + τ) x (covJet g 0 s (2 * p) (v (t₀ + τ)) x) := by
  obtain ⟨A, hA, hAeq⟩ := D.exists_avg_coeff hu.smooth hv.smooth hu.le_T₀ ht₀ hη hηT fun t ht x σ hσ => (hseg t ht x σ hσ).1
  have hmem : ∀ τ ∈ Icc (0 : ℝ) η, t₀ + τ ∈ Icc t₀ (t₀ + η) :=
    fun τ hτ => ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  have hT₀ : ∀ τ ∈ Icc (0 : ℝ) η, t₀ + τ ∈ Icc (0 : ℝ) D.T₀ :=
    fun τ hτ => ⟨by linarith [hτ.1], by linarith [hτ.2, hu.le_T₀]⟩
  -- `F` is `C¹` along the segment between the jets
  have hC1 : ∀ τ ∈ Icc (0 : ℝ) η, ∀ x : M, ∀ σ ∈ Icc (0 : ℝ) 1,
      ContDiffAt ℝ 1 (D.Fmod (t₀ + τ) x) (jetIso I 0 s (2 * p) x
        (covJet g 0 s (2 * p) (v (t₀ + τ)) x + σ • (covJet g 0 s (2 * p) (u (t₀ + τ)) x -
          covJet g 0 s (2 * p) (v (t₀ + τ)) x))) := by
    intro τ hτ x σ hσ
    have h := (hseg (t₀ + τ) (hmem τ hτ) x σ hσ).1
    rw [covJet_segment] at h
    exact (D.contDiffAt_Fmod (hT₀ τ hτ) x h).of_le (by norm_num)
  refine ⟨⟨A, hA⟩, ⟨hlam, fun τ hτ x => ?_⟩, fun τ hτ x => ?_⟩
  · -- the Legendre condition for the averaged principal coefficient
    have hcont := D.continuousOn_partialDeriv_segment (hC1 τ hτ x) ⟨2 * p, Nat.lt_succ_self _⟩
    simp_rw [← covJet_segment] at hcont
    have hLeg : ∀ σ ∈ Icc (0 : ℝ) 1, LegendreAt g 0 s p x
        ((D.partialDeriv ⟨2 * p, Nat.lt_succ_self _⟩ (t₀ + τ) x
          (covJet g 0 s (2 * p) (v (t₀ + τ) + σ • (u (t₀ + τ) - v (t₀ + τ))) x)).comp
          (EquationData.castIdx (r := 0) (by simp only; omega) x).toContinuousLinearMap)
        lam :=
      fun σ hσ => (hseg (t₀ + τ) (hmem τ hτ) x σ hσ).2
    unfold LinearOp.principal
    dsimp only
    rw [hAeq ⟨2 * p, Nat.lt_succ_self _⟩ τ hτ x, avgFib_comp_right hcont]
    refine legendreAt_avgFib g (fun w => ?_) hLeg
    simpa only [ContinuousLinearMap.comp_apply] using hcont _
  · -- the linearized equation, by the fundamental theorem of calculus
    have hsum := D.F_sub_eq_sum_avg (hC1 τ hτ x)
    simp_rw [← covJet_segment] at hsum
    rw [hsum, LinearOp.apply, toSection_finset_sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [operatorFieldApply_toSection_eq, hAeq k τ hτ x, iteratedCovGrad_sub,
      SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
    simp only [covJet, Pi.sub_apply]

end EquationData

end ShortTime
