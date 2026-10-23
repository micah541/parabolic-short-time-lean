import ShortTime.Linear.Operator
import ShortTime.Sanity.LegendreTrace
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Iterated.Linear

/-!
# Equation data in model coordinates; averages along segments of jets

Tools for the linearized difference equation (`ShortTime.Nonlinear.Linearize`): equation data read
in model coordinates, averages of fibre maps along a segment of jets, the Legendre condition for such
averages, and the fundamental theorem of calculus along the segment.

**Model coordinates.** The library equips a tensor fibre with two structures: the topology of the
bundle, and a norm transported from the model space. They agree mathematically but not
definitionally, so maps between fibres carry no usable norm. All analysis here is therefore done
in the model spaces: `fibIso` is the linear isometry from a fibre (with its norm) to the model, and
`Fmod` is `F` read through it. `fibIso_partialDeriv` connects the derivative of `Fmod` with the
pinned `EquationData.partialDeriv`.
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

/-! ### The two topologies on a fibre agree -/

/-- The bundle topology of a tensor fibre is the topology of its norm (they are equal, though not
definitionally). -/
theorem tensorRSSpace_topology_eq (r s : ℕ) (x : M) :
    tensorRSSpaceTopologicalSpace (𝕜 := ℝ) (I := I) r s x =
      @UniformSpace.toTopologicalSpace _ (@PseudoMetricSpace.toUniformSpace _
        (@SeminormedAddCommGroup.toPseudoMetricSpace _
          (@NormedAddCommGroup.toSeminormedAddCommGroup _
            (tensorRSSpaceNormedAddCommGroup (𝕜 := ℝ) (I := I) r s x)))) := by
  rw [← (tensorRSSpaceContinuousLinearEquiv (𝕜 := ℝ) (I := I) r s x).toHomeomorph.induced_eq]
  rfl

/-- `fderiv` depends on the topologies only through their values. -/
theorem fderiv_congr_top {𝕜 : Type*} [NontriviallyNormedField 𝕜] {V W : Type*} [AddCommGroup V]
    [Module 𝕜 V] [AddCommGroup W] [Module 𝕜 W] {t₁ t₂ : TopologicalSpace V}
    {u₁ u₂ : TopologicalSpace W} (ht : t₁ = t₂) (hu : u₁ = u₂) (f : V → W) (v : V) :
    (@fderiv 𝕜 _ V _ _ t₁ W _ _ u₁ f v : V → W) = @fderiv 𝕜 _ V _ _ t₂ W _ _ u₂ f v := by
  subst ht hu
  rfl

/-- The Fréchet derivative for the norms (as opposed to the bundle topologies). -/
def fderivN {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
    [NormedSpace ℝ W] (f : V → W) (v : V) : V → W :=
  fun d => fderiv ℝ f v d

/-! ### Fibres as normed spaces, in model coordinates -/

variable (I) in
/-- The fibre `T^r_s|_x`, with its norm, is isometric to the model space. -/
def fibIso (r s : ℕ) (x : M) : TensorRSSpace r s I x ≃ₗᵢ[ℝ] TensorRSModel r s ℝ E where
  toLinearEquiv := (tensorRSSpaceContinuousLinearEquiv (I := I) r s x).toLinearEquiv
  norm_map' _ := rfl

theorem fibIso_apply {r s : ℕ} {x : M} (T : TensorRSSpace r s I x) :
    fibIso I r s x T = TensorRSSpace.toModel T := rfl

variable (I) in
/-- The jet fibre, with its norm, is isometric to the jet model space. -/
def jetIso (r s N : ℕ) (x : M) : CovJetFiber I r s N x ≃ₗᵢ[ℝ] JetModel E r s N where
  toLinearEquiv := LinearEquiv.piCongrRight fun k => (fibIso I r (s + k) x).toLinearEquiv
  norm_map' ζ := by
    simp only [Pi.norm_def]
    congr 2

theorem jetIso_apply {r s N : ℕ} {x : M} (ζ : CovJetFiber I r s N x) (k : Fin (N + 1)) :
    jetIso I r s N x ζ k = TensorRSSpace.toModel (ζ k) := rfl

theorem jetIso_symm_apply {r s N : ℕ} {x : M} (z : JetModel E r s N) (k : Fin (N + 1)) :
    (jetIso I r s N x).symm z k = (fibIso I r (s + k) x).symm (z k) := rfl

theorem jetIso_symm_single {r s N : ℕ} {x : M} (k : Fin (N + 1))
    (w : TensorRSModel r (s + k) ℝ E) :
    (jetIso I r s N x).symm (Pi.single k w) = Pi.single k ((fibIso I r (s + k) x).symm w) := by
  funext j
  rw [jetIso_symm_apply]
  by_cases h : j = k
  · subst h
    simp
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, map_zero]

namespace EquationData

variable {r s p : ℕ} (D : EquationData I M r s p)

/-- `F(t, ·)` at `x`, read in model coordinates. -/
def Fmod (t : ℝ) (x : M) (z : JetModel E r s (2 * p)) : TensorRSModel r s ℝ E :=
  fibIso I r s x (D.F t x ((jetIso I r s (2 * p) x).symm z))

theorem fibIso_F (t : ℝ) (x : M) (ζ : CovJetFiber I r s (2 * p) x) :
    fibIso I r s x (D.F t x ζ) = D.Fmod t x (jetIso I r s (2 * p) x ζ) := by
  simp [Fmod]

/-- The pinned partial derivative is the derivative for the norms. -/
theorem partialDeriv_eq_fderivN (k : Fin (2 * p + 1)) (t : ℝ) (x : M)
    (ζ : CovJetFiber I r s (2 * p) x) (w : TensorRSSpace r (s + k) I x) :
    D.partialDeriv k t x ζ w = fderivN (D.F t x) ζ (Pi.single k w) := by
  have hPi : (Pi.topologicalSpace : TopologicalSpace (CovJetFiber I r s (2 * p) x)) =
      @Pi.topologicalSpace _ _ fun k : Fin (2 * p + 1) => @UniformSpace.toTopologicalSpace _
        (@PseudoMetricSpace.toUniformSpace _ (@SeminormedAddCommGroup.toPseudoMetricSpace _
          (@NormedAddCommGroup.toSeminormedAddCommGroup _
            (tensorRSSpaceNormedAddCommGroup (𝕜 := ℝ) (I := I) r (s + (k : ℕ)) x)))) :=
    congrArg _ (funext fun k : Fin (2 * p + 1) => tensorRSSpace_topology_eq r (s + (k : ℕ)) x)
  exact congrFun (fderiv_congr_top (𝕜 := ℝ) hPi (tensorRSSpace_topology_eq r s x) (D.F t x) ζ)
    (Pi.single k w)

/-- **The pinned partial derivatives in model coordinates.** -/
theorem fibIso_partialDeriv (k : Fin (2 * p + 1)) (t : ℝ) (x : M)
    (ζ : CovJetFiber I r s (2 * p) x) (w : TensorRSSpace r (s + k) I x) :
    fibIso I r s x (D.partialDeriv k t x ζ w) =
      fderiv ℝ (D.Fmod t x) (jetIso I r s (2 * p) x ζ) (Pi.single k (fibIso I r (s + k) x w)) := by
  have hF : D.Fmod t x = (fibIso I r s x) ∘
      (D.F t x ∘ ((jetIso I r s (2 * p) x).symm.toContinuousLinearEquiv)) := rfl
  calc fibIso I r s x (D.partialDeriv k t x ζ w) =
        fibIso I r s x (fderivN (D.F t x) ζ (Pi.single k w)) := by rw [partialDeriv_eq_fderivN]
    _ = _ := by
        unfold fderivN
        rw [hF, LinearIsometryEquiv.comp_fderiv, ContinuousLinearEquiv.comp_right_fderiv]
        simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
          ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
          LinearIsometryEquiv.symm_apply_apply, jetIso_symm_single,
          LinearIsometryEquiv.symm_apply_apply]

end EquationData

/-! ### Averages of fibre maps, computed in the model -/

section Average

variable {r a b : ℕ} {x : M}

/-- A fibre map, read in the model. -/
def modelCLM (P : TensorRSSpace r a I x →L[ℝ] TensorRSSpace r b I x) :
    TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r b ℝ E :=
  (tensorRSSpaceContinuousLinearEquiv (I := I) r b x).toContinuousLinearMap.comp
    (P.comp (tensorRSSpaceContinuousLinearEquiv (I := I) r a x).symm.toContinuousLinearMap)

theorem modelCLM_apply (P : TensorRSSpace r a I x →L[ℝ] TensorRSSpace r b I x)
    (m : TensorRSModel r a ℝ E) :
    modelCLM P m =
      TensorRSSpace.toModel (P ((tensorRSSpaceContinuousLinearEquiv (I := I) r a x).symm m)) :=
  rfl

/-- The average `∫₀¹ P(σ) dσ` of a family of fibre maps, computed in the model. -/
def avgFib (P : ℝ → (TensorRSSpace r a I x →L[ℝ] TensorRSSpace r b I x)) :
    TensorRSSpace r a I x →L[ℝ] TensorRSSpace r b I x :=
  (tensorRSSpaceContinuousLinearEquiv (I := I) r b x).symm.toContinuousLinearMap.comp
    ((∫ σ in (0 : ℝ)..1, modelCLM (P σ)).comp
      (tensorRSSpaceContinuousLinearEquiv (I := I) r a x).toContinuousLinearMap)

theorem avgFib_apply {P : ℝ → (TensorRSSpace r a I x →L[ℝ] TensorRSSpace r b I x)}
    (hP : ∀ w, ContinuousOn (fun σ => TensorRSSpace.toModel (P σ w)) (Icc 0 1))
    (w : TensorRSSpace r a I x) :
    TensorRSSpace.toModel (avgFib P w) = ∫ σ in (0 : ℝ)..1, TensorRSSpace.toModel (P σ w) := by
  have hc : ContinuousOn (fun σ => modelCLM (P σ)) (Icc 0 1) := by
    refine continuousOn_clm_apply.mpr fun m => ?_
    simpa only [modelCLM_apply] using hP ((tensorRSSpaceContinuousLinearEquiv (I := I) r a x).symm m)
  have hi : IntervalIntegrable (fun σ => modelCLM (P σ)) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rwa [uIcc_of_le zero_le_one]
  change (tensorRSSpaceContinuousLinearEquiv (I := I) r b x)
      ((tensorRSSpaceContinuousLinearEquiv (I := I) r b x).symm
        ((∫ σ in (0 : ℝ)..1, modelCLM (P σ)) (TensorRSSpace.toModel w))) = _
  rw [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.intervalIntegral_apply hi]
  refine intervalIntegral.integral_congr fun σ _ => ?_
  simp only [modelCLM_apply]
  congr 2

end Average

/-! ### The Legendre condition passes to averages -/

section LegendreAverage

variable (g : SmoothRiemannianMetric I M) {r s p : ℕ} {x : M}

/-- The fibre inner product with `a`, as a continuous linear functional on the model. -/
def innerModel (a : TensorRSSpace r s I x) : TensorRSModel r s ℝ E →L[ℝ] ℝ :=
  ((Tensor.TensorRSRiemannianBundle.tensorRSRiemannianMetric (I := I) (M := M) g r s).inner
    x a).comp (tensorRSSpaceContinuousLinearEquiv (I := I) r s x).symm.toContinuousLinearMap

theorem fiberInner_eq_innerModel (a T : TensorRSSpace r s I x) :
    fiberInner g r s x a T = innerModel g a (TensorRSSpace.toModel T) := by
  simp only [innerModel, fiberInner, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearEquiv.coe_coe]
  congr 1

/-- The Legendre form commutes with averaging the coefficient. -/
theorem legendreForm_avgFib {P : ℝ → (TensorRSSpace r (s + p + p) I x →L[ℝ] TensorRSSpace r s I x)}
    (hP : ∀ w, ContinuousOn (fun σ => TensorRSSpace.toModel (P σ w)) (Icc 0 1))
    (ξ : TensorRSSpace r (s + p) I x) :
    legendreForm g r s p x (avgFib P) ξ ξ = ∫ σ in (0 : ℝ)..1, legendreForm g r s p x (P σ) ξ ξ := by
  have hint : ∀ (c : TensorRSSpace r s I x) (w : TensorRSSpace r (s + p + p) I x),
      IntervalIntegrable (fun σ => innerModel g c (TensorRSSpace.toModel (P σ w))) volume 0 1 := by
    intro c w
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    exact (innerModel g c).continuous.comp_continuousOn (hP w)
  simp only [legendreForm_eq, fiberInner_eq_innerModel]
  rw [intervalIntegral.integral_finsetSum fun K _ => hint _ _]
  refine Finset.sum_congr rfl fun K _ => ?_
  have hf : ∀ w : TensorRSSpace r (s + p + p) I x,
      IntervalIntegrable (fun σ => TensorRSSpace.toModel (P σ w)) volume 0 1 := by
    intro w
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    exact hP w
  rw [avgFib_apply hP]
  exact (ContinuousLinearMap.intervalIntegral_comp_comm _ (hf _)).symm

/-- **The Legendre condition passes to averages.** -/
theorem legendreAt_avgFib {P : ℝ → (TensorRSSpace r (s + p + p) I x →L[ℝ] TensorRSSpace r s I x)}
    (hP : ∀ w, ContinuousOn (fun σ => TensorRSSpace.toModel (P σ w)) (Icc 0 1)) {lam : ℝ}
    (hL : ∀ σ ∈ Icc (0 : ℝ) 1, LegendreAt g r s p x (P σ) lam) :
    LegendreAt g r s p x (avgFib P) lam := by
  refine ⟨(hL 0 ⟨le_rfl, zero_le_one⟩).1, fun ξ => ?_⟩
  rw [legendreForm_avgFib g hP, ← intervalIntegral.integral_const_mul]
  have hc : ContinuousOn (fun σ => legendreForm g r s p x (P σ) ξ ξ) (Icc 0 1) := by
    simp only [legendreForm_eq, fiberInner_eq_innerModel]
    exact continuousOn_finsetSum _ fun K _ => (innerModel g _).continuous.comp_continuousOn (hP _)
  have hci : IntervalIntegrable (fun σ => (-1 : ℝ) ^ (p + 1) * legendreForm g r s p x (P σ) ξ ξ)
      volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    exact continuousOn_const.mul hc
  calc lam * fiberInner g r (s + p) x ξ ξ =
        ∫ _ in (0 : ℝ)..1, lam * fiberInner g r (s + p) x ξ ξ := by simp
    _ ≤ ∫ σ in (0 : ℝ)..1, (-1 : ℝ) ^ (p + 1) * legendreForm g r s p x (P σ) ξ ξ :=
        intervalIntegral.integral_mono_on zero_le_one (by simp) hci fun σ hσ => (hL σ hσ).2 ξ

end LegendreAverage

/-! ### The fundamental theorem of calculus along a segment -/

section Segment

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
  [NormedSpace ℝ W] [CompleteSpace W]

theorem continuousOn_fderiv_segment {G : V → W} {z₀ d : V}
    (hG : ∀ σ ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 1 G (z₀ + σ • d)) :
    ContinuousOn (fun σ : ℝ => fderiv ℝ G (z₀ + σ • d)) (Icc 0 1) := by
  intro σ hσ
  have h1 := ((hG σ hσ).fderiv_right (m := 0) (by norm_num)).continuousAt
  exact (h1.comp (continuous_const.add (continuous_id.smul continuous_const)).continuousAt
    (x := σ)).continuousWithinAt

/-- `G(z₀ + d) - G(z₀) = ∫₀¹ DG(z₀ + σd) d dσ` when `G` is `C¹` along the segment. -/
theorem sub_eq_integral_fderiv_segment {G : V → W} {z₀ d : V}
    (hG : ∀ σ ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 1 G (z₀ + σ • d)) :
    G (z₀ + d) - G z₀ = ∫ σ in (0 : ℝ)..1, fderiv ℝ G (z₀ + σ • d) d := by
  have hint : IntervalIntegrable (fun σ : ℝ => fderiv ℝ G (z₀ + σ • d) d) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    exact (continuousOn_fderiv_segment hG).clm_apply continuousOn_const
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun σ : ℝ => G (z₀ + σ • d))
    (fun σ hσ => ?_) hint]
  · simp
  · rw [uIcc_of_le zero_le_one] at hσ
    have hγ : HasDerivAt (fun σ : ℝ => z₀ + σ • d) d σ := by
      simpa using ((hasDerivAt_id σ).smul_const d).const_add z₀
    exact ((hG σ hσ).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt σ hγ

end Segment

namespace EquationData

variable {r s p : ℕ} (D : EquationData I M r s p)

theorem jetIso_segment {x : M} (ζ₀ ζ₁ : CovJetFiber I r s (2 * p) x) (σ : ℝ) :
    jetIso I r s (2 * p) x (ζ₀ + σ • (ζ₁ - ζ₀)) =
      jetIso I r s (2 * p) x ζ₀ + σ • jetIso I r s (2 * p) x (ζ₁ - ζ₀) := by
  rw [map_add, map_smul]

/-- Along a segment where `F` is `C¹`, the partial derivatives are continuous (in the model). -/
theorem continuousOn_partialDeriv_segment {t : ℝ} {x : M} {ζ₀ ζ₁ : CovJetFiber I r s (2 * p) x}
    (hF : ∀ σ ∈ Icc (0 : ℝ) 1,
      ContDiffAt ℝ 1 (D.Fmod t x) (jetIso I r s (2 * p) x (ζ₀ + σ • (ζ₁ - ζ₀))))
    (k : Fin (2 * p + 1)) (w : TensorRSSpace r (s + (k : ℕ)) I x) :
    ContinuousOn (fun σ : ℝ => TensorRSSpace.toModel (D.partialDeriv k t x (ζ₀ + σ • (ζ₁ - ζ₀)) w))
      (Icc 0 1) := by
  have hF' : ∀ σ ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 1 (D.Fmod t x)
      (jetIso I r s (2 * p) x ζ₀ + σ • jetIso I r s (2 * p) x (ζ₁ - ζ₀)) := fun σ hσ => by
    rw [← jetIso_segment]
    exact hF σ hσ
  have heq : (fun σ : ℝ => TensorRSSpace.toModel (D.partialDeriv k t x (ζ₀ + σ • (ζ₁ - ζ₀)) w)) =
      fun σ : ℝ => fderiv ℝ (D.Fmod t x)
        (jetIso I r s (2 * p) x ζ₀ + σ • jetIso I r s (2 * p) x (ζ₁ - ζ₀))
        (Pi.single k (fibIso I r (s + k) x w)) := by
    funext σ
    rw [← fibIso_apply, fibIso_partialDeriv, jetIso_segment]
  rw [heq]
  exact (continuousOn_fderiv_segment hF').clm_apply continuousOn_const

/-- `F(ζ₁) - F(ζ₀) = Σ_k (∫₀¹ D_kF(ζ₀ + σ(ζ₁ - ζ₀)) dσ)(ζ₁ - ζ₀)_k` along a segment where `F` is
`C¹`, the averages being computed in the model (`avgFib`). -/
theorem F_sub_eq_sum_avg {t : ℝ} {x : M} {ζ₀ ζ₁ : CovJetFiber I r s (2 * p) x}
    (hF : ∀ σ ∈ Icc (0 : ℝ) 1,
      ContDiffAt ℝ 1 (D.Fmod t x) (jetIso I r s (2 * p) x (ζ₀ + σ • (ζ₁ - ζ₀)))) :
    D.F t x ζ₁ - D.F t x ζ₀ =
      ∑ k, avgFib (fun σ => D.partialDeriv k t x (ζ₀ + σ • (ζ₁ - ζ₀))) ((ζ₁ - ζ₀) k) := by
  have hF' : ∀ σ ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 1 (D.Fmod t x)
      (jetIso I r s (2 * p) x ζ₀ + σ • jetIso I r s (2 * p) x (ζ₁ - ζ₀)) := fun σ hσ => by
    rw [← jetIso_segment]
    exact hF σ hσ
  have hcont := continuousOn_fderiv_segment hF'
  have hpk_eq : ∀ (k : Fin (2 * p + 1)) (w : TensorRSSpace r (s + (k : ℕ)) I x) (σ : ℝ),
      TensorRSSpace.toModel (D.partialDeriv k t x (ζ₀ + σ • (ζ₁ - ζ₀)) w) =
        fderiv ℝ (D.Fmod t x)
          (jetIso I r s (2 * p) x ζ₀ + σ • jetIso I r s (2 * p) x (ζ₁ - ζ₀))
          (Pi.single k (fibIso I r (s + k) x w)) := by
    intro k w σ
    rw [← fibIso_apply, fibIso_partialDeriv, jetIso_segment]
  have hpk : ∀ (k : Fin (2 * p + 1)) (w : TensorRSSpace r (s + (k : ℕ)) I x), ContinuousOn
      (fun σ : ℝ => TensorRSSpace.toModel (D.partialDeriv k t x (ζ₀ + σ • (ζ₁ - ζ₀)) w))
      (Icc 0 1) := by
    intro k w
    simp_rw [hpk_eq]
    exact hcont.clm_apply continuousOn_const
  have hint : ∀ v : JetModel E r s (2 * p), IntervalIntegrable (fun σ : ℝ =>
      fderiv ℝ (D.Fmod t x)
        (jetIso I r s (2 * p) x ζ₀ + σ • jetIso I r s (2 * p) x (ζ₁ - ζ₀)) v) volume 0 1 := by
    intro v
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    exact hcont.clm_apply continuousOn_const
  have hFTC := sub_eq_integral_fderiv_segment hF'
  have h1 : jetIso I r s (2 * p) x ζ₀ + jetIso I r s (2 * p) x (ζ₁ - ζ₀) =
      jetIso I r s (2 * p) x ζ₁ := by
    rw [← map_add, add_sub_cancel]
  rw [h1] at hFTC
  apply (fibIso I r s x).injective
  rw [map_sub, fibIso_F, fibIso_F, map_sum, hFTC]
  calc ∫ σ in (0 : ℝ)..1, fderiv ℝ (D.Fmod t x)
        (jetIso I r s (2 * p) x ζ₀ + σ • jetIso I r s (2 * p) x (ζ₁ - ζ₀))
        (jetIso I r s (2 * p) x (ζ₁ - ζ₀))
      = ∫ σ in (0 : ℝ)..1, ∑ k, fderiv ℝ (D.Fmod t x)
          (jetIso I r s (2 * p) x ζ₀ + σ • jetIso I r s (2 * p) x (ζ₁ - ζ₀))
          (Pi.single k (jetIso I r s (2 * p) x (ζ₁ - ζ₀) k)) := by
        refine intervalIntegral.integral_congr fun σ _ => ?_
        exact (congrArg (fderiv ℝ (D.Fmod t x) _)
          (Finset.univ_sum_single (jetIso I r s (2 * p) x (ζ₁ - ζ₀))).symm).trans (map_sum _ _ _)
    _ = ∑ k, ∫ σ in (0 : ℝ)..1, fderiv ℝ (D.Fmod t x)
          (jetIso I r s (2 * p) x ζ₀ + σ • jetIso I r s (2 * p) x (ζ₁ - ζ₀))
          (Pi.single k (jetIso I r s (2 * p) x (ζ₁ - ζ₀) k)) :=
        intervalIntegral.integral_finsetSum fun k _ => hint _
    _ = _ := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [fibIso_apply, avgFib_apply (hpk k)]
        refine intervalIntegral.integral_congr fun σ _ => ?_
        simp only [hpk_eq]
        rfl

end EquationData

/-! ### Jets along a segment -/

theorem covJet_segment (g : SmoothRiemannianMetric I M) {r s N : ℕ} (u v : SmoothCcTensor g r s)
    (σ : ℝ) (x : M) :
    covJet g r s N (v + σ • (u - v)) x =
      covJet g r s N v x + σ • (covJet g r s N u x - covJet g r s N v x) := by
  funext k
  simp only [covJet, iteratedCovGrad_add, iteratedCovGrad_smul, iteratedCovGrad_sub,
    SmoothCcTensor.toSection_add, SmoothCcTensor.toSection_smul, SmoothCcTensor.toSection_sub,
    ContMDiffSection.coe_add, ContMDiffSection.coe_smul, ContMDiffSection.coe_sub,
    Pi.add_apply, Pi.smul_apply, Pi.sub_apply]

/-! ### Averages commute with composition -/

theorem avgFib_comp_right {r a b c : ℕ} {x : M}
    {P : ℝ → (TensorRSSpace r a I x →L[ℝ] TensorRSSpace r b I x)}
    (hP : ∀ w, ContinuousOn (fun σ => TensorRSSpace.toModel (P σ w)) (Icc 0 1))
    (C : TensorRSSpace r c I x →L[ℝ] TensorRSSpace r a I x) :
    (avgFib P).comp C = avgFib (fun σ => (P σ).comp C) := by
  refine ContinuousLinearMap.ext fun w => (fibIso I r b x).injective ?_
  have hPC : ∀ w, ContinuousOn (fun σ => TensorRSSpace.toModel ((P σ).comp C w)) (Icc 0 1) :=
    fun w => hP (C w)
  rw [ContinuousLinearMap.comp_apply, fibIso_apply, fibIso_apply, avgFib_apply hP,
    avgFib_apply hPC]
  simp only [ContinuousLinearMap.comp_apply]

theorem toSection_finset_sum_apply {g : SmoothRiemannianMetric I M} {a b : ℕ} {ι : Type*}
    (S : Finset ι) (F : ι → SmoothCcTensor g a b) (x : M) :
    (∑ i ∈ S, F i).toSection x = ∑ i ∈ S, (F i).toSection x := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, SmoothCcTensor.toSection_add,
      ContMDiffSection.coe_add, Pi.add_apply, ih]

theorem operatorFieldApply_toSection_eq {g : SmoothRiemannianMetric I M} [CompleteSpace E]
    {a b : ℕ} (Φ : SmoothCcTensor g a b) (W : SmoothCcTensor g 0 a) (x : M) :
    (operatorFieldApply (I := I) (M := M) g a b Φ W).toSection x =
      opFieldHom (Φ.toSection x) (W.toSection x) := rfl

end ShortTime
