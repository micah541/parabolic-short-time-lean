import ShortTime.Analysis.TimeDerivManifold
import ShortTime.Linear.Garding
import DifferentialGeometry.Bundle.ContinuousLinearMapSection.ParametricSmoothness

/-!
# Time derivatives of jointly smooth families

For a family `u : ℝ → C^∞(M; T^a_b)`, jointly smooth on `M × [0,T]` with `T > 0`, the time
derivative `∂ₜu` (taken fibrewise, in the model fibre, within `[0,T]`) is again a jointly smooth
family (`jointlySmoothOn_timeDeriv`), and it is the derivative of `u` within `[0,T]` at every point
(`hasDerivWithinAt_timeDeriv`). Iterating gives `∂ₜ^j u` (`timeDerivIter`).

In the trivialization at `x₀` the coordinates of `∂ₜu` are the time derivatives of the coordinates
of `u`, which are smooth by `contMDiffOn_derivWithin_snd`.
-/

noncomputable section

open Bundle Manifold Set Filter
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev MeasureTheory
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

variable {g : SmoothRiemannianMetric I M} {a b : ℕ} {T : ℝ}

/-- The fibrewise time derivative of `u` at `(x, t)`, within `[0,T]`. -/
def timeDerivSec (T : ℝ) (u : ℝ → SmoothCcTensor g a b) (x : M) (t : ℝ) : TensorRSSpace a b I x :=
  TensorRSSpace.ofModel (derivWithin (fun τ => TensorRSSpace.toModel ((u τ).toSection x)) (Icc 0 T) t)

theorem toModel_timeDerivSec (u : ℝ → SmoothCcTensor g a b) (x : M) (t : ℝ) :
    TensorRSSpace.toModel (timeDerivSec T u x t) =
      derivWithin (fun τ => TensorRSSpace.toModel ((u τ).toSection x)) (Icc 0 T) t :=
  (tensorRSSpaceContinuousLinearEquiv (I := I) a b x).apply_symm_apply _

/-- The model value is a fixed linear image of the coordinates in a trivialization. -/
theorem toModel_eq_trivAt {x₀ y : M} (hy : y ∈ (trivAt I M a b x₀).baseSet) (w : TensorRSSpace a b I y) :
    TensorRSSpace.toModel w =
      ((tensorRSSpaceContinuousLinearEquiv (I := I) a b y).toContinuousLinearMap.comp
        ((trivAt I M a b x₀).symmL ℝ y)) ((trivAt I M a b x₀ ⟨y, w⟩).2) := by
  have h2 : (trivAt I M a b x₀ ⟨y, w⟩).2 = (trivAt I M a b x₀).continuousLinearMapAt ℝ y w := by
    rw [Trivialization.continuousLinearMapAt_apply, Trivialization.coe_linearMapAt_of_mem _ hy]
  rw [ContinuousLinearMap.comp_apply, h2, Trivialization.symmL_continuousLinearMapAt _ hy]
  rfl

/-- In the trivialization at `x₀`, the time derivative of `u` has the time derivatives of the
coordinates of `u` as coordinates. -/
theorem trivAt_timeDerivSec (hT : 0 < T) {u : ℝ → SmoothCcTensor g a b}
    (hu : JointlySmoothOn g a b (Icc 0 T) u) {x₀ y : M} (hy : y ∈ (trivAt I M a b x₀).baseSet)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    (trivAt I M a b x₀ ⟨y, timeDerivSec T u y t⟩).2 =
      derivWithin (fun τ => (trivAt I M a b x₀ ⟨y, (u τ).toSection y⟩).2) (Icc 0 T) t ∧
    HasDerivWithinAt (fun τ => TensorRSSpace.toModel ((u τ).toSection y))
      (TensorRSSpace.toModel (timeDerivSec T u y t)) (Icc 0 T) t := by
  set e := trivAt I M a b x₀
  set A := (tensorRSSpaceContinuousLinearEquiv (I := I) a b y).toContinuousLinearMap.comp
    (e.symmL ℝ y)
  -- the coordinates of `u` are smooth on `baseSet × [0,T]`
  have hc : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, TensorRSModel a b ℝ E) ∞
      (fun q : M × ℝ => (e ⟨q.1, (u q.2).toSection q.1⟩).2) (e.baseSet ×ˢ Icc 0 T) :=
    ((e.contMDiffOn_iff fun q hq => e.mem_source.mpr hq.1).mp
      (hu.mono (prod_mono (subset_univ _) le_rfl))).2
  have hd := hasDerivWithinAt_snd (uniqueDiffOn_Icc hT)
    (f := fun y τ => (e ⟨y, (u τ).toSection y⟩).2) hc hy ht
  have hfun : (fun τ => TensorRSSpace.toModel ((u τ).toSection y)) =
      fun τ => A ((e ⟨y, (u τ).toSection y⟩).2) :=
    funext fun τ => toModel_eq_trivAt hy _
  have hA : HasDerivWithinAt (fun τ => TensorRSSpace.toModel ((u τ).toSection y))
      (A (derivWithin (fun τ => (e ⟨y, (u τ).toSection y⟩).2) (Icc 0 T) t)) (Icc 0 T) t := by
    rw [hfun]
    exact A.hasFDerivAt.comp_hasDerivWithinAt t hd
  have hderiv : derivWithin (fun τ => TensorRSSpace.toModel ((u τ).toSection y)) (Icc 0 T) t =
      A (derivWithin (fun τ => (e ⟨y, (u τ).toSection y⟩).2) (Icc 0 T) t) :=
    hA.derivWithin (uniqueDiffOn_Icc hT t ht)
  refine ⟨?_, ?_⟩
  · have h2 : (e ⟨y, timeDerivSec T u y t⟩).2 = e.continuousLinearMapAt ℝ y (timeDerivSec T u y t) := by
      rw [Trivialization.continuousLinearMapAt_apply, Trivialization.coe_linearMapAt_of_mem _ hy]
    rw [h2]
    change e.continuousLinearMapAt ℝ y
      ((tensorRSSpaceContinuousLinearEquiv (I := I) a b y).symm
        (derivWithin (fun τ => TensorRSSpace.toModel ((u τ).toSection y)) (Icc 0 T) t)) = _
    rw [hderiv]
    simp only [A, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply]
    exact Trivialization.continuousLinearMapAt_symmL _ hy _
  · rw [toModel_timeDerivSec, hderiv]
    exact hA

/-- **The time derivative of a jointly smooth family is jointly smooth.** -/
theorem contMDiffOn_timeDerivSec (hT : 0 < T) {u : ℝ → SmoothCcTensor g a b}
    (hu : JointlySmoothOn g a b (Icc 0 T) u) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel a b ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel a b ℝ E)
        (E := fun x : M => TensorRSSpace a b I x) q.1 (timeDerivSec T u q.1 q.2))
      ((Set.univ : Set M) ×ˢ Icc 0 T) := by
  intro q₀ hq₀
  set e := trivAt I M a b q₀.1
  have hloc : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel a b ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel a b ℝ E)
        (E := fun x : M => TensorRSSpace a b I x) q.1 (timeDerivSec T u q.1 q.2))
      (e.baseSet ×ˢ Icc 0 T) := by
    rw [e.contMDiffOn_iff fun q hq => e.mem_source.mpr hq.1]
    refine ⟨contMDiffOn_fst, ?_⟩
    have hc : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, TensorRSModel a b ℝ E) ∞
        (fun q : M × ℝ => (e ⟨q.1, (u q.2).toSection q.1⟩).2) (e.baseSet ×ˢ Icc 0 T) :=
      ((e.contMDiffOn_iff fun q hq => e.mem_source.mpr hq.1).mp
        (hu.mono (prod_mono (subset_univ _) le_rfl))).2
    have hd := contMDiffOn_derivWithin_snd e.open_baseSet (uniqueDiffOn_Icc hT)
      (f := fun y τ => (e ⟨y, (u τ).toSection y⟩).2) hc
    exact hd.congr fun q hq => (trivAt_timeDerivSec hT hu hq.1 hq.2).1
  have hnhds : e.baseSet ×ˢ Icc 0 T ∈ 𝓝[(Set.univ : Set M) ×ˢ Icc 0 T] q₀ := by
    have : ((Set.univ : Set M) ×ˢ Icc 0 T) ∩ (e.baseSet ×ˢ (Set.univ : Set ℝ)) ⊆
        e.baseSet ×ˢ Icc 0 T := fun q hq => ⟨hq.2.1, hq.1.2⟩
    exact mem_of_superset (inter_mem_nhdsWithin _ (prod_mem_nhds
      (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt _ _ _)) univ_mem)) this
  exact (hloc q₀ ⟨mem_baseSet_trivializationAt _ _ _, hq₀.2⟩).mono_of_mem_nhdsWithin hnhds

open Classical in
/-- **The time derivative `∂ₜu` of a jointly smooth family**, as a family of tensor fields. Outside
`[0,T]`, or if `u` is not jointly smooth on `[0,T]`, it is `0`. -/
def timeDeriv (T : ℝ) (u : ℝ → SmoothCcTensor g a b) : ℝ → SmoothCcTensor g a b := fun t =>
  if h : 0 < T ∧ t ∈ Icc 0 T ∧ JointlySmoothOn g a b (Icc 0 T) u then
    { toSection := ⟨fun y => timeDerivSec T u y t, by
        have hsl : ContMDiff I (I.prod 𝓘(ℝ, ℝ)) ∞ (fun y : M => (y, t)) :=
          contMDiff_id.prodMk contMDiff_const
        intro y
        exact ((contMDiffOn_timeDerivSec h.1 h.2.2).comp_contMDiff hsl
          (fun _ => ⟨mem_univ _, h.2.1⟩)) y⟩
      hasCompactSupport := HasCompactSupport.of_compactSpace _ }
  else 0

theorem timeDeriv_toSection (hT : 0 < T) {u : ℝ → SmoothCcTensor g a b}
    (hu : JointlySmoothOn g a b (Icc 0 T) u) {t : ℝ} (ht : t ∈ Icc 0 T) (x : M) :
    (timeDeriv T u t).toSection x = timeDerivSec T u x t := by
  rw [timeDeriv, dif_pos ⟨hT, ht, hu⟩]
  rfl

theorem jointlySmoothOn_timeDeriv (hT : 0 < T) {u : ℝ → SmoothCcTensor g a b}
    (hu : JointlySmoothOn g a b (Icc 0 T) u) :
    JointlySmoothOn g a b (Icc 0 T) (timeDeriv T u) :=
  (contMDiffOn_timeDerivSec hT hu).congr fun q hq => by
    rw [timeDeriv_toSection hT hu hq.2]

/-- `∂ₜu` is the derivative of `u` within `[0,T]`. -/
theorem hasDerivWithinAt_timeDeriv (hT : 0 < T) {u : ℝ → SmoothCcTensor g a b}
    (hu : JointlySmoothOn g a b (Icc 0 T) u) {t : ℝ} (ht : t ∈ Icc 0 T) (x : M) :
    HasDerivWithinAt (fun τ => TensorRSSpace.toModel ((u τ).toSection x))
      (TensorRSSpace.toModel ((timeDeriv T u t).toSection x)) (Icc 0 T) t := by
  rw [timeDeriv_toSection hT hu ht]
  exact (trivAt_timeDerivSec hT hu (mem_baseSet_trivializationAt _ _ x) ht).2

/-- The iterated time derivative `∂ₜ^j u`. -/
def timeDerivIter (T : ℝ) (u : ℝ → SmoothCcTensor g a b) : ℕ → ℝ → SmoothCcTensor g a b
  | 0 => u
  | j + 1 => timeDeriv T (timeDerivIter T u j)

theorem jointlySmoothOn_timeDerivIter (hT : 0 < T) {u : ℝ → SmoothCcTensor g a b}
    (hu : JointlySmoothOn g a b (Icc 0 T) u) :
    ∀ j, JointlySmoothOn g a b (Icc 0 T) (timeDerivIter T u j)
  | 0 => hu
  | j + 1 => jointlySmoothOn_timeDeriv hT (jointlySmoothOn_timeDerivIter hT hu j)

/-! ### Linearity -/

omit [CompactSpace M] in
theorem jointlySmoothOn_smul {S : Set ℝ} {A : ℝ → SmoothCcTensor g a b} (c : ℝ)
    (hA : JointlySmoothOn g a b S A) : JointlySmoothOn g a b S (fun t => c • A t) := by
  have hφ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel a b ℝ E →L[ℝ] TensorRSModel a b ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel a b ℝ E →L[ℝ] TensorRSModel a b ℝ E)
        (E := fun x : M => TensorRSSpace a b I x →L[ℝ] TensorRSSpace a b I x) p.1
        (c • ContinuousLinearMap.id ℝ (TensorRSSpace a b I p.1))) ((Set.univ : Set M) ×ˢ S) := by
    apply contMDiffOn_clm_section_of_apply (I := I) (M := M)
      (F₁ := TensorRSModel a b ℝ E) (V₁ := fun x : M => TensorRSSpace a b I x)
      (F₂ := TensorRSModel a b ℝ E) (V₂ := fun x : M => TensorRSSpace a b I x)
      (φ := fun p : M × ℝ => c • ContinuousLinearMap.id ℝ (TensorRSSpace a b I p.1)) (S := S)
    intro Y
    have h := (Y.contMDiff.const_smul_section (a := c)).comp_contMDiffOn
      (contMDiffOn_fst : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞ (Prod.fst : M × ℝ → M)
        ((Set.univ : Set M) ×ˢ S))
    exact h.congr fun p _ => rfl
  exact (ContMDiffOn.clm_bundle_apply (b := Prod.fst) hφ hA).congr fun p _ => rfl

theorem smoothCcTensor_eq_of_toFun {A B : SmoothCcTensor g a b} (h : ∀ x, A.toFun x = B.toFun x) :
    A = B := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  exact (tensorRSSpaceContinuousLinearEquiv (I := I) a b x).injective (h x)

theorem timeDeriv_of_not_mem {u : ℝ → SmoothCcTensor g a b} {t : ℝ} (ht : t ∉ Icc 0 T) :
    timeDeriv T u t = 0 := by
  rw [timeDeriv, dif_neg fun h => ht h.2.1]

theorem timeDeriv_add (hT : 0 < T) {A B : ℝ → SmoothCcTensor g a b}
    (hA : JointlySmoothOn g a b (Icc 0 T) A) (hB : JointlySmoothOn g a b (Icc 0 T) B) :
    timeDeriv T (fun τ => A τ + B τ) = fun t => timeDeriv T A t + timeDeriv T B t := by
  funext t
  by_cases ht : t ∈ Icc 0 T
  · refine smoothCcTensor_eq_of_toFun fun x => ?_
    have h1 := hasDerivWithinAt_timeDeriv hT (jointlySmoothOn_add hA hB) ht x
    have h2 := (hasDerivWithinAt_timeDeriv hT hA ht x).add (hasDerivWithinAt_timeDeriv hT hB ht x)
    have hf : (fun τ => TensorRSSpace.toModel ((A τ + B τ).toSection x)) =
        fun τ => TensorRSSpace.toModel ((A τ).toSection x) +
          TensorRSSpace.toModel ((B τ).toSection x) := by
      funext τ
      rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
        TensorRSSpace.toModel_add]
    rw [hf] at h1
    rw [SmoothCcTensor.toFun_add, Pi.add_apply]
    exact (uniqueDiffOn_Icc hT t ht).eq_deriv _ h1 h2
  · rw [timeDeriv_of_not_mem ht, timeDeriv_of_not_mem ht, timeDeriv_of_not_mem ht, add_zero]

theorem timeDeriv_smul (hT : 0 < T) {A : ℝ → SmoothCcTensor g a b} (c : ℝ)
    (hA : JointlySmoothOn g a b (Icc 0 T) A) :
    timeDeriv T (fun τ => c • A τ) = fun t => c • timeDeriv T A t := by
  funext t
  by_cases ht : t ∈ Icc 0 T
  · refine smoothCcTensor_eq_of_toFun fun x => ?_
    have h1 := hasDerivWithinAt_timeDeriv hT (jointlySmoothOn_smul c hA) ht x
    have h2 := (hasDerivWithinAt_timeDeriv hT hA ht x).const_smul c
    have hf : (fun τ => TensorRSSpace.toModel ((c • A τ).toSection x)) =
        fun τ => c • TensorRSSpace.toModel ((A τ).toSection x) := by
      funext τ
      rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
        TensorRSSpace.toModel_smul]
    rw [hf] at h1
    rw [SmoothCcTensor.toFun_smul, Pi.smul_apply]
    exact (uniqueDiffOn_Icc hT t ht).eq_deriv _ h1 h2
  · rw [timeDeriv_of_not_mem ht, timeDeriv_of_not_mem ht, smul_zero]

theorem timeDerivIter_add (hT : 0 < T) {A B : ℝ → SmoothCcTensor g a b}
    (hA : JointlySmoothOn g a b (Icc 0 T) A) (hB : JointlySmoothOn g a b (Icc 0 T) B) :
    ∀ j, timeDerivIter T (fun τ => A τ + B τ) j =
      fun t => timeDerivIter T A j t + timeDerivIter T B j t
  | 0 => rfl
  | j + 1 => by
    change timeDeriv T (timeDerivIter T (fun τ => A τ + B τ) j) = _
    rw [timeDerivIter_add hT hA hB j]
    exact timeDeriv_add hT (jointlySmoothOn_timeDerivIter hT hA j)
      (jointlySmoothOn_timeDerivIter hT hB j)

theorem timeDerivIter_smul (hT : 0 < T) {A : ℝ → SmoothCcTensor g a b} (c : ℝ)
    (hA : JointlySmoothOn g a b (Icc 0 T) A) :
    ∀ j, timeDerivIter T (fun τ => c • A τ) j = fun t => c • timeDerivIter T A j t
  | 0 => rfl
  | j + 1 => by
    change timeDeriv T (timeDerivIter T (fun τ => c • A τ) j) = _
    rw [timeDerivIter_smul hT c hA j]
    exact timeDeriv_smul hT c (jointlySmoothOn_timeDerivIter hT hA j)

/-- The iterated derivative within `[0,T]` of the model values is the iterated time derivative
family. -/
theorem iteratedDerivWithin_eq_timeDerivIter (hT : 0 < T) {A : ℝ → SmoothCcTensor g a b}
    (hA : JointlySmoothOn g a b (Icc 0 T) A) (x : M) :
    ∀ j, ∀ t ∈ Icc 0 T,
      iteratedDerivWithin j (fun τ => (A τ).toFun x) (Icc 0 T) t = (timeDerivIter T A j t).toFun x
  | 0, t, _ => rfl
  | j + 1, t, ht => by
    rw [iteratedDerivWithin_succ, derivWithin_congr (fun τ hτ =>
      iteratedDerivWithin_eq_timeDerivIter hT hA x j τ hτ)
      (iteratedDerivWithin_eq_timeDerivIter hT hA x j t ht)]
    exact (hasDerivWithinAt_timeDeriv hT (jointlySmoothOn_timeDerivIter hT hA j) ht x).derivWithin
      (uniqueDiffOn_Icc hT t ht)

/-! ### Continuity in time of `L²` pairings -/

/-- `t ↦ ⟨A(t), B(t)⟩_{L²}` is continuous on `[0,T]` for jointly smooth families. -/
theorem continuousOn_l2Pairing (hT : 0 < T) {A B : ℝ → SmoothCcTensor g a b}
    (hA : JointlySmoothOn g a b (Icc 0 T) A) (hB : JointlySmoothOn g a b (Icc 0 T) B) :
    ContinuousOn (fun τ => ∫ x, tensorInnerPointwise (I := I) (M := M) g a b x
      ((A τ).toFun x) ((B τ).toFun x) ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      (Icc 0 T) := by
  have := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  obtain ⟨Ba, -, hBa⟩ := exists_bound_of_jointlySmoothOn hA
  obtain ⟨Bb, -, hBb⟩ := exists_bound_of_jointlySmoothOn hB
  refine continuousOn_of_dominated (bound := fun _ => Real.sqrt Ba * Real.sqrt Bb)
    (fun τ _ => (SmoothCcTensor.integrable_inner_cross (A τ) (B τ)).aestronglyMeasurable)
    (fun τ hτ => ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]
      exact abs_tensorInnerPointwise_cc_le g (A τ) (B τ) x (hBa τ hτ x) (hBb τ hτ x))
    (integrable_const _) (ae_of_all _ fun x => ?_)
  have hU : ContinuousOn (fun τ => (A τ).toFun x) (Icc 0 T) :=
    fun τ hτ => (hasDerivWithinAt_timeDeriv hT hA hτ x).continuousWithinAt
  have hV : ContinuousOn (fun τ => (B τ).toFun x) (Icc 0 T) :=
    fun τ hτ => (hasDerivWithinAt_timeDeriv hT hB hτ x).continuousWithinAt
  have hc : ContinuousOn (fun τ => ptInnerBilin g a b x ((A τ).toFun x) ((B τ).toFun x))
      (Icc 0 T) :=
    ((ptInnerBilin g a b x).continuous.comp_continuousOn hU).clm_apply hV
  simp only [ptInnerBilin_apply] at hc
  exact hc

end ShortTime
