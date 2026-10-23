import ShortTime.Linear.TimeDeriv
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Iterated.Linear

/-!
# Parabolic Sobolev spaces and the linear theorem (statements)

Paper: Definition `def:parabolic`, Theorem `thm:linear`.

For a jointly smooth family `u : [0,T] → C^∞(M; T⁰_s)`,
`‖u‖²_{𝒫^m} = Σ_{2pj+i ≤ 2pm} ∫₀ᵀ ‖∂ₜ^j ∇^i u‖²_{L²} dt`.

* `mixedDeriv` is `∂ₜ^j ∇^i u(x, t)`, taken pointwise in the model fibre (one-sided at `t = 0, T`).
* `ParabolicPre g s p m T` is the space of jointly smooth families with this (semi)inner product;
  `ParabolicSpace` is its completion `𝒫^m`, and `ParabolicSpace.zeroAtStart` is `𝒫^m_0`, the
  closure of the families vanishing at `t = 0`.
* `LinearOp.isomorphism` (`thm:linear` (i), in `ShortTime.Linear.ModelSolve`):
  `∂ₜ - L : 𝒫^m_0 → 𝒫^{m-1}` is a linear homeomorphism agreeing with `∂ₜ - L` on smooth families,
  i.e. sending `u` to `w` whenever `∂ₜu = Lu + w` (`LinearOp.Solves`).
* `LinearOp.exists_smooth` (`thm:linear` (ii), in `ShortTime.Linear.SmoothSolve`): smooth data give
  a smooth solution. Uniqueness is `LinearOp.unique_of_isParabolic`.

The inner-product axioms are proved: on `[0,T]`, `mixedDeriv` is the iterated time derivative
family `timeDerivIter` of `∇^i u` (`mixedDeriv_eq`), so the pairings are integrals of continuous
functions of time.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev
open scoped Manifold ContDiff

set_option linter.unusedSectionVars false

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

variable (g : SmoothRiemannianMetric I M)

/-! ### Smooth families -/

/-- The jointly smooth families on `[0,T]`: the dense subspace of `𝒫^m`. -/
def smoothFamilies (s : ℕ) (T : ℝ) : Submodule ℝ (ℝ → SmoothCcTensor g 0 s) where
  carrier := {u | JointlySmoothOn g 0 s (Icc 0 T) u}
  add_mem' hu hv := jointlySmoothOn_add hu hv
  zero_mem' := jointlySmoothOn_const g _ 0
  smul_mem' c _ hu := jointlySmoothOn_smul c hu

/-! ### The norm of `𝒫^m` -/

/-- `∂ₜ^j ∇^i u (x, t)`, in the model fibre of `T⁰_{s+i}` at `x`; the time derivatives are taken
within `[0,T]`. -/
def mixedDeriv (s : ℕ) (T : ℝ) (u : ℝ → SmoothCcTensor g 0 s) (j i : ℕ) (x : M) (t : ℝ) :
    TensorRSModel 0 (s + i) ℝ E :=
  iteratedDerivWithin j
    (fun τ => TensorRSSpace.toModel ((iteratedCovGrad g 0 s i (u τ)).toSection x)) (Icc 0 T) t

/-- `∫₀ᵀ ⟨∂ₜ^j ∇^i u, ∂ₜ^j ∇^i v⟩_{L²} dt`. -/
def mixedInner (s : ℕ) (T : ℝ) (u v : ℝ → SmoothCcTensor g 0 s) (j i : ℕ) : ℝ :=
  ∫ t in Icc 0 T, ∫ x, tensorInnerPointwise (I := I) (M := M) g 0 (s + i) x
      (mixedDeriv g s T u j i x t) (mixedDeriv g s T v j i x t)
    ∂(riemannianVolumeMeasure (I := I) (M := M) g)

/-- The inner product of `𝒫^m`: the sum of `mixedInner` over `2pj + i ≤ 2pm` (`def:parabolic`). -/
def parabolicInner (s p m : ℕ) (T : ℝ) (u v : ℝ → SmoothCcTensor g 0 s) : ℝ :=
  ∑ j ∈ Finset.range (m + 1), ∑ i ∈ Finset.range (2 * p * (m - j) + 1), mixedInner g s T u v j i

/-! ### Properties of the mixed pairings -/

section MixedProps

variable {g} {s : ℕ} {T : ℝ}

theorem jointlySmoothOn_iteratedCovGrad {u : ℝ → SmoothCcTensor g 0 s}
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u) (i : ℕ) :
    JointlySmoothOn g 0 (s + i) (Icc 0 T) (fun τ => iteratedCovGrad g 0 s i (u τ)) :=
  Vendor.covGrad_iter_joint (I := I) (M := M) g 0 s i u (Icc 0 T) hu

/-- On `[0,T]`, `∂ₜ^j ∇^i u` is the iterated time derivative of the family `∇^i u`. -/
theorem mixedDeriv_eq (hT : 0 < T) {u : ℝ → SmoothCcTensor g 0 s}
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u) (j i : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) (x : M) :
    mixedDeriv g s T u j i x t =
      (timeDerivIter T (fun τ => iteratedCovGrad g 0 s i (u τ)) j t).toFun x :=
  iteratedDerivWithin_eq_timeDerivIter hT (jointlySmoothOn_iteratedCovGrad hu i) x j t ht

theorem mixedInner_eq (hT : 0 < T) {u v : ℝ → SmoothCcTensor g 0 s}
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u) (hv : JointlySmoothOn g 0 s (Icc 0 T) v) (j i : ℕ) :
    mixedInner g s T u v j i =
      ∫ t in Icc 0 T, ∫ x, tensorInnerPointwise (I := I) (M := M) g 0 (s + i) x
          ((timeDerivIter T (fun τ => iteratedCovGrad g 0 s i (u τ)) j t).toFun x)
          ((timeDerivIter T (fun τ => iteratedCovGrad g 0 s i (v τ)) j t).toFun x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  unfold mixedInner
  refine setIntegral_congr_fun measurableSet_Icc fun t ht => ?_
  simp only [mixedDeriv_eq hT hu j i ht, mixedDeriv_eq hT hv j i ht]

theorem mixedInner_of_nonpos (hT : T ≤ 0) (u v : ℝ → SmoothCcTensor g 0 s) (j i : ℕ) :
    mixedInner g s T u v j i = 0 := by
  unfold mixedInner
  refine setIntegral_measure_zero _ ?_
  rw [Real.volume_Icc]
  exact ENNReal.ofReal_eq_zero.mpr (by linarith)

theorem mixedInner_comm (u v : ℝ → SmoothCcTensor g 0 s) (j i : ℕ) :
    mixedInner g s T u v j i = mixedInner g s T v u j i := by
  unfold mixedInner
  congr 1
  funext t
  congr 1
  funext x
  exact tensorInnerPointwise_symm g 0 (s + i) x _ _

theorem mixedInner_self_nonneg (u : ℝ → SmoothCcTensor g 0 s) (j i : ℕ) :
    0 ≤ mixedInner g s T u u j i :=
  setIntegral_nonneg measurableSet_Icc fun _ _ =>
    integral_nonneg fun x => tensorInnerPointwise_nonneg g 0 (s + i) x _

theorem mixedInner_add_left {u v w : ℝ → SmoothCcTensor g 0 s}
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u) (hv : JointlySmoothOn g 0 s (Icc 0 T) v)
    (hw : JointlySmoothOn g 0 s (Icc 0 T) w) (j i : ℕ) :
    mixedInner g s T (fun τ => u τ + v τ) w j i = mixedInner g s T u w j i + mixedInner g s T v w j i := by
  rcases le_or_gt T 0 with hT | hT
  · rw [mixedInner_of_nonpos hT, mixedInner_of_nonpos hT, mixedInner_of_nonpos hT, add_zero]
  have hU := jointlySmoothOn_timeDerivIter hT (jointlySmoothOn_iteratedCovGrad hu i) j
  have hV := jointlySmoothOn_timeDerivIter hT (jointlySmoothOn_iteratedCovGrad hv i) j
  have hW := jointlySmoothOn_timeDerivIter hT (jointlySmoothOn_iteratedCovGrad hw i) j
  rw [mixedInner_eq hT (jointlySmoothOn_add hu hv) hw, mixedInner_eq hT hu hw, mixedInner_eq hT hv hw]
  have hsum : timeDerivIter T (fun τ => iteratedCovGrad g 0 s i (u τ + v τ)) j =
      fun t => timeDerivIter T (fun τ => iteratedCovGrad g 0 s i (u τ)) j t +
        timeDerivIter T (fun τ => iteratedCovGrad g 0 s i (v τ)) j t := by
    have h : (fun τ => iteratedCovGrad g 0 s i (u τ + v τ)) =
        fun τ => iteratedCovGrad g 0 s i (u τ) + iteratedCovGrad g 0 s i (v τ) :=
      funext fun τ => Analysis.Spectral.iteratedCovGrad_add (I := I) (M := M) g 0 s i (u τ) (v τ)
    rw [h]
    exact timeDerivIter_add hT (jointlySmoothOn_iteratedCovGrad hu i)
      (jointlySmoothOn_iteratedCovGrad hv i) j
  rw [hsum]
  simp only [SmoothCcTensor.toFun_add, Pi.add_apply, tensorInnerPointwise_add_left]
  have hx : ∀ t, ∫ x, (tensorInnerPointwise (I := I) (M := M) g 0 (s + i) x
        ((timeDerivIter T (fun τ => iteratedCovGrad g 0 s i (u τ)) j t).toFun x)
        ((timeDerivIter T (fun τ => iteratedCovGrad g 0 s i (w τ)) j t).toFun x) +
      tensorInnerPointwise (I := I) (M := M) g 0 (s + i) x
        ((timeDerivIter T (fun τ => iteratedCovGrad g 0 s i (v τ)) j t).toFun x)
        ((timeDerivIter T (fun τ => iteratedCovGrad g 0 s i (w τ)) j t).toFun x))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      (∫ x, tensorInnerPointwise (I := I) (M := M) g 0 (s + i) x
        ((timeDerivIter T (fun τ => iteratedCovGrad g 0 s i (u τ)) j t).toFun x)
        ((timeDerivIter T (fun τ => iteratedCovGrad g 0 s i (w τ)) j t).toFun x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) +
      ∫ x, tensorInnerPointwise (I := I) (M := M) g 0 (s + i) x
        ((timeDerivIter T (fun τ => iteratedCovGrad g 0 s i (v τ)) j t).toFun x)
        ((timeDerivIter T (fun τ => iteratedCovGrad g 0 s i (w τ)) j t).toFun x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := fun t =>
    integral_add (SmoothCcTensor.integrable_inner_cross _ _)
      (SmoothCcTensor.integrable_inner_cross _ _)
  simp only [hx]
  exact integral_add (continuousOn_l2Pairing hT hU hW).integrableOn_Icc
    (continuousOn_l2Pairing hT hV hW).integrableOn_Icc

theorem mixedInner_smul_left {u w : ℝ → SmoothCcTensor g 0 s}
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u) (c : ℝ) (j i : ℕ) :
    mixedInner g s T (fun τ => c • u τ) w j i = c * mixedInner g s T u w j i := by
  rcases le_or_gt T 0 with hT | hT
  · rw [mixedInner_of_nonpos hT, mixedInner_of_nonpos hT, mul_zero]
  unfold mixedInner
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Icc fun t ht => ?_
  rw [← integral_const_mul]
  congr 1
  funext x
  have hsmul : (fun τ => iteratedCovGrad g 0 s i (c • u τ)) =
      fun τ => c • iteratedCovGrad g 0 s i (u τ) :=
    funext fun τ => Analysis.Spectral.iteratedCovGrad_smul (I := I) (M := M) g 0 s i c (u τ)
  rw [mixedDeriv_eq hT (jointlySmoothOn_smul c hu) j i ht, mixedDeriv_eq hT hu j i ht, hsmul,
    timeDerivIter_smul hT c (jointlySmoothOn_iteratedCovGrad hu i) j, SmoothCcTensor.toFun_smul,
    Pi.smul_apply, tensorInnerPointwise_smul_left]

end MixedProps

/-! ### The spaces `𝒫^m` and `𝒫^m_0` -/

/-- Smooth families with the inner product of `𝒫^m` (a type synonym, so that it carries no other
topology). -/
def ParabolicPre (s _p _m : ℕ) (T : ℝ) : Type _ := smoothFamilies g s T

namespace ParabolicPre

variable {g} {s p m : ℕ} {T : ℝ}

instance : AddCommGroup (ParabolicPre g s p m T) :=
  inferInstanceAs (AddCommGroup (smoothFamilies g s T))

instance : Module ℝ (ParabolicPre g s p m T) := inferInstanceAs (Module ℝ (smoothFamilies g s T))

/-- The underlying family. -/
def family (u : ParabolicPre g s p m T) : ℝ → SmoothCcTensor g 0 s :=
  (u : smoothFamilies g s T).1

variable (g s p m T) in
/-- The `𝒫^m` inner product as a pre-inner-product structure. -/
@[instance_reducible]
def core : PreInnerProductSpace.Core ℝ (ParabolicPre g s p m T) where
  inner u v := parabolicInner g s p m T u.family v.family
  conj_inner_symm u v := by
    change (starRingEnd ℝ) (parabolicInner g s p m T v.family u.family) =
      parabolicInner g s p m T u.family v.family
    rw [starRingEnd_apply, star_trivial]
    unfold parabolicInner
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => mixedInner_comm _ _ j i
  re_inner_nonneg u := by
    change 0 ≤ RCLike.re (parabolicInner g s p m T u.family u.family)
    rw [RCLike.re_to_real]
    exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => mixedInner_self_nonneg _ j i
  add_left u v w := by
    change parabolicInner g s p m T (fun τ => u.family τ + v.family τ) w.family =
      parabolicInner g s p m T u.family w.family + parabolicInner g s p m T v.family w.family
    unfold parabolicInner
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => mixedInner_add_left u.2 v.2 w.2 j i
  smul_left u v c := by
    change parabolicInner g s p m T (fun τ => c • u.family τ) v.family =
      (starRingEnd ℝ) c * parabolicInner g s p m T u.family v.family
    rw [starRingEnd_apply, star_trivial]
    unfold parabolicInner
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => mixedInner_smul_left u.2 c j i

instance : SeminormedAddCommGroup (ParabolicPre g s p m T) :=
  @InnerProductSpace.Core.toSeminormedAddCommGroup ℝ (ParabolicPre g s p m T) _ _ _ (core g s p m T)

instance : InnerProductSpace ℝ (ParabolicPre g s p m T) := InnerProductSpace.ofCore (core g s p m T)

/-- The families vanishing at `t = 0`. -/
def zeroAtStart : Submodule ℝ (ParabolicPre g s p m T) where
  carrier := {u | u.family 0 = 0}
  add_mem' {u v} hu hv := by
    change u.family 0 + v.family 0 = 0
    rw [hu, hv, add_zero]
  zero_mem' := rfl
  smul_mem' c u hu := by
    change c • u.family 0 = 0
    rw [hu, smul_zero]

end ParabolicPre

/-- The parabolic Sobolev space `𝒫^m` (`def:parabolic`), the completion of the smooth families. -/
abbrev ParabolicSpace (s p m : ℕ) (T : ℝ) : Type _ := UniformSpace.Completion (ParabolicPre g s p m T)

namespace ParabolicSpace

variable {g} {s p m : ℕ} {T : ℝ}

/-- A smooth family as an element of `𝒫^m`. -/
def ofSmooth (u : ℝ → SmoothCcTensor g 0 s) (hu : JointlySmoothOn g 0 s (Icc 0 T) u) :
    ParabolicSpace g s p m T :=
  UniformSpace.Completion.coe' (show ParabolicPre g s p m T from ⟨u, hu⟩)

variable (g s p m T) in
/-- `𝒫^m_0`, the closure in `𝒫^m` of the smooth families vanishing at `t = 0` (`def:parabolic`). -/
def zeroAtStart : Submodule ℝ (ParabolicSpace g s p m T) :=
  (ParabolicPre.zeroAtStart.map
    (UniformSpace.Completion.toComplL (𝕜 := ℝ) (E := ParabolicPre g s p m T)).toLinearMap).topologicalClosure

theorem ofSmooth_mem_zeroAtStart (u : ℝ → SmoothCcTensor g 0 s)
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u) (h0 : u 0 = 0) :
    ofSmooth (p := p) (m := m) u hu ∈ zeroAtStart g s p m T :=
  Submodule.le_topologicalClosure _ (Submodule.mem_map.mpr ⟨_, h0, rfl⟩)

end ParabolicSpace

end ShortTime
