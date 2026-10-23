import ShortTime.Nonlinear.Evaluation
import ShortTime.Nonlinear.FibreCalcRemainder
import ShortTime.Nonlinear.EqFibre

/-!
# Smooth families inside `𝒫^m`: representatives

`ParabolicPre` is only seminormed (families may differ outside `[0,T]`), so the dense subspace on
which the composition operators of `cor:N` are defined is taken inside the completion:

* `ParabolicSpace.smoothSub g s p m T`: the image of the smooth families in `𝒫^m`, a normed
  subspace with dense range (`denseRange_smoothSub`).
* `ParabolicSpace.rep v`: a chosen smooth family representing `v`. Representatives are unique on
  `[0,T]` (`rep_eqOn`, for `m ≥ 1`), hence linear on `[0,T]` (`rep_add`, `rep_smul`).
* `ParabolicSpace.ofSmooth'`: `ofSmooth` of a family when it is smooth, `0` otherwise.
* `exists_fiberNormSq_jet_le`, `sum_jetFamily_le`: the jets `∇^k`, `k ≤ 2p`, of a smooth family are
  bounded pointwise, and in `𝒫^N`, by its `𝒫^{N+1}` norm.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set Filter Topology MeasureTheory
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Spectral
open scoped Manifold ContDiff BigOperators

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

variable {g : SmoothRiemannianMetric I M}

namespace ParabolicSpace

variable {s p m : ℕ} {T : ℝ}

/-! ### Linearity of `ofSmooth` -/

theorem ofSmooth_add {u v : ℝ → SmoothCcTensor g 0 s} (hu : JointlySmoothOn g 0 s (Icc 0 T) u)
    (hv : JointlySmoothOn g 0 s (Icc 0 T) v) :
    ofSmooth (p := p) (m := m) (fun t => u t + v t) (jointlySmoothOn_add hu hv) =
      ofSmooth u hu + ofSmooth v hv := by
  unfold ofSmooth
  rw [← UniformSpace.Completion.coe_add]
  rfl

theorem ofSmooth_sub {u v : ℝ → SmoothCcTensor g 0 s} (hu : JointlySmoothOn g 0 s (Icc 0 T) u)
    (hv : JointlySmoothOn g 0 s (Icc 0 T) v) :
    ofSmooth (p := p) (m := m) (fun t => u t - v t) (jointlySmoothOn_sub hu hv) =
      ofSmooth u hu - ofSmooth v hv := by
  unfold ofSmooth
  rw [← UniformSpace.Completion.coe_sub]
  rfl

theorem ofSmooth_smul {u : ℝ → SmoothCcTensor g 0 s} (c : ℝ)
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u) :
    ofSmooth (p := p) (m := m) (fun t => c • u t) (jointlySmoothOn_smul c hu) =
      c • ofSmooth u hu := by
  unfold ofSmooth
  rw [← UniformSpace.Completion.coe_smul]
  rfl

/-! ### `ofSmooth'` -/

open Classical in
/-- `ofSmooth` of a family when it is jointly smooth on `[0,T]`, and `0` otherwise. -/
def ofSmooth' (u : ℝ → SmoothCcTensor g 0 s) : ParabolicSpace g s p m T :=
  if h : JointlySmoothOn g 0 s (Icc 0 T) u then ofSmooth u h else 0

theorem ofSmooth'_eq {u : ℝ → SmoothCcTensor g 0 s} (hu : JointlySmoothOn g 0 s (Icc 0 T) u) :
    ofSmooth' (p := p) (m := m) (T := T) u = ofSmooth u hu := by
  rw [ofSmooth', dif_pos hu]

/-! ### The subspace of smooth families -/

variable (g s p m T) in
/-- The smooth families inside `𝒫^m`: a normed subspace with dense range. -/
def smoothSub : Submodule ℝ (ParabolicSpace g s p m T) :=
  LinearMap.range
    (UniformSpace.Completion.toComplL (𝕜 := ℝ) (E := ParabolicPre g s p m T)).toLinearMap

theorem ofSmooth_mem_smoothSub (u : ℝ → SmoothCcTensor g 0 s)
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u) :
    ofSmooth (p := p) (m := m) u hu ∈ smoothSub g s p m T :=
  ⟨⟨u, hu⟩, rfl⟩

/-- A smooth family as an element of `smoothSub`. -/
def smoothElt (u : ℝ → SmoothCcTensor g 0 s) (hu : JointlySmoothOn g 0 s (Icc 0 T) u) :
    smoothSub g s p m T :=
  ⟨ofSmooth u hu, ofSmooth_mem_smoothSub u hu⟩

@[simp] theorem coe_smoothElt (u : ℝ → SmoothCcTensor g 0 s)
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u) :
    ((smoothElt (p := p) (m := m) u hu : smoothSub g s p m T) : ParabolicSpace g s p m T) =
      ofSmooth u hu := rfl

theorem denseRange_smoothSub :
    DenseRange (smoothSub g s p m T).subtypeL := by
  refine Dense.mono ?_ (denseRange_toComplL (g := g) (s := s) (p := p) (m := m) (T := T))
  rintro _ ⟨u, rfl⟩
  exact ⟨⟨_, ⟨u, rfl⟩⟩, rfl⟩

theorem norm_subtypeL (v : smoothSub g s p m T) : ‖(smoothSub g s p m T).subtypeL v‖ = ‖v‖ := rfl

/-- A chosen smooth representative. -/
def rep (v : smoothSub g s p m T) : ℝ → SmoothCcTensor g 0 s :=
  (Classical.choose v.2).family

theorem rep_smooth (v : smoothSub g s p m T) : JointlySmoothOn g 0 s (Icc 0 T) (rep v) :=
  (Classical.choose v.2).2

theorem ofSmooth_rep (v : smoothSub g s p m T) :
    ofSmooth (p := p) (m := m) (rep v) (rep_smooth v) = (v : ParabolicSpace g s p m T) :=
  Classical.choose_spec v.2

theorem norm_sq_eq_rep (v : smoothSub g s p m T) :
    ‖v‖ ^ 2 = parabolicInner g s p m T (rep v) (rep v) := by
  rw [← norm_ofSmooth_sq (rep_smooth v), ofSmooth_rep]
  rfl

/-- **Representatives are unique on `[0,T]`.** -/
theorem rep_eqOn (hT : 0 < T) (hm : 1 ≤ m) {v : smoothSub g s p m T}
    {u : ℝ → SmoothCcTensor g 0 s} {hu : JointlySmoothOn g 0 s (Icc 0 T) u}
    (h : (v : ParabolicSpace g s p m T) = ofSmooth u hu) : EqOn (rep v) u (Icc 0 T) := by
  have h0 : ofSmooth (p := p) (m := m) (fun t => rep v t - u t)
      (jointlySmoothOn_sub (rep_smooth v) hu) = 0 := by
    rw [ofSmooth_sub (rep_smooth v) hu, ofSmooth_rep, h, sub_self]
  intro t ht
  have := eq_zero_of_ofSmooth_eq_zero hT hm _ h0 ht
  exact sub_eq_zero.1 this

theorem rep_smoothElt (hT : 0 < T) (hm : 1 ≤ m) (u : ℝ → SmoothCcTensor g 0 s)
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u) :
    EqOn (rep (smoothElt (p := p) (m := m) u hu)) u (Icc 0 T) :=
  rep_eqOn hT hm rfl

theorem rep_add (hT : 0 < T) (hm : 1 ≤ m) (v v' : smoothSub g s p m T) :
    EqOn (rep (v + v')) (fun t => rep v t + rep v' t) (Icc 0 T) :=
  rep_eqOn (hu := jointlySmoothOn_add (rep_smooth v) (rep_smooth v')) hT hm (by
    rw [ofSmooth_add (rep_smooth v) (rep_smooth v'), ofSmooth_rep, ofSmooth_rep, Submodule.coe_add])

theorem rep_smul (hT : 0 < T) (hm : 1 ≤ m) (c : ℝ) (v : smoothSub g s p m T) :
    EqOn (rep (c • v)) (fun t => c • rep v t) (Icc 0 T) :=
  rep_eqOn (hu := jointlySmoothOn_smul c (rep_smooth v)) hT hm (by
    rw [ofSmooth_smul c (rep_smooth v), ofSmooth_rep, Submodule.coe_smul])

theorem rep_sub (hT : 0 < T) (hm : 1 ≤ m) (v v' : smoothSub g s p m T) :
    EqOn (rep (v - v')) (fun t => rep v t - rep v' t) (Icc 0 T) :=
  rep_eqOn (hu := jointlySmoothOn_sub (rep_smooth v) (rep_smooth v')) hT hm (by
    rw [ofSmooth_sub (rep_smooth v) (rep_smooth v'), ofSmooth_rep, ofSmooth_rep, Submodule.coe_sub])

/-- `‖v - w‖²` through the representatives. -/
theorem norm_sub_sq_eq (v : smoothSub g s p m T) {w : ℝ → SmoothCcTensor g 0 s}
    (hw : JointlySmoothOn g 0 s (Icc 0 T) w) :
    ‖(v : ParabolicSpace g s p m T) - ofSmooth w hw‖ ^ 2 =
      parabolicInner g s p m T (fun t => rep v t - w t) (fun t => rep v t - w t) := by
  rw [← ofSmooth_rep v, ← ofSmooth_sub (rep_smooth v) hw, norm_ofSmooth_sq]

end ParabolicSpace

/-! ### Jets of smooth families -/

section Jets

variable {s p : ℕ} {T : ℝ}

/-- **Low jets are bounded pointwise by the `𝒫^{N+1}` norm** (for `N ≥ ⌊n/2p⌋ + 3`). -/
theorem exists_fiberNormSq_jet_le (hT : 0 < T) (hp : 1 ≤ p) {N : ℕ}
    (hN : Module.finrank ℝ E / (2 * p) + 3 ≤ N) :
    ∃ Ce : ℝ, 0 ≤ Ce ∧ ∀ v : ℝ → SmoothCcTensor g 0 s, JointlySmoothOn g 0 s (Icc 0 T) v →
      ∀ c : Fin (2 * p + 1), ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g 0 (s + c) x
          ((iteratedCovGrad g 0 s c (v t)).toSection x) ≤
          Ce * parabolicInner g s p (N + 1) T v v := by
  choose C hC0 hC using fun c : Fin (2 * p + 1) =>
    exists_jetSq_le_parabolicInner (g := g) hT hp hN (s + c)
  refine ⟨∑ c, C c, Finset.sum_nonneg fun c _ => hC0 c, fun v hv c t ht x => ?_⟩
  have hU := jointlySmoothOn_iteratedCovGrad hv c
  have h1 := hC c _ hU 0 0 (by simp) t ht x
  rw [jetSq_zero_zero] at h1
  refine h1.trans ?_
  have hP := parabolicInner_iteratedCovGrad_le hT hv (p := p) (N := N) (k := c)
    (Nat.lt_succ_iff.mp c.2)
  have hP0 : 0 ≤ parabolicInner g s p (N + 1) T v v := parabolicInner_self_nonneg _ _ _
  calc C c * parabolicInner g (s + c) p N T (fun t => iteratedCovGrad g 0 s c (v t))
        (fun t => iteratedCovGrad g 0 s c (v t))
      ≤ C c * parabolicInner g s p (N + 1) T v v := mul_le_mul_of_nonneg_left hP (hC0 c)
    _ ≤ (∑ c, C c) * parabolicInner g s p (N + 1) T v v :=
        mul_le_mul_of_nonneg_right
          (Finset.single_le_sum (fun c _ => hC0 c) (Finset.mem_univ c)) hP0

/-- **The jets in `𝒫^N`**: `Σ_{k ≤ 2p} ‖∇^k v‖²_{𝒫^N} ≤ (2p+1) ‖v‖²_{𝒫^{N+1}}`. -/
theorem sum_jetFamily_le (hT : 0 < T) {v : ℝ → SmoothCcTensor g 0 s}
    (hv : JointlySmoothOn g 0 s (Icc 0 T) v) (N : ℕ) :
    ∑ c : Fin (2 * p + 1), parabolicInner g (EquationData.jetRanks s p c) p N T
        (EquationData.jetFamily (p := p) v c) (EquationData.jetFamily (p := p) v c) ≤
      (2 * p + 1 : ℕ) * parabolicInner g s p (N + 1) T v v := by
  calc ∑ c : Fin (2 * p + 1), parabolicInner g (EquationData.jetRanks s p c) p N T
        (EquationData.jetFamily (p := p) v c) (EquationData.jetFamily (p := p) v c)
      ≤ ∑ _c : Fin (2 * p + 1), parabolicInner g s p (N + 1) T v v :=
        Finset.sum_le_sum fun c _ =>
          parabolicInner_iteratedCovGrad_le hT hv (p := p) (N := N) (k := c)
            (Nat.lt_succ_iff.mp c.2)
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end Jets

end ShortTime
