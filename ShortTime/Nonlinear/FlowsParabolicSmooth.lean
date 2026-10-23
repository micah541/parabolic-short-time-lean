import ShortTime.Nonlinear.FlowsParabolicDeriv
import ShortTime.Nonlinear.ParabolicBound
import ShortTime.Nonlinear.NemytskiiRep

/-!
# Smooth dependence of `Π_σ u` on `σ` in `𝒫^m`

Paper: Lemma `lem:flows` (a): for smooth `u`, `σ ↦ Π_σ u` is `C^∞` into `𝒫^m`.

* `hasDerivAt_ofSmooth_hpull`: for a jointly smooth family `u` on `[0,T]`,
  `d/dσ (Π_σ u) = Π_σ ∇_X u` in `𝒫^m`, at every `σ`.
* `contDiff_ofSmooth_hpull`: `σ ↦ Π_σ u` is `C^∞` from `ℝ` into `𝒫^m`.

Proof of the derivative: the jets of `R_h = Π_{σ+h} u - Π_σ u - h Π_σ ∇_X u` are
`∇^i Π_{σ+h} w - ∇^i Π_σ w - h ∇^i Π_σ ∇_X w` with `w = ∂ₜ^j u(t)` (`timeDerivIter_hpull`,
`timeDerivIter_covAlong`). Their fibre norms are `O(h²)` uniformly in `(t, x)`: pair with the
remainder itself and apply the mean value inequality twice to the scalar function
`τ ↦ ⟨R, ∇^i Π_τ w⟩` (`taylor_fiber`), whose second derivative is `⟨R, ∇^i Π_τ ∇_X² w⟩`; the latter is
bounded by Cauchy–Schwarz and the uniform jet bound `exists_jetNormSq_hpull_le`. Integrating
(`parabolicInner_le_of_jetSq_le`) gives `‖R_h‖_{𝒫^m} = O(h²)`.
-/

noncomputable section

open Bundle Manifold Set Filter MeasureTheory
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Analysis.ODE
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

namespace ShortTime

namespace HFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

/-! ### Second-order Taylor bound in a fibre -/

section Taylor

variable (g : SmoothRiemannianMetric I M)

/-- `w ↦ ⟨v, w⟩_x`, as a continuous linear functional on the model fibre. -/
def innerL (a : ℕ) (x : M) (v : TensorRSModel 0 a ℝ E) : TensorRSModel 0 a ℝ E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => tensorInnerPointwise (I := I) (M := M) g 0 a x v w
      map_add' := tensorInnerPointwise_add_right (I := I) (M := M) g 0 a x v
      map_smul' := fun c w => tensorInnerPointwise_smul_right (I := I) (M := M) g 0 a x c v w }

theorem innerL_apply (a : ℕ) (x : M) (v w : TensorRSModel 0 a ℝ E) :
    innerL g a x v w = tensorInnerPointwise (I := I) (M := M) g 0 a x v w := rfl

theorem sq_le_of_sq_le_mul {q D : ℝ} (hq : 0 ≤ q) (hD : 0 ≤ D) (h : q ^ 2 ≤ q * D) :
    q ^ 2 ≤ D ^ 2 := by
  rcases eq_or_lt_of_le hq with h0 | hpos
  · rw [← h0, zero_pow two_ne_zero]; exact sq_nonneg D
  · have : q ≤ D := by nlinarith
    exact pow_le_pow_left₀ hq this 2

/-- **Second-order Taylor bound, in the fibre norm.** If `A' = B`, `B' = Dd` and
`|Dd τ|² ≤ D²` between `σ` and `σ + h`, then `|A(σ+h) - A(σ) - h B(σ)|² ≤ (h² D)²`. -/
theorem taylor_fiber (a : ℕ) (x : M) {A B Dd : ℝ → TensorRSModel 0 a ℝ E}
    (hA : ∀ τ, HasDerivAt A (B τ) τ) (hB : ∀ τ, HasDerivAt B (Dd τ) τ) (σ h : ℝ) {D : ℝ}
    (hD0 : 0 ≤ D)
    (hD : ∀ τ ∈ uIcc σ (σ + h), tensorInnerPointwise (I := I) (M := M) g 0 a x (Dd τ) (Dd τ) ≤ D ^ 2) :
    tensorInnerPointwise (I := I) (M := M) g 0 a x
        (A (σ + h) + ((-1 : ℝ) • A σ + (-h) • B σ)) (A (σ + h) + ((-1 : ℝ) • A σ + (-h) • B σ)) ≤
      (h ^ 2 * D) ^ 2 := by
  set v := A (σ + h) + ((-1 : ℝ) • A σ + (-h) • B σ) with hv
  set L := innerL g a x v with hL
  have hvv0 : 0 ≤ tensorInnerPointwise (I := I) (M := M) g 0 a x v v :=
    tensorInnerPointwise_nonneg g 0 a x v
  set q := Real.sqrt (tensorInnerPointwise (I := I) (M := M) g 0 a x v v) with hq
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hqq : q ^ 2 = tensorInnerPointwise (I := I) (M := M) g 0 a x v v := Real.sq_sqrt hvv0
  have hLv : tensorInnerPointwise (I := I) (M := M) g 0 a x v v =
      L (A (σ + h)) - L (A σ) - h * L (B σ) := by
    change L v = _
    rw [hv, map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    ring
  -- `|⟨v, Dd τ⟩| ≤ q D`
  have hLd : ∀ τ ∈ uIcc σ (σ + h), ‖L (Dd τ)‖ ≤ q * D := by
    intro τ hτ
    have hcs := tensorInnerPointwise_sq_le_mul (I := I) (M := M) g 0 a x v (Dd τ)
    have h1 : (L (Dd τ)) ^ 2 ≤ (q * D) ^ 2 := by
      rw [mul_pow, hqq]
      exact hcs.trans (mul_le_mul_of_nonneg_left (hD τ hτ) hvv0)
    rw [Real.norm_eq_abs]
    have h2 := sq_le_sq.mp h1
    rwa [abs_of_nonneg (mul_nonneg hq0 hD0)] at h2
  have hconv : Convex ℝ (uIcc σ (σ + h)) := convex_uIcc σ (σ + h)
  have hσmem : σ ∈ uIcc σ (σ + h) := left_mem_uIcc
  -- first mean value inequality: `|⟨v, B τ⟩ - ⟨v, B σ⟩| ≤ q D |τ - σ|`
  have hmv1 : ∀ τ ∈ uIcc σ (σ + h), ‖L (B τ) - L (B σ)‖ ≤ q * D * ‖τ - σ‖ := fun τ hτ =>
    hconv.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun τ => L (B τ))
      (fun y _ => (L.hasFDerivAt.comp_hasDerivAt y (hB y)).hasDerivWithinAt) hLd hσmem hτ
  -- second mean value inequality, for `ψ τ = ⟨v, A τ⟩ - τ ⟨v, B σ⟩`
  have hψ : ∀ y, HasDerivAt (fun τ => L (A τ) - τ * L (B σ)) (L (B y) - L (B σ)) y := fun y => by
    have h1 := (L.hasFDerivAt.comp_hasDerivAt y (hA y)).sub ((hasDerivAt_id y).mul_const (L (B σ)))
    rw [one_mul] at h1
    exact h1
  have hbd : ∀ y ∈ uIcc σ (σ + h), ‖L (B y) - L (B σ)‖ ≤ q * D * |h| := by
    intro y hy
    refine (hmv1 y hy).trans (mul_le_mul_of_nonneg_left ?_ (mul_nonneg hq0 hD0))
    rw [Real.norm_eq_abs]
    have := abs_sub_left_of_mem_uIcc hy
    simpa using this
  have hmv2 := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun τ => L (A τ) - τ * L (B σ)) (fun y _ => (hψ y).hasDerivWithinAt) hbd hσmem
    right_mem_uIcc
  have hdiff : (L (A (σ + h)) - (σ + h) * L (B σ)) - (L (A σ) - σ * L (B σ)) =
      tensorInnerPointwise (I := I) (M := M) g 0 a x v v := by
    rw [hLv]; ring
  rw [hdiff, Real.norm_eq_abs, Real.norm_eq_abs, add_sub_cancel_left] at hmv2
  have h3 : q ^ 2 ≤ q * (h ^ 2 * D) := by
    rw [hqq]
    refine (le_abs_self _).trans (hmv2.trans (le_of_eq ?_))
    rw [mul_assoc, ← sq_abs h]
    ring
  rw [← hqq]
  exact sq_le_of_sq_le_mul hq0 (by positivity) h3

end Taylor

/-! ### The remainder in `𝒫^m` -/

section Remainder

variable (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
variable (g : SmoothRiemannianMetric I M) (s : ℕ)

/-- The remainder `R_h = Π_{σ+h} u - Π_σ u - h Π_σ ∇_X u`. -/
def hpullRem (u : ℝ → SmoothCcTensor g 0 s) (σ h : ℝ) : ℝ → SmoothCcTensor g 0 s := fun t =>
  hpull X g s (σ + h) (u t) +
    ((-1 : ℝ) • hpull X g s σ (u t) + (-h) • hpull X g s σ (covAlong X g s (u t)))

theorem jointlySmoothOn_hpullRem {T : ℝ} {u : ℝ → SmoothCcTensor g 0 s}
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u) (σ h : ℝ) :
    JointlySmoothOn g 0 s (Icc 0 T) (hpullRem X g s u σ h) :=
  jointlySmoothOn_add (jointlySmoothOn_hpull X g s (σ + h) hu)
    (jointlySmoothOn_add (jointlySmoothOn_smul (-1) (jointlySmoothOn_hpull X g s σ hu))
      (jointlySmoothOn_smul (-h) (jointlySmoothOn_hpull X g s σ (jointlySmoothOn_covAlong X g s hu))))

/-- The time derivatives of the remainder. -/
theorem timeDerivIter_hpullRem {T : ℝ} (hT : 0 < T) {u : ℝ → SmoothCcTensor g 0 s}
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u) (σ h : ℝ) (j : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    timeDerivIter T (hpullRem X g s u σ h) j t =
      hpull X g s (σ + h) (timeDerivIter T u j t) +
        ((-1 : ℝ) • hpull X g s σ (timeDerivIter T u j t) +
          (-h) • hpull X g s σ (covAlong X g s (timeDerivIter T u j t))) := by
  have hA := jointlySmoothOn_hpull X g s (σ + h) hu
  have hB := jointlySmoothOn_hpull X g s σ hu
  have hC := jointlySmoothOn_hpull X g s σ (jointlySmoothOn_covAlong X g s hu)
  unfold hpullRem
  rw [timeDerivIter_add_apply hA (jointlySmoothOn_add (jointlySmoothOn_smul (-1) hB)
      (jointlySmoothOn_smul (-h) hC)),
    timeDerivIter_add_apply (jointlySmoothOn_smul (-1) hB) (jointlySmoothOn_smul (-h) hC),
    timeDerivIter_smul_apply (-1) hB, timeDerivIter_smul_apply (-h) hC,
    timeDerivIter_hpull X g s hT hu (σ + h) j ht, timeDerivIter_hpull X g s hT hu σ j ht,
    timeDerivIter_hpull X g s hT (jointlySmoothOn_covAlong X g s hu) σ j ht,
    timeDerivIter_covAlong X g s hT hu j ht]

/-- The single top term of the squared jet. -/
theorem fiberNormSq_le_jetNormSq (N : ℕ) (v : SmoothCcTensor g 0 s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 (s + N) x
        ((iteratedCovGrad g 0 s N v).toSection x) ≤ jetNormSq g s N v x := by
  have e : jetNormSq g s N v x = ∑ k ∈ Finset.range (N + 1),
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + k) x
        ((iteratedCovGrad g 0 s k v).toSection x) :=
    Fin.sum_univ_eq_sum_range (fun k => riemannianFiberNormSq (I := I) (M := M) g 0 (s + k) x
        ((iteratedCovGrad g 0 s k v).toSection x)) (N + 1)
  rw [e]
  exact Finset.single_le_sum (f := fun k => riemannianFiberNormSq (I := I) (M := M) g 0
      (s + k) x ((iteratedCovGrad g 0 s k v).toSection x))
    (fun k _ => riemannianFiberNormSq_nonneg g 0 (s + k) _ _) (Finset.self_mem_range_succ N)

theorem toModel_iteratedCovGrad_comb (i : ℕ) (x : M) (A B C : SmoothCcTensor g 0 s) (h : ℝ) :
    TensorRSSpace.toModel ((iteratedCovGrad g 0 s i (A + ((-1 : ℝ) • B + (-h) • C))).toSection x) =
      TensorRSSpace.toModel ((iteratedCovGrad g 0 s i A).toSection x) +
        ((-1 : ℝ) • TensorRSSpace.toModel ((iteratedCovGrad g 0 s i B).toSection x) +
          (-h) • TensorRSSpace.toModel ((iteratedCovGrad g 0 s i C).toSection x)) := by
  simp only [Analysis.Spectral.iteratedCovGrad_add, Analysis.Spectral.iteratedCovGrad_smul,
    SmoothCcTensor.toSection_add, SmoothCcTensor.toSection_smul,
    ContMDiffSection.coe_add, ContMDiffSection.coe_smul, Pi.add_apply, Pi.smul_apply,
    TensorRSSpace.toModel_add, TensorRSSpace.toModel_smul]

/-- The remainder bound at a point, for a fixed smooth field `w`. -/
theorem fiber_rem_le (w : SmoothCcTensor g 0 s) (i : ℕ) (x : M) (σ h : ℝ) {D : ℝ} (hD0 : 0 ≤ D)
    (hD : ∀ τ ∈ uIcc σ (σ + h), riemannianFiberNormSq (I := I) (M := M) g 0 (s + i) x
      ((iteratedCovGrad g 0 s i (hpull X g s τ (covAlong X g s (covAlong X g s w)))).toSection x) ≤
        D ^ 2) :
    riemannianFiberNormSq (I := I) (M := M) g 0 (s + i) x
      ((iteratedCovGrad g 0 s i (hpull X g s (σ + h) w +
        ((-1 : ℝ) • hpull X g s σ w + (-h) • hpull X g s σ (covAlong X g s w)))).toSection x) ≤
      (h ^ 2 * D) ^ 2 := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise, toModel_iteratedCovGrad_comb]
  exact taylor_fiber g (s + i) x
    (A := fun τ => TensorRSSpace.toModel ((iteratedCovGrad g 0 s i (hpull X g s τ w)).toSection x))
    (B := fun τ => TensorRSSpace.toModel
      ((iteratedCovGrad g 0 s i (hpull X g s τ (covAlong X g s w))).toSection x))
    (Dd := fun τ => TensorRSSpace.toModel
      ((iteratedCovGrad g 0 s i (hpull X g s τ (covAlong X g s (covAlong X g s w)))).toSection x))
    (fun τ => hasDerivAt_iteratedCovGrad_hpull X g s w i x τ)
    (fun τ => hasDerivAt_iteratedCovGrad_hpull X g s (covAlong X g s w) i x τ) σ h hD0
    (fun τ hτ => by rw [← riemannianFiberNormSq_eq_tensorInnerPointwise]; exact hD τ hτ)

/-- **The pointwise remainder bound**: the jets of `R_h` are `O(h²)`, uniformly on `M × [0,T]`. -/
theorem exists_jetSq_hpullRem_le {T : ℝ} (hT : 0 < T) {u : ℝ → SmoothCcTensor g 0 s}
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u) (σ : ℝ) (m N : ℕ) :
    ∃ K, 0 ≤ K ∧ ∀ h : ℝ, |h| ≤ 1 → ∀ j i, j ≤ m → i ≤ N → ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      jetSq g T (hpullRem X g s u σ h) j i t x ≤ (h ^ 2) ^ 2 * K := by
  classical
  have hZs : ∀ j, JointlySmoothOn g 0 s (Icc 0 T)
      (fun t => covAlong X g s (covAlong X g s (timeDerivIter T u j t))) := fun j =>
    jointlySmoothOn_covAlong X g s (jointlySmoothOn_covAlong X g s
      (jointlySmoothOn_timeDerivIter hT hu j))
  choose B hB0 hB using fun j => Vendor.joint_jet_bdd g 0 s
    (fun t => covAlong X g s (covAlong X g s (timeDerivIter T u j t))) (isCompact_Icc (a := (0 : ℝ))
    (b := T)) subset_rfl (hZs j)
  choose C hC0 hC using fun i => exists_jetNormSq_hpull_le X g s i (|σ| + 1)
  obtain ⟨Dsq, hDsq⟩ : ∃ Dsq : ℕ → ℕ → ℝ, Dsq = fun j i => C i * ∑ k : Fin (i + 1), B j k :=
    ⟨_, rfl⟩
  have hDsq0 : ∀ j i, 0 ≤ Dsq j i := fun j i => by
    rw [hDsq]; exact mul_nonneg (hC0 i) (Finset.sum_nonneg fun k _ => hB0 j k)
  refine ⟨∑ j ∈ Finset.range (m + 1), ∑ i ∈ Finset.range (N + 1), Dsq j i,
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => hDsq0 j i,
    fun h hh j i hj hi t ht x => ?_⟩
  have hDK : Dsq j i ≤ ∑ j ∈ Finset.range (m + 1), ∑ i ∈ Finset.range (N + 1), Dsq j i := by
    refine (Finset.single_le_sum (f := fun i => Dsq j i) (fun i _ => hDsq0 j i)
      (Finset.mem_range.mpr (show i < N + 1 by omega))).trans ?_
    exact Finset.single_le_sum (f := fun j => ∑ i ∈ Finset.range (N + 1), Dsq j i)
      (fun j _ => Finset.sum_nonneg fun i _ => hDsq0 j i)
      (Finset.mem_range.mpr (show j < m + 1 by omega))
  have hsecond : ∀ τ ∈ uIcc σ (σ + h), riemannianFiberNormSq (I := I) (M := M) g 0 (s + i) x
      ((iteratedCovGrad g 0 s i (hpull X g s τ (covAlong X g s (covAlong X g s
        (timeDerivIter T u j t))))).toSection x) ≤ Real.sqrt (Dsq j i) ^ 2 := by
    intro τ hτ
    rw [Real.sq_sqrt (hDsq0 j i), hDsq]
    have hτR : |τ| ≤ |σ| + 1 := by
      have h1 := abs_sub_left_of_mem_uIcc hτ
      simp only [add_sub_cancel_left] at h1
      calc |τ| = |σ + (τ - σ)| := by ring_nf
        _ ≤ |σ| + |τ - σ| := abs_add_le _ _
        _ ≤ |σ| + 1 := by linarith
    refine (fiberNormSq_le_jetNormSq g s i _ x).trans ((hC i τ hτR _ x).trans
      (mul_le_mul_of_nonneg_left ?_ (hC0 i)))
    exact Finset.sum_le_sum fun k _ => hB j k t ht _
  have hrem := fiber_rem_le X g s (timeDerivIter T u j t) i x σ h (Real.sqrt_nonneg _) hsecond
  rw [mul_pow, Real.sq_sqrt (hDsq0 j i)] at hrem
  have hjet : jetSq g T (hpullRem X g s u σ h) j i t x =
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + i) x
        ((iteratedCovGrad g 0 s i (hpull X g s (σ + h) (timeDerivIter T u j t) +
          ((-1 : ℝ) • hpull X g s σ (timeDerivIter T u j t) +
            (-h) • hpull X g s σ (covAlong X g s (timeDerivIter T u j t))))).toSection x) := by
    unfold jetSq
    rw [timeDerivIter_hpullRem X g s hT hu σ h j ht]
  rw [hjet]
  exact hrem.trans (mul_le_mul_of_nonneg_left hDK (by positivity))

end Remainder

/-! ### Differentiability and smoothness in `σ` -/

section Smooth

variable (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
variable (g : SmoothRiemannianMetric I M) (s : ℕ)

open ParabolicSpace

variable {p m : ℕ} {T : ℝ}

/-- **The `𝒫^m` derivative of the horizontal pullback**: `d/dσ (Π_σ u) = Π_σ ∇_X u` in `𝒫^m`. -/
theorem hasDerivAt_ofSmooth_hpull (hT : 0 < T) {u : ℝ → SmoothCcTensor g 0 s}
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u) (σ : ℝ) :
    HasDerivAt (fun τ => ofSmooth (p := p) (m := m) (fun t => hpull X g s τ (u t))
        (jointlySmoothOn_hpull X g s τ hu))
      (ofSmooth (fun t => hpull X g s σ (covAlong X g s (u t)))
        (jointlySmoothOn_hpull X g s σ (jointlySmoothOn_covAlong X g s hu))) σ := by
  obtain ⟨K, hK0, hK⟩ := exists_jetSq_hpullRem_le X g s hT hu σ m (2 * p * m)
  set c := K * parabolicCount p m *
    (T * (riemannianVolumeMeasure (I := I) (M := M) g).real univ + 1) with hc
  have hc0 : 0 ≤ c := mul_nonneg (mul_nonneg hK0 (Nat.cast_nonneg _))
    (by have := mul_nonneg hT.le (measureReal_nonneg (μ := riemannianVolumeMeasure (I := I) (M := M) g)
          (s := univ)); linarith)
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  refine Asymptotics.IsBigO.trans_isLittleO (g := fun h : ℝ => h ^ 2) ?_
    (Asymptotics.isLittleO_pow_id one_lt_two)
  refine Asymptotics.IsBigO.of_bound (Real.sqrt c) ?_
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with h hh
  have hh1 : |h| ≤ 1 := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hh; exact hh.le
  -- the difference quotient remainder is `R_h`
  have hR := jointlySmoothOn_hpullRem X g s hu σ h
  have heq : ofSmooth (p := p) (m := m) (fun t => hpull X g s (σ + h) (u t))
        (jointlySmoothOn_hpull X g s (σ + h) hu) -
      ofSmooth (p := p) (m := m) (fun t => hpull X g s σ (u t)) (jointlySmoothOn_hpull X g s σ hu) -
      h • ofSmooth (p := p) (m := m) (fun t => hpull X g s σ (covAlong X g s (u t)))
        (jointlySmoothOn_hpull X g s σ (jointlySmoothOn_covAlong X g s hu)) =
      ofSmooth (p := p) (m := m) (hpullRem X g s u σ h) hR := by
    have hA := jointlySmoothOn_hpull X g s (σ + h) hu
    have hB := jointlySmoothOn_hpull X g s σ hu
    have hC := jointlySmoothOn_hpull X g s σ (jointlySmoothOn_covAlong X g s hu)
    have e1 := ofSmooth_add (p := p) (m := m) hA
      (jointlySmoothOn_add (jointlySmoothOn_smul (-1) hB) (jointlySmoothOn_smul (-h) hC))
    have e2 := ofSmooth_add (p := p) (m := m) (jointlySmoothOn_smul (-1) hB)
      (jointlySmoothOn_smul (-h) hC)
    have e3 := ofSmooth_smul (p := p) (m := m) (-1) hB
    have e4 := ofSmooth_smul (p := p) (m := m) (-h) hC
    change _ = ofSmooth (p := p) (m := m) (fun t => hpull X g s (σ + h) (u t) +
      ((-1 : ℝ) • hpull X g s σ (u t) + (-h) • hpull X g s σ (covAlong X g s (u t)))) hR
    rw [e1, e2, e3, e4, neg_smul, one_smul, neg_smul]
    abel
  rw [heq]
  -- the `𝒫^m` norm of `R_h`
  have hsq : ‖ofSmooth (p := p) (m := m) (hpullRem X g s u σ h) hR‖ ^ 2 ≤ c * (h ^ 2) ^ 2 := by
    rw [norm_ofSmooth_sq]
    have hb := parabolicInner_le_of_jetSq_le (N := m) (p := p) hT hR
      (b := fun _ : Empty => s) (V := fun c => c.elim) (fun c => c.elim)
      (C := (h ^ 2) ^ 2 * K) (by positivity) (fun j i hj hi t ht x => by
        simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, mul_one]
        exact hK h hh1 j i hj (hi.trans (Nat.mul_le_mul_left _ (Nat.sub_le m j))) t ht x)
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, mul_one] at hb
    refine hb.trans (le_of_eq ?_)
    rw [hc]; ring
  have hnorm : ‖ofSmooth (p := p) (m := m) (hpullRem X g s u σ h) hR‖ ≤ Real.sqrt c * (h ^ 2) := by
    have h1 := Real.le_sqrt_of_sq_le hsq
    rwa [Real.sqrt_mul hc0, Real.sqrt_sq (sq_nonneg h)] at h1
  refine hnorm.trans (le_of_eq ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg h)]

/-- **`σ ↦ Π_σ u` is `C^∞` into `𝒫^m`** for every jointly smooth family `u`. -/
theorem contDiff_ofSmooth_hpull_nat (hT : 0 < T) :
    ∀ (n : ℕ) {u : ℝ → SmoothCcTensor g 0 s} (hu : JointlySmoothOn g 0 s (Icc 0 T) u),
      ContDiff ℝ n (fun τ => ofSmooth (p := p) (m := m) (fun t => hpull X g s τ (u t))
        (jointlySmoothOn_hpull X g s τ hu))
  | 0, u, hu => by
    rw [Nat.cast_zero, contDiff_zero]
    exact Differentiable.continuous
      (fun σ => (hasDerivAt_ofSmooth_hpull X g s hT hu σ).differentiableAt)
  | n + 1, u, hu => by
    have hderiv : deriv (fun τ => ofSmooth (p := p) (m := m) (fun t => hpull X g s τ (u t))
        (jointlySmoothOn_hpull X g s τ hu)) =
        fun σ => ofSmooth (p := p) (m := m) (fun t => hpull X g s σ (covAlong X g s (u t)))
          (jointlySmoothOn_hpull X g s σ (jointlySmoothOn_covAlong X g s hu)) :=
      funext fun σ => (hasDerivAt_ofSmooth_hpull X g s hT hu σ).deriv
    rw [Nat.cast_succ, contDiff_succ_iff_deriv]
    refine ⟨fun σ => (hasDerivAt_ofSmooth_hpull X g s hT hu σ).differentiableAt,
      fun h => absurd h (by simp), ?_⟩
    rw [hderiv]
    exact contDiff_ofSmooth_hpull_nat hT n (jointlySmoothOn_covAlong X g s hu)

/-- **`σ ↦ Π_σ u` is `C^∞` from `ℝ` into `𝒫^m`** (`lem:flows` (a)). -/
theorem contDiff_ofSmooth_hpull (hT : 0 < T) {u : ℝ → SmoothCcTensor g 0 s}
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u) :
    ContDiff ℝ ∞ (fun τ => ofSmooth (p := p) (m := m) (fun t => hpull X g s τ (u t))
      (jointlySmoothOn_hpull X g s τ hu)) :=
  contDiff_infty.mpr fun n => contDiff_ofSmooth_hpull_nat X g s hT n hu

end Smooth

end HFlow

end ShortTime
