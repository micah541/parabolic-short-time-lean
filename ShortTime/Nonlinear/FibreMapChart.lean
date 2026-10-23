import ShortTime.Linear.LimitFamily
import ShortTime.Analysis.IterDir

/-!
# Covariant jets versus coordinate derivatives in a chart

In the chart and trivialization at `α`, on a patch where the vector fields `B k` have constant
coordinates (`exists_chart_patch`), the chart reading `G i = chartRd (∇^i S)` satisfies the first-order
recursion

  `D(G i) = slotIns (G (i+1)) + kerL (G i)`

(`fderiv_chartRd_eq`), with `slotIns` the insertion into the first slot and `kerL` a Christoffel
term. The Euclidean lemmas of `JetRecursion` then compare the coordinate derivatives of `chartRd S`
with the chart readings of the covariant derivatives `∇^k S`, uniformly on compact subsets of the
patch (`exists_iter_chartRd_le`, `exists_chartRd_iter_le`).
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff BigOperators

set_option linter.unusedSectionVars false

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

variable {g : SmoothRiemannianMetric I M}

/-! ### Insertion into the first slot, on model tensors -/

variable (E) in
/-- Currying the first slot of a model `(a+1)`-form. -/
def curE (a : ℕ) : Tensor0SModel (a + 1) ℝ E ≃L[ℝ] (E →L[ℝ] Tensor0SModel a ℝ E) :=
  (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (a + 1) => E) ℝ).toContinuousLinearEquiv

variable (E) in
/-- `D ↦ (v ↦ D(v, ·))` on model tensors. -/
def slotIns (a : ℕ) : TensorRSModel 0 (a + 1) ℝ E →L[ℝ] (E →L[ℝ] TensorRSModel 0 a ℝ E) :=
  (ContinuousLinearMap.flipₗᵢ ℝ (Tensor0SModel 0 ℝ E) E (Tensor0SModel a ℝ E)).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (ContinuousLinearMap.compL ℝ (Tensor0SModel 0 ℝ E) (Tensor0SModel (a + 1) ℝ E)
      (E →L[ℝ] Tensor0SModel a ℝ E) (curE E a).toContinuousLinearMap)

variable (E) in
/-- The inverse of `slotIns`. -/
def slotUnins (a : ℕ) : (E →L[ℝ] TensorRSModel 0 a ℝ E) →L[ℝ] TensorRSModel 0 (a + 1) ℝ E :=
  (ContinuousLinearMap.compL ℝ (Tensor0SModel 0 ℝ E) (E →L[ℝ] Tensor0SModel a ℝ E)
      (Tensor0SModel (a + 1) ℝ E) (curE E a).symm.toContinuousLinearMap).comp
    (ContinuousLinearMap.flipₗᵢ ℝ E (Tensor0SModel 0 ℝ E) (Tensor0SModel a ℝ E)).toContinuousLinearEquiv.toContinuousLinearMap

theorem slotIns_apply {a : ℕ} (D : TensorRSModel 0 (a + 1) ℝ E) (v : E) (β : Tensor0SModel 0 ℝ E) :
    slotIns E a D v β = curE E a (D β) v := rfl

theorem slotUnins_slotIns {a : ℕ} (D : TensorRSModel 0 (a + 1) ℝ E) :
    slotUnins E a (slotIns E a D) = D := by
  refine ContinuousLinearMap.ext fun β => ?_
  change (curE E a).symm (curE E a (D β)) = D β
  exact (curE E a).symm_apply_apply _

/-! ### Insertion of a vector field, in the chart -/

theorem mem_tangent_baseSet_of_target (α : M) {y : E} (hy : y ∈ (extChartAt I α).target) :
    (extChartAt I α).symm y ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
  rw [TangentBundle.trivializationAt_baseSet, ← extChartAt_source (I := I)]
  exact (extChartAt I α).map_target hy

/-- The chart reading of `D(B, ·)` is the chart reading of `D` with the coordinates of `B` inserted
into the first slot. -/
theorem chartRd_insField (α : M) {a : ℕ} (D : SmoothCcTensor g 0 (a + 1))
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) {y : E} (hy : y ∈ (extChartAt I α).target) :
    chartRd g α (operatorFieldApply (I := I) (M := M) g (a + 1) a (insField g B) D) y =
      slotIns E a (chartRd g α D y)
        (trivToE I α ((extChartAt I α).symm y) (B ((extChartAt I α).symm y))) := by
  have hxs := mem_tangent_baseSet_of_target (I := I) α hy
  set x := (extChartAt I α).symm y with hx
  rw [chartRd_eq_twist α _ hy, chartRd_eq_twist α _ hy, toModel_opField_apply]
  refine ContinuousLinearMap.ext fun β => ContinuousMultilinearMap.ext fun m => ?_
  rw [slotIns_apply]
  change ((psiAt (insField g B) x) (TensorRSSpace.toModel (D.toSection x)
      (β.compContinuousLinearMap fun _ : Fin 0 =>
        Tensor.Tensor0SRiemannian.chartTrivializationLinearMap (I := I) (M := M) α x)))
      (fun i => Tensor.Tensor0SRiemannian.chartTrivializationLinearMapSymm (I := I) (M := M) α x
        (m i)) =
    (TensorRSSpace.toModel (D.toSection x)
      (β.compContinuousLinearMap fun _ : Fin 0 =>
        Tensor.Tensor0SRiemannian.chartTrivializationLinearMap (I := I) (M := M) α x))
      (fun i => Tensor.Tensor0SRiemannian.chartTrivializationLinearMapSymm (I := I) (M := M) α x
        ((Fin.cons (trivToE I α x (B x)) m : Fin (a + 1) → E) i))
  rw [psiAt_insField, ContinuousMultilinearMap.curryLeft_apply]
  congr 1
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp only [Fin.cons_zero]
    rw [Tensor.Tensor0SRiemannian.chartJinv_apply,
      Trivialization.symmL_continuousLinearMapAt _ hxs]
  · simp only [Fin.cons_succ]

/-! ### The first-order recursion for chart readings -/

variable (g) in
/-- The Christoffel term of the recursion: `G ↦ (v ↦ Σ_k v^k Γ_k G)`. -/
def kerL (α : M) (a : ℕ) (B : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (y : E) : TensorRSModel 0 a ℝ E →L[ℝ] (E →L[ℝ] TensorRSModel 0 a ℝ E) :=
  ∑ k, (ContinuousLinearMap.smulRightL ℝ E (TensorRSModel 0 a ℝ E) (coordL k)).comp
    (kerSum g α a (B k) y)

theorem kerL_apply (α : M) (a : ℕ)
    (B : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (y : E)
    (G : TensorRSModel 0 a ℝ E) (v : E) :
    kerL g α a B y G v = ∑ k, coordL k v • kerSum g α a (B k) y G := by
  simp only [kerL, ContinuousLinearMap.sum_apply, ContinuousLinearMap.coe_comp',
    Function.comp_apply]
  rfl

theorem contDiffOn_kerL (α : M) (a : ℕ)
    (B : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContDiffOn ℝ ∞ (kerL g α a B) (extChartAt I α).target := by
  intro y hy
  change ContDiffWithinAt ℝ ∞ (fun y => ∑ k, (ContinuousLinearMap.smulRightL ℝ E
    (TensorRSModel 0 a ℝ E) (coordL k)).comp (kerSum g α a (B k) y)) _ y
  exact (ContDiffAt.sum fun k _ =>
    (contDiffAt_const.clm_comp (contDiffAt_kerSum α a (B k) hy))).contDiffWithinAt

theorem coordL_finBasis (l k : Fin (Module.finrank ℝ E)) :
    coordL l (Module.finBasis ℝ E k) = if k = l then 1 else 0 := by
  simp [coordL, Module.Basis.repr_self, Finsupp.single_apply]

/-- **The chart derivative of a section, on a patch**: `D(chartRd S) = slotIns (chartRd ∇S) + kerL`. -/
theorem fderiv_chartRd_eq {α : M} {r : ℝ}
    {B : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯}
    (hball : Metric.closedBall (extChartAt I α α) r ⊆ (extChartAt I α).target)
    (hB : ∀ y ∈ Metric.closedBall (extChartAt I α α) r, ∀ k,
      trivToE I α ((extChartAt I α).symm y) (B k ((extChartAt I α).symm y)) = Module.finBasis ℝ E k)
    {a : ℕ} (S : SmoothCcTensor g 0 a) {y : E} (hy : y ∈ Metric.closedBall (extChartAt I α α) r) :
    fderiv ℝ (chartRd g α S) y =
      slotIns E a (chartRd g α (covGrad (I := I) (M := M) g 0 a S) y) +
        kerL g α a B y (chartRd g α S y) := by
  refine ContinuousLinearMap.ext fun v => ?_
  have hlin : ∀ L : E →L[ℝ] TensorRSModel 0 a ℝ E,
      L v = ∑ k, coordL k v • L (Module.finBasis ℝ E k) := fun L => by
    conv_lhs => rw [← sum_coordL_smul v]
    simp only [map_sum, map_smul]
  rw [hlin (fderiv ℝ (chartRd g α S) y), hlin (slotIns E a _ + kerL g α a B y _)]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  have h1 := fderiv_chartRd α S (B k) (hball hy)
  rw [hB y hy k] at h1
  rw [h1, chartRd_insField α _ (B k) (hball hy), hB y hy k, ContinuousLinearMap.add_apply,
    kerL_apply, Finset.sum_eq_single k]
  · rw [coordL_finBasis, if_pos rfl, one_smul, kerSum, ContinuousLinearMap.sum_apply]
  · intro l _ hl
    rw [coordL_finBasis, if_neg (Ne.symm hl), zero_smul]
  · simp

/-- Chart readings of smooth tensor fields are smooth on the chart target. -/
theorem contDiffOn_chartRd (α : M) {a : ℕ} (S : SmoothCcTensor g 0 a) :
    ContDiffOn ℝ ∞ (chartRd g α S) (extChartAt I α).target := by
  intro y hy
  have hF : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel 0 a ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel 0 a ℝ E)
        (E := fun z : M => TensorRSSpace 0 a I z) p.1 (((fun _ : ℝ => S) p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ Set.univ) := fun p _ =>
    ((S.toSection.contMDiff p.1).comp p contMDiffAt_fst).contMDiffWithinAt
  have h := Vendor.chartRepr_euclid_jointContDiffWithinAt (I := I) g 0 a (fun _ => S) univ α hF
    (mem_univ 0) hy
  exact h.comp y (contDiffWithinAt_const.prodMk contDiffWithinAt_id)
    (fun y' hy' => (⟨mem_univ _, hy'⟩ : ((0 : ℝ), y') ∈ (univ : Set ℝ) ×ˢ (extChartAt I α).target))

/-! ### Comparison of jets on a patch -/

section Patch

variable {α : M} {r₀ r : ℝ}
  {B : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯}

/-- **Coordinate derivatives are bounded by covariant jets.** -/
theorem exists_iter_chartRd_le
    (hball : Metric.closedBall (extChartAt I α α) r₀ ⊆ (extChartAt I α).target)
    (hB : ∀ y ∈ Metric.closedBall (extChartAt I α α) r₀, ∀ k,
      trivToE I α ((extChartAt I α).symm y) (B k ((extChartAt I α).symm y)) = Module.finBasis ℝ E k)
    (hr : r < r₀) (a N : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ S : SmoothCcTensor g 0 a, ∀ n ≤ N, ∀ y ∈ Metric.closedBall (extChartAt I α α) r,
      ‖iteratedFDeriv ℝ n (chartRd g α S) y‖ ≤
        C * ∑ k ∈ Finset.range (N + 1), ‖chartRd g α (iteratedCovGrad g 0 a k S) y‖ := by
  have hΩ : IsOpen (Metric.ball (extChartAt I α α) r₀) := Metric.isOpen_ball
  have hΩt : Metric.ball (extChartAt I α α) r₀ ⊆ (extChartAt I α).target :=
    Metric.ball_subset_closedBall.trans hball
  have hKΩ : Metric.closedBall (extChartAt I α α) r ⊆ Metric.ball (extChartAt I α α) r₀ :=
    Metric.closedBall_subset_ball hr
  obtain ⟨C, hC0, hC⟩ := JetRec.exists_iter_le_rec (F := fun k => TensorRSModel 0 (a + k) ℝ E)
    hΩ.uniqueDiffOn (isCompact_closedBall _ _) hKΩ (fun k => slotIns E (a + k))
    (fun k => kerL g α (a + k) B) (fun k => (contDiffOn_kerL α (a + k) B).mono hΩt) N 0
  refine ⟨C, hC0, fun S n hn y hy => ?_⟩
  have h := hC (fun k => chartRd g α (iteratedCovGrad g 0 a k S))
    (fun k => (contDiffOn_chartRd α _).mono hΩt)
    (fun k z hz => by
      rw [fderivWithin_of_isOpen hΩ hz]
      exact fderiv_chartRd_eq hball hB _ (Metric.ball_subset_closedBall hz))
    n hn y hy
  rw [iteratedFDerivWithin_of_isOpen n hΩ (hKΩ hy), zero_add] at h
  exact h

/-- **Covariant jets are bounded by coordinate derivatives.** -/
theorem exists_chartRd_iter_le
    (hball : Metric.closedBall (extChartAt I α α) r₀ ⊆ (extChartAt I α).target)
    (hB : ∀ y ∈ Metric.closedBall (extChartAt I α α) r₀, ∀ k,
      trivToE I α ((extChartAt I α).symm y) (B k ((extChartAt I α).symm y)) = Module.finBasis ℝ E k)
    (hr : r < r₀) (a i : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ S : SmoothCcTensor g 0 a, ∀ y ∈ Metric.closedBall (extChartAt I α α) r,
      ‖chartRd g α (iteratedCovGrad g 0 a i S) y‖ ≤
        C * ∑ m ∈ Finset.range (i + 1), ‖iteratedFDeriv ℝ m (chartRd g α S) y‖ := by
  have hΩ : IsOpen (Metric.ball (extChartAt I α α) r₀) := Metric.isOpen_ball
  have hΩt : Metric.ball (extChartAt I α α) r₀ ⊆ (extChartAt I α).target :=
    Metric.ball_subset_closedBall.trans hball
  have hKΩ : Metric.closedBall (extChartAt I α α) r ⊆ Metric.ball (extChartAt I α α) r₀ :=
    Metric.closedBall_subset_ball hr
  obtain ⟨C, hC0, hC⟩ := JetRec.exists_iter_le_rec_inv (F := fun k => TensorRSModel 0 (a + k) ℝ E)
    hΩ.uniqueDiffOn (isCompact_closedBall _ _) hKΩ (fun k => slotUnins E (a + k))
    (fun k => kerL g α (a + k) B) (fun k => (contDiffOn_kerL α (a + k) B).mono hΩt) i 0
  refine ⟨C, hC0, fun S y hy => ?_⟩
  have h := hC (fun k => chartRd g α (iteratedCovGrad g 0 a k S))
    (fun k => (contDiffOn_chartRd α _).mono hΩt)
    (fun k z hz => by
      rw [fderivWithin_of_isOpen hΩ hz,
        fderiv_chartRd_eq hball hB _ (Metric.ball_subset_closedBall hz), add_sub_cancel_right]
      exact (slotUnins_slotIns _).symm)
    0 le_rfl y hy
  rw [norm_iteratedFDerivWithin_zero, zero_add] at h
  refine h.trans (le_of_eq ?_)
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [iteratedFDerivWithin_of_isOpen m hΩ (hKΩ hy)]
  rfl

end Patch

/-! ### Families in space-time charts -/

variable (g) in
/-- The chart reading of a time-dependent family, as a function of `(t, y)`. -/
def chartFam (α : M) {a : ℕ} (u : ℝ → SmoothCcTensor g 0 a) (q : ℝ × E) : TensorRSModel 0 a ℝ E :=
  chartRd g α (u q.1) q.2

theorem contDiffOn_chartFam (α : M) {a : ℕ} {S : Set ℝ} {u : ℝ → SmoothCcTensor g 0 a}
    (hu : JointlySmoothOn g 0 a S u) :
    ContDiffOn ℝ ∞ (chartFam g α u) (S ×ˢ (extChartAt I α).target) := fun _q hq =>
  Vendor.chartRepr_euclid_jointContDiffWithinAt (I := I) g 0 a u S α hu hq.1 hq.2

section PatchTime

variable {α : M} {ρ T : ℝ}
  {B : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯}

theorem fderivWithin_chartFam_time (hT : 0 < T)
    (hball : Metric.closedBall (extChartAt I α α) ρ ⊆ (extChartAt I α).target)
    (hB : ∀ y ∈ Metric.closedBall (extChartAt I α α) ρ, ∀ k,
      trivToE I α ((extChartAt I α).symm y) (B k ((extChartAt I α).symm y)) = Module.finBasis ℝ E k)
    {a : ℕ} {u : ℝ → SmoothCcTensor g 0 a} (hu : JointlySmoothOn g 0 a (Icc 0 T) u)
    {q : ℝ × E} (hq : q ∈ Icc 0 T ×ˢ Metric.ball (extChartAt I α α) ρ) :
    fderivWithin ℝ (chartFam g α u) (Icc 0 T ×ˢ Metric.ball (extChartAt I α α) ρ) q
      ((1 : ℝ), (0 : E)) = chartFam g α (timeDeriv T u) q := by
  have h := (hasFDerivWithinAt_chartRd hT hball hB hu hq).fderivWithin
    (UniqueDiffOn.prod (uniqueDiffOn_Icc hT) Metric.isOpen_ball.uniqueDiffOn q hq)
  change fderivWithin ℝ (fun q : ℝ × E => chartRd g α (u q.1) q.2) _ q _ = _
  rw [h, combL_apply]
  simp [chartFam]

/-- **Mixed derivatives of chart readings**: spatial directions followed by `j` time directions. -/
theorem iteratedFDerivWithin_chartFam_append (hT : 0 < T)
    (hball : Metric.closedBall (extChartAt I α α) ρ ⊆ (extChartAt I α).target)
    (hB : ∀ y ∈ Metric.closedBall (extChartAt I α α) ρ, ∀ k,
      trivToE I α ((extChartAt I α).symm y) (B k ((extChartAt I α).symm y)) = Module.finBasis ℝ E k)
    {a : ℕ} {u : ℝ → SmoothCcTensor g 0 a} (hu : JointlySmoothOn g 0 a (Icc 0 T) u) (n j : ℕ)
    (e : Fin n → E) {q : ℝ × E} (hq : q ∈ Icc 0 T ×ˢ Metric.ball (extChartAt I α α) ρ) :
    iteratedFDerivWithin ℝ (n + j) (chartFam g α u) (Icc 0 T ×ˢ Metric.ball (extChartAt I α α) ρ) q
        (Fin.append (fun m => ((0 : ℝ), e m)) (fun _ : Fin j => ((1 : ℝ), (0 : E)))) =
      iteratedFDeriv ℝ n (chartRd g α (timeDerivIter T u j q.1)) q.2 e := by
  have hs : UniqueDiffOn ℝ (Icc 0 T ×ˢ Metric.ball (extChartAt I α α) ρ) :=
    UniqueDiffOn.prod (uniqueDiffOn_Icc hT) Metric.isOpen_ball.uniqueDiffOn
  have hsm : ∀ k, ContDiffOn ℝ ∞ (chartFam g α (timeDerivIter T u k))
      (Icc 0 T ×ˢ Metric.ball (extChartAt I α α) ρ) := fun k =>
    (contDiffOn_chartFam α (jointlySmoothOn_timeDerivIter hT hu k)).mono
      (prod_mono le_rfl (Metric.ball_subset_closedBall.trans hball))
  have h1 := IterDir.iteratedFDerivWithin_append_const hs ((1 : ℝ), (0 : E)) n
    (fun m => ((0 : ℝ), e m)) j (fun k => chartFam g α (timeDerivIter T u k)) hsm
    (fun k x hx => fderivWithin_chartFam_time hT hball hB
      (jointlySmoothOn_timeDerivIter hT hu k) hx) q hq
  refine h1.trans ?_
  rw [IterDir.iteratedFDerivWithin_prod_slice (uniqueDiffOn_Icc hT) Metric.isOpen_ball (hsm j) n e q hq,
    iteratedFDerivWithin_of_isOpen n Metric.isOpen_ball hq.2]
  rfl

/-- **Sorted mixed derivatives** (spatial directions of norm `≤ 1`, then time directions) of chart
readings are bounded by spatial derivatives of chart readings of time derivatives. -/
theorem norm_iteratedFDerivWithin_chartFam_sorted_le (hT : 0 < T)
    (hball : Metric.closedBall (extChartAt I α α) ρ ⊆ (extChartAt I α).target)
    (hB : ∀ y ∈ Metric.closedBall (extChartAt I α α) ρ, ∀ k,
      trivToE I α ((extChartAt I α).symm y) (B k ((extChartAt I α).symm y)) = Module.finBasis ℝ E k)
    {a : ℕ} {u : ℝ → SmoothCcTensor g 0 a} (hu : JointlySmoothOn g 0 a (Icc 0 T) u) {N sB : ℕ}
    (hsB : sB ≤ N) (w : Fin N → ℝ × E)
    (hsp : ∀ m : Fin N, (m : ℕ) < sB → (w m).1 = 0 ∧ ‖(w m).2‖ ≤ 1)
    (htm : ∀ m : Fin N, sB ≤ (m : ℕ) → w m = ((1 : ℝ), (0 : E)))
    {q : ℝ × E} (hq : q ∈ Icc 0 T ×ˢ Metric.ball (extChartAt I α α) ρ) :
    ‖iteratedFDerivWithin ℝ N (chartFam g α u) (Icc 0 T ×ˢ Metric.ball (extChartAt I α α) ρ) q w‖ ≤
      ‖iteratedFDeriv ℝ sB (chartRd g α (timeDerivIter T u (N - sB) q.1)) q.2‖ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hsB
  have hw : w = Fin.append (fun m => ((0 : ℝ), (w (Fin.castAdd k m)).2))
      (fun _ : Fin k => ((1 : ℝ), (0 : E))) := by
    conv_lhs => rw [← Fin.append_castAdd_natAdd (f := w)]
    congr 1
    · funext m
      exact Prod.ext (hsp _ (by simp)).1 rfl
    · funext m
      exact htm _ (by simp)
  rw [hw, iteratedFDerivWithin_chartFam_append hT hball hB hu sB k _ hq, Nat.add_sub_cancel_left]
  refine (ContinuousMultilinearMap.le_opNorm
    (iteratedFDeriv ℝ sB (chartRd g α (timeDerivIter T u k q.1)) q.2) _).trans ?_
  exact mul_le_of_le_one_right (norm_nonneg _)
    (Finset.prod_le_one (fun _ _ => norm_nonneg _) fun m _ => (hsp _ (by simp)).2)

end PatchTime

end ShortTime
