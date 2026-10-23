import ShortTime.Linear.GoodSeq
import ShortTime.Analysis.UniformLimit
import ShortTime.Vendor.ParametricJets
import DifferentialGeometry.Analysis.Spectral.Tensor.TrivProj.CovNormBound

/-!
# Smooth limits of good sequences (`lem:embedding`, last part)

If `wₘ` is a good sequence (`Good`: every `∇^i ∂ₜ^j wₘ` is uniformly Cauchy on `M × [0,T]`), its
limit is jointly smooth. The proof reads the families in charts:

* `covApply_eq_insField`: `∇_B T = (insField B)(∇T)`.
* In the chart at `α`, the derivative of the chart reading of `wₘ` is built from the chart readings of
  `∂ₜwₘ`, of `∇_{B_k} wₘ` (vector fields with constant chart coordinates) and of `wₘ` itself (the
  library's formula `chart_pulled_covApply_explicit_formula_target_smoothCc`).
* These are again good sequences, so by induction on `n` the limit is `C^n` for every `n`
  (`hasFDerivWithinAt_of_tendstoUniformlyOn_convex`).
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

/-- `∇_B T = (insField B)(∇T)`. -/
theorem covApply_eq_insField {a : ℕ} (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (T : SmoothCcTensor g 0 a) (x : M) :
    covApply (TensorRSNabla.tensorRSCovariantDerivative I M 0 a (LeviCivita (I := I) g)) B.toFun
        (fun z => T.toSection z) x =
      (operatorFieldApply (I := I) (M := M) g (a + 1) a (insField g B)
        (covGrad (I := I) (M := M) g 0 a T)).toSection x := by
  rw [operatorFieldApplication_toSection]
  refine ContinuousLinearMap.ext fun D => Tensor0SSpace.toModel_injective ?_
  refine ContinuousMultilinearMap.ext fun m => ?_
  change _ = Tensor0SSpace.toModel (insFib I x (B x)
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (a + 1) I x from
      (covGrad (I := I) (M := M) g 0 a T).toSection x) D)) m
  rw [toModel_insFib, ContinuousMultilinearMap.curryLeft_apply, covGrad_toSection_apply_eval,
    tensorCovDerivAt_def]
  rfl

/-! ### Chart readings -/

variable (g) in
/-- The reading of a section in the chart and trivialization at `α`, at the chart point `y`. -/
def chartRd (α : M) {a : ℕ} (S : SmoothCcTensor g 0 a) (y : E) : TensorRSModel 0 a ℝ E :=
  tensorRSChartESectionRepr (I := I) 0 a α (fun z => S.toSection z) ((extChartAt I α).symm y)

/-- Vector fields with prescribed constant coordinates near `α`. -/
theorem exists_const_coord_fields (α : M) {ι : Type*} (c : ι → E) :
    ∃ B : ι → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯,
      ∀ᶠ x in 𝓝 α, ∀ i, trivToE I α x (B i x) = c i := by
  set e := trivializationAt E (TangentSpace I : M → Type _) α with he
  have hs : ∀ j, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) y (e.symmL ℝ y (c j)))
      e.baseSet := by
    intro j
    rw [e.contMDiffOn_iff fun y hy => e.mem_source.mpr hy]
    refine ⟨contMDiffOn_id, (contMDiffOn_const (c := c j)).congr fun y hy => ?_⟩
    rw [Trivialization.symmL_apply _ hy, e.apply_mk_symm hy]
  obtain ⟨B, hB⟩ := exists_contMDiffSection_eqOn_nhd (I := I)
    (s := fun j y => e.symmL ℝ y (c j)) hs e.open_baseSet (mem_baseSet_trivializationAt _ _ α)
  refine ⟨B, ?_⟩
  filter_upwards [hB, e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt _ _ α)] with x hx hxb i
  rw [hx i]
  exact e.continuousLinearMapAt_symmL hxb _

/-- **The chart derivative of a section**: along the chart coordinates of `B`, it is the chart reading
of `∇_B S` plus a Christoffel term. -/
theorem fderiv_chartRd (α : M) {a : ℕ} (S : SmoothCcTensor g 0 a)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) {y : E} (hy : y ∈ (extChartAt I α).target) :
    fderiv ℝ (chartRd g α S) y (trivToE I α ((extChartAt I α).symm y) (B ((extChartAt I α).symm y))) =
      chartRd g α (operatorFieldApply (I := I) (M := M) g (a + 1) a (insField g B)
          (covGrad (I := I) (M := M) g 0 a S)) y +
        ∑ l : Fin a, outputSlotChartKernel (I := I) g 0 a α B.toFun l ((extChartAt I α).symm y)
          (chartRd g α S y) := by
  have hsrc : (extChartAt I α).symm y ∈ (extChartAt I α).source := (extChartAt I α).map_target hy
  have hgood : (extChartAt I α).symm y ∈ chartLeviCivitaGoodSet (I := I) α := by
    rw [chartLeviCivitaGoodSet_eq_extChartAt_source]; exact hsrc
  have hchart : (extChartAt I α).symm y ∈ (chartAt H α).source := by
    rw [← extChartAt_source (I := I)]; exact hsrc
  have h := chart_pulled_covApply_explicit_formula_target_smoothCc (I := I) (M := M) g 0 a α S B hy hgood
  have hcov : covApply (TensorRSNabla.tensorRSCovariantDerivative I M 0 a
      (LeviCivita (I := I) g)) B.toFun (fun z => S.toSection z) =
      fun b => (operatorFieldApply (I := I) (M := M) g (a + 1) a (insField g B)
        (covGrad (I := I) (M := M) g 0 a S)).toSection b :=
    funext fun b => covApply_eq_insField B S b
  rw [hcov] at h
  simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, Function.comp_apply] at h
  simp only [chartTensorRSOutputSlotCorrection_chart_kernel_factorization (I := I) (M := M) g 0 a α
    _ _ hchart] at h
  unfold chartRd
  rw [h]
  simp only [tensorRSChartE_section_repr_apply]
  exact (sub_add_cancel _ _).symm

/-- Chart readings are bounded by the fibre norm on compact subsets of the chart domain. -/
theorem exists_norm_twist_le (α : M) (a : ℕ) {K : Set M} (hK : IsCompact K)
    (hKs : K ⊆ (chartAt H α).source) :
    ∃ C, 0 ≤ C ∧ ∀ b ∈ K, ∀ v : TensorRSSpace 0 a I b,
      ‖chartRSTwistInv (I := I) (M := M) α b 0 a (TensorRSSpace.toModel v)‖ ^ 2 ≤
        C * riemannianFiberNormSq (I := I) (M := M) g 0 a b v := by
  have hKb : K ⊆ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hKs
  obtain ⟨C, hC0, hC⟩ :=
    chartRSTwistInv_sq_norm_le_const_mul_tensorInnerPointwise_on_compact (g := g) 0 a α hK hKb
  refine ⟨C, hC0, fun b hb v => ?_⟩
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise]
  exact hC hb _

theorem chartRd_eq_twist (α : M) {a : ℕ} (S : SmoothCcTensor g 0 a) {y : E}
    (hy : y ∈ (extChartAt I α).target) :
    chartRd g α S y = chartRSTwistInv (I := I) (M := M) α ((extChartAt I α).symm y) 0 a
      (TensorRSSpace.toModel (S.toSection ((extChartAt I α).symm y))) := by
  have hs : (extChartAt I α).symm y ∈ (chartAt H α).source := by
    rw [← extChartAt_source (I := I)]; exact (extChartAt I α).map_target hy
  unfold chartRd
  rw [tensorRSChartE_section_repr_apply, triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel 0 a α hs]

theorem chartRd_sub (α : M) {a : ℕ} (S S' : SmoothCcTensor g 0 a) (y : E) :
    chartRd g α (S - S') y = chartRd g α S y - chartRd g α S' y := by
  simp only [chartRd, tensorRSChartE_section_repr_apply, SmoothCcTensor.toSection_sub,
    ContMDiffSection.coe_sub, Pi.sub_apply, map_sub]

/-- Uniformly Cauchy sequences have uniformly Cauchy chart readings on compact sets. -/
theorem UCauchy.chartRd_uniform {T : ℝ} {a : ℕ} {w : ℕ → ℝ → SmoothCcTensor g 0 a} (hw : UCauchy T w)
    (α : M) {Ky : Set E} (hK : IsCompact Ky) (hKt : Ky ⊆ (extChartAt I α).target) :
    ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ m' ≥ N, ∀ t ∈ Icc (0 : ℝ) T, ∀ y ∈ Ky,
      ‖chartRd g α (w m t) y - chartRd g α (w m' t) y‖ ≤ ε := by
  intro ε hε
  set K := (extChartAt I α).symm '' Ky
  have hKc : IsCompact K := hK.image_of_continuousOn ((continuousOn_extChartAt_symm α).mono hKt)
  have hKs : K ⊆ (chartAt H α).source := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← extChartAt_source (I := I)]
    exact (extChartAt I α).map_target (hKt hy)
  obtain ⟨C, hC0, hC⟩ := exists_norm_twist_le (g := g) α a hKc hKs
  obtain ⟨N, hN⟩ := hw (ε ^ 2 / (C + 1)) (by positivity)
  refine ⟨N, fun m hm m' hm' t ht y hy => ?_⟩
  rw [← chartRd_sub]
  have h1 := hC _ ⟨y, hy, rfl⟩ ((w m t - w m' t).toSection ((extChartAt I α).symm y))
  have h2 := hN m hm m' hm' t ht ((extChartAt I α).symm y)
  have h3 : ‖chartRd g α (w m t - w m' t) y‖ ^ 2 ≤ ε ^ 2 := by
    rw [chartRd_eq_twist α _ (hKt hy)]
    refine h1.trans ?_
    calc C * _ ≤ C * (ε ^ 2 / (C + 1)) := mul_le_mul_of_nonneg_left h2 hC0
      _ ≤ ε ^ 2 := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith [sq_nonneg ε]
  exact pow_le_pow_iff_left₀ (norm_nonneg _) hε.le (by norm_num) |>.mp h3

/-- A chart patch around `α`: a closed ball in the chart target on which the vector fields `B k` have
constant chart coordinates `b k`. -/
theorem exists_chart_patch (α : M) :
    ∃ r > 0, ∃ B : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯,
      Metric.closedBall (extChartAt I α α) r ⊆ (extChartAt I α).target ∧
      ∀ y ∈ Metric.closedBall (extChartAt I α α) r, ∀ k,
        trivToE I α ((extChartAt I α).symm y) (B k ((extChartAt I α).symm y)) =
          Module.finBasis ℝ E k := by
  obtain ⟨B, hB⟩ := exists_const_coord_fields (I := I) α (Module.finBasis ℝ E)
  have hc : Tendsto (extChartAt I α).symm (𝓝 (extChartAt I α α)) (𝓝 α) := by
    have h := continuousAt_extChartAt_symm (I := I) α
    rwa [ContinuousAt, extChartAt_to_inv] at h
  have h1 := hc.eventually hB
  have h2 : ∀ᶠ y in 𝓝 (extChartAt I α α), y ∈ (extChartAt I α).target :=
    extChartAt_target_mem_nhds (I := I) α
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.eventually_iff.mp (h1.and h2)
  exact ⟨r, hr, B, fun y hy => (hball hy).2, fun y hy => (hball hy).1⟩

/-- The time derivative of a chart reading is the chart reading of the time derivative. -/
theorem hasDerivWithinAt_chartRd_time {T : ℝ} (hT : 0 < T) (α : M) {a : ℕ}
    {w : ℝ → SmoothCcTensor g 0 a} (hw : JointlySmoothOn g 0 a (Icc 0 T) w) {t : ℝ}
    (ht : t ∈ Icc 0 T) {y : E} (hy : y ∈ (extChartAt I α).target) :
    HasDerivWithinAt (fun τ => chartRd g α (w τ) y) (chartRd g α (timeDeriv T w t) y) (Icc 0 T) t := by
  simp only [chartRd_eq_twist α _ hy]
  unfold chartRSTwistInv
  have hX := hasDerivWithinAt_timeDeriv hT hw ht ((extChartAt I α).symm y)
  have h := (hasDerivWithinAt_const t (Icc 0 T) (ContinuousMultilinearMap.compContinuousLinearMapL
      (𝕜 := ℝ) (E := fun _ : Fin a => E) (F := ℝ)
      (fun _ : Fin a => Tensor.Tensor0SRiemannian.chartTrivializationLinearMapSymm (I := I) (M := M) α
        ((extChartAt I α).symm y)))).clm_comp
    (hX.clm_comp (hasDerivWithinAt_const t (Icc 0 T) (ContinuousMultilinearMap.compContinuousLinearMapL
      (𝕜 := ℝ) (E := fun _ : Fin 0 => E) (F := ℝ)
      (fun _ : Fin 0 => Tensor.Tensor0SRiemannian.chartTrivializationLinearMap (I := I) (M := M) α ((extChartAt I α).symm y)))))
  simpa using h

/-! ### The derivative of chart readings on a patch -/

/-- The `k`-th coordinate functional of the model basis. -/
def coordL (k : Fin (Module.finrank ℝ E)) : E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord k)

theorem sum_coordL_smul (v : E) : ∑ k, coordL k v • Module.finBasis ℝ E k = v := by
  simpa [coordL] using (Module.finBasis ℝ E).sum_repr v

variable (g) in
/-- The Christoffel term along `B` at the chart point `y`. -/
def kerSum (α : M) (a : ℕ) (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (y : E) :
    TensorRSModel 0 a ℝ E →L[ℝ] TensorRSModel 0 a ℝ E :=
  ∑ l : Fin a, outputSlotChartKernel (I := I) g 0 a α B.toFun l ((extChartAt I α).symm y)

variable (g) in
/-- The space-time derivative assembled from the time derivative `Gt`, the derivatives `Gk k` along
`B k` and the value `G`. -/
def combL (α : M) (a : ℕ) (B : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Gt : TensorRSModel 0 a ℝ E) (Gk : Fin (Module.finrank ℝ E) → TensorRSModel 0 a ℝ E)
    (G : TensorRSModel 0 a ℝ E) (y : E) : ℝ × E →L[ℝ] TensorRSModel 0 a ℝ E :=
  (ContinuousLinearMap.fst ℝ ℝ E).smulRight Gt +
    ∑ k, ((coordL k).comp (ContinuousLinearMap.snd ℝ ℝ E)).smulRight (Gk k + kerSum g α a (B k) y G)

theorem combL_apply (α : M) (a : ℕ) (B : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Gt : TensorRSModel 0 a ℝ E) (Gk : Fin (Module.finrank ℝ E) → TensorRSModel 0 a ℝ E)
    (G : TensorRSModel 0 a ℝ E) (y : E) (τ : ℝ) (v : E) :
    combL g α a B Gt Gk G y (τ, v) = τ • Gt + ∑ k, coordL k v • (Gk k + kerSum g α a (B k) y G) := by
  simp [combL]

/-- **Derivative of the chart reading of a smooth family** on a patch. -/
theorem hasFDerivWithinAt_chartRd {T : ℝ} (hT : 0 < T) {α : M} {r : ℝ}
    {B : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯}
    (hball : Metric.closedBall (extChartAt I α α) r ⊆ (extChartAt I α).target)
    (hB : ∀ y ∈ Metric.closedBall (extChartAt I α α) r, ∀ k,
      trivToE I α ((extChartAt I α).symm y) (B k ((extChartAt I α).symm y)) = Module.finBasis ℝ E k)
    {a : ℕ} {w : ℝ → SmoothCcTensor g 0 a} (hw : JointlySmoothOn g 0 a (Icc 0 T) w)
    {q : ℝ × E} (hq : q ∈ Icc 0 T ×ˢ Metric.ball (extChartAt I α α) r) :
    HasFDerivWithinAt (fun q : ℝ × E => chartRd g α (w q.1) q.2)
      (combL g α a B (chartRd g α (timeDeriv T w q.1) q.2)
        (fun k => chartRd g α (operatorFieldApply (I := I) (M := M) g (a + 1) a (insField g (B k))
          (covGrad (I := I) (M := M) g 0 a (w q.1))) q.2)
        (chartRd g α (w q.1) q.2) q.2)
      (Icc 0 T ×ˢ Metric.ball (extChartAt I α α) r) q := by
  obtain ⟨ht, hyb⟩ := hq
  have hyc : q.2 ∈ Metric.closedBall (extChartAt I α α) r := Metric.ball_subset_closedBall hyb
  have hy : q.2 ∈ (extChartAt I α).target := hball hyc
  set s' := Icc 0 T ×ˢ (extChartAt I α).target
  have hcd := Vendor.chartRepr_euclid_jointContDiffWithinAt (I := I) g 0 a w (Icc 0 T) α hw ht hy
  have hd : HasFDerivWithinAt (fun q : ℝ × E => chartRd g α (w q.1) q.2)
      (fderivWithin ℝ (fun q : ℝ × E => chartRd g α (w q.1) q.2) s' (q.1, q.2)) s' (q.1, q.2) :=
    (hcd.differentiableWithinAt (by simp)).hasFDerivWithinAt
  set L := fderivWithin ℝ (fun q : ℝ × E => chartRd g α (w q.1) q.2) s' (q.1, q.2)
  -- the spatial slice
  have hsp : ∀ v, L (0, v) = fderiv ℝ (chartRd g α (w q.1)) q.2 v := by
    have h1 : HasFDerivWithinAt (fun y => chartRd g α (w q.1) y)
        (L.comp (ContinuousLinearMap.inr ℝ ℝ E)) (extChartAt I α).target q.2 := by
      have hin : HasFDerivAt (fun y : E => (q.1, y)) (ContinuousLinearMap.inr ℝ ℝ E) q.2 :=
        (hasFDerivAt_const q.1 q.2).prodMk (hasFDerivAt_id q.2)
      exact hd.comp q.2 hin.hasFDerivWithinAt fun y hy' => (⟨ht, hy'⟩ : (q.1, y) ∈ s')
    have h2 := (h1.hasFDerivAt ((isOpen_extChartAt_target α).mem_nhds hy)).fderiv
    intro v
    rw [h2]
    rfl
  -- the time slice
  have htm : L (1, 0) = chartRd g α (timeDeriv T w q.1) q.2 := by
    have h1 : HasFDerivWithinAt (fun t => chartRd g α (w t) q.2)
        (L.comp (ContinuousLinearMap.inl ℝ ℝ E)) (Icc 0 T) q.1 := by
      have hin : HasFDerivAt (fun t : ℝ => (t, q.2)) (ContinuousLinearMap.inl ℝ ℝ E) q.1 :=
        (hasFDerivAt_id q.1).prodMk (hasFDerivAt_const q.2 q.1)
      exact hd.comp q.1 hin.hasFDerivWithinAt fun t ht' => (⟨ht', hy⟩ : (t, q.2) ∈ s')
    have h2 := h1.hasDerivWithinAt
    exact (uniqueDiffOn_Icc hT q.1 ht).eq_deriv _ h2 (hasDerivWithinAt_chartRd_time hT α hw ht hy)
  refine (hd.mono (prod_mono subset_rfl (Metric.ball_subset_closedBall.trans hball))).congr_fderiv ?_
  refine ContinuousLinearMap.ext fun p => ?_
  obtain ⟨τ, v⟩ := p
  have hdec : ((τ, v) : ℝ × E) = τ • ((1 : ℝ), (0 : E)) + ((0 : ℝ), v) := by
    ext <;> simp
  rw [hdec, map_add, map_smul, htm, hsp, combL_apply]
  simp only [smul_eq_mul, mul_one, smul_zero, add_zero, zero_add, Prod.smul_mk, Prod.mk_add_mk]
  congr 1
  conv_lhs => rw [← sum_coordL_smul v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, ← hB q.2 hyc k, fderiv_chartRd α (w q.1) (B k) hy, kerSum,
    ContinuousLinearMap.sum_apply]

/-! ### Limits of chart readings -/

variable (g) in
/-- The pointwise limit of the chart readings of `wₘ`. -/
def limChart (α : M) {a : ℕ} (w : ℕ → ℝ → SmoothCcTensor g 0 a) (q : ℝ × E) :
    TensorRSModel 0 a ℝ E :=
  limUnder atTop (fun m => chartRd g α (w m q.1) q.2)

theorem tendstoUniformlyOn_limChart {T : ℝ} {α : M} {r : ℝ}
    (hball : Metric.closedBall (extChartAt I α α) r ⊆ (extChartAt I α).target)
    {a : ℕ} {w : ℕ → ℝ → SmoothCcTensor g 0 a} (hw : UCauchy T w) :
    TendstoUniformlyOn (fun m (q : ℝ × E) => chartRd g α (w m q.1) q.2) (limChart g α w) atTop
      (Icc 0 T ×ˢ Metric.closedBall (extChartAt I α α) r) := by
  have hC : UniformCauchySeqOn (fun m (q : ℝ × E) => chartRd g α (w m q.1) q.2) atTop
      (Icc 0 T ×ˢ Metric.closedBall (extChartAt I α α) r) := by
    refine Metric.uniformCauchySeqOn_iff.2 fun ε hε => ?_
    obtain ⟨N, hN⟩ := hw.chartRd_uniform α (isCompact_closedBall _ _) hball (ε / 2) (half_pos hε)
    exact ⟨N, fun m hm n hn q hq => by
      rw [dist_eq_norm]; exact (hN m hm n hn q.1 hq.1 q.2 hq.2).trans_lt (half_lt_self hε)⟩
  exact hC.tendstoUniformlyOn_of_tendsto fun q hq =>
    tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete (hC.cauchySeq hq))

theorem contDiffAt_kerSum (α : M) (a : ℕ) (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {y : E} (hy : y ∈ (extChartAt I α).target) : ContDiffAt ℝ ∞ (kerSum g α a B) y := by
  have hgood : (extChartAt I α).symm y ∈ chartLeviCivitaGoodSet (I := I) α := by
    rw [chartLeviCivitaGoodSet_eq_extChartAt_source]; exact (extChartAt I α).map_target hy
  have h := fun l => outputSlotChartKernel_contDiffAt_chart_pulled (I := I) (M := M) g 0 a α B l hgood
  simp only [(extChartAt I α).right_inv hy] at h
  change ContDiffAt ℝ ∞ (fun y => ∑ l : Fin a, outputSlotChartKernel (I := I) g 0 a α B.toFun l
    ((extChartAt I α).symm y)) y
  exact ContDiffAt.sum fun l _ => h l

theorem combL_sub (α : M) (a : ℕ) (B : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Gt Gt' : TensorRSModel 0 a ℝ E) (Gk Gk' : Fin (Module.finrank ℝ E) → TensorRSModel 0 a ℝ E)
    (G G' : TensorRSModel 0 a ℝ E) (y : E) :
    combL g α a B Gt Gk G y - combL g α a B Gt' Gk' G' y =
      combL g α a B (Gt - Gt') (Gk - Gk') (G - G') y := by
  refine ContinuousLinearMap.ext fun p => ?_
  obtain ⟨τ, v⟩ := p
  simp only [ContinuousLinearMap.sub_apply, combL_apply, Pi.sub_apply, map_sub, smul_sub]
  rw [add_sub_add_comm, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← smul_sub]
  congr 1
  abel

theorem norm_combL_le (α : M) (a : ℕ)
    (B : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Gt : TensorRSModel 0 a ℝ E) (Gk : Fin (Module.finrank ℝ E) → TensorRSModel 0 a ℝ E)
    (G : TensorRSModel 0 a ℝ E) (y : E) :
    ‖combL g α a B Gt Gk G y‖ ≤
      ‖Gt‖ + ∑ k, ‖coordL k‖ * (‖Gk k‖ + ‖kerSum g α a (B k) y‖ * ‖G‖) := by
  unfold combL
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [ContinuousLinearMap.norm_smulRight_apply]
    exact (mul_le_of_le_one_left (norm_nonneg _) (ContinuousLinearMap.norm_fst_le ℝ ℝ E))
  · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [ContinuousLinearMap.norm_smulRight_apply]
    refine mul_le_mul ?_ ((norm_add_le _ _).trans (add_le_add le_rfl
      ((kerSum g α a (B k) y).le_opNorm G))) (norm_nonneg _) (norm_nonneg _)
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_of_le_one_right (norm_nonneg _) (ContinuousLinearMap.norm_snd_le ℝ ℝ E))

/-- `combL` of `C^n` data is `C^n`. -/
theorem contDiffOn_combL {α : M} {r : ℝ}
    (hball : Metric.closedBall (extChartAt I α α) r ⊆ (extChartAt I α).target) {a : ℕ}
    (B : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {S : Set ℝ} {n : ℕ} {Gt G : ℝ × E → TensorRSModel 0 a ℝ E}
    {Gk : Fin (Module.finrank ℝ E) → ℝ × E → TensorRSModel 0 a ℝ E}
    (ht : ContDiffOn ℝ n Gt (S ×ˢ Metric.ball (extChartAt I α α) r))
    (hk : ∀ k, ContDiffOn ℝ n (Gk k) (S ×ˢ Metric.ball (extChartAt I α α) r))
    (h0 : ContDiffOn ℝ n G (S ×ˢ Metric.ball (extChartAt I α α) r)) :
    ContDiffOn ℝ n (fun q => combL g α a B (Gt q) (fun k => Gk k q) (G q) q.2)
      (S ×ˢ Metric.ball (extChartAt I α α) r) := by
  have hker : ∀ k, ContDiffOn ℝ n (fun q : ℝ × E => kerSum g α a (B k) q.2)
      (S ×ˢ Metric.ball (extChartAt I α α) r) := fun k q hq =>
    (((contDiffAt_kerSum α a (B k) (hball (Metric.ball_subset_closedBall hq.2))).comp q
      contDiffAt_snd).of_le (by exact_mod_cast le_top)).contDiffWithinAt
  unfold combL
  refine ContDiffOn.add ?_ (ContDiffOn.sum fun k _ => ?_)
  · exact (contDiffOn_const (c := ContinuousLinearMap.smulRightL ℝ (ℝ × E) (TensorRSModel 0 a ℝ E)
      (ContinuousLinearMap.fst ℝ ℝ E))).clm_apply ht
  · exact (contDiffOn_const (c := ContinuousLinearMap.smulRightL ℝ (ℝ × E) (TensorRSModel 0 a ℝ E)
      ((coordL k).comp (ContinuousLinearMap.snd ℝ ℝ E)))).clm_apply
      ((hk k).add ((hker k).clm_apply h0))

theorem Good.ucauchy {T : ℝ} {a : ℕ} {w : ℕ → ℝ → SmoothCcTensor g 0 a} (hw : Good T w) :
    UCauchy T w :=
  (hw.2 0 0).congr fun _ _ _ => rfl

theorem continuousOn_limChart {T : ℝ} {α : M} {r : ℝ}
    (hball : Metric.closedBall (extChartAt I α α) r ⊆ (extChartAt I α).target)
    {a : ℕ} {w : ℕ → ℝ → SmoothCcTensor g 0 a} (hw : Good T w) :
    ContinuousOn (limChart g α w) (Icc 0 T ×ˢ Metric.closedBall (extChartAt I α α) r) :=
  (tendstoUniformlyOn_limChart hball hw.ucauchy).continuousOn (Frequently.of_forall fun m _ hq =>
    ((Vendor.chartRepr_euclid_jointContDiffWithinAt (I := I) g 0 a (w m) (Icc 0 T) α (hw.1 m)
      hq.1 (hball hq.2)).continuousWithinAt.mono (prod_mono subset_rfl hball)))

/-- **The derivative of the limit** of the chart readings of a good sequence. -/
theorem hasFDerivWithinAt_limChart {T : ℝ} (hT : 0 < T) {α : M} {r : ℝ}
    {B : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯}
    (hball : Metric.closedBall (extChartAt I α α) r ⊆ (extChartAt I α).target)
    (hB : ∀ y ∈ Metric.closedBall (extChartAt I α α) r, ∀ k,
      trivToE I α ((extChartAt I α).symm y) (B k ((extChartAt I α).symm y)) = Module.finBasis ℝ E k)
    {a : ℕ} {w : ℕ → ℝ → SmoothCcTensor g 0 a} (hw : Good T w)
    {q : ℝ × E} (hq : q ∈ Icc 0 T ×ˢ Metric.ball (extChartAt I α α) r) :
    HasFDerivWithinAt (limChart g α w)
      (combL g α a B (limChart g α (fun m => timeDeriv T (w m)) q)
        (fun k => limChart g α (fun m t => operatorFieldApply (I := I) (M := M) g (a + 1) a
          (insField g (B k)) (covGrad (I := I) (M := M) g 0 a (w m t))) q)
        (limChart g α w q) q.2)
      (Icc 0 T ×ˢ Metric.ball (extChartAt I α α) r) q := by
  have hsub : Icc 0 T ×ˢ Metric.ball (extChartAt I α α) r ⊆
      Icc 0 T ×ˢ Metric.closedBall (extChartAt I α α) r :=
    prod_mono subset_rfl Metric.ball_subset_closedBall
  have hgt : Good T (fun m => timeDeriv T (w m)) := hw.timeDeriv hT
  have hgk := fun k => hw.opField_covGrad hT (insField g (B k))
  have ut := (tendstoUniformlyOn_limChart hball hgt.ucauchy).mono hsub
  have uk := fun k => (tendstoUniformlyOn_limChart hball (hgk k).ucauchy).mono hsub
  have u0 := (tendstoUniformlyOn_limChart hball hw.ucauchy).mono hsub
  -- bounds on the Christoffel terms
  obtain ⟨Kk, hKk⟩ : ∃ K, ∀ y ∈ Metric.closedBall (extChartAt I α α) r, ∀ k,
      ‖kerSum g α a (B k) y‖ ≤ K := by
    have hc : ∀ k, ContinuousOn (fun y => ‖kerSum g α a (B k) y‖)
        (Metric.closedBall (extChartAt I α α) r) := fun k y hy =>
      (contDiffAt_kerSum α a (B k) (hball hy)).continuousAt.norm.continuousWithinAt
    choose K hK using fun k => (isCompact_closedBall (extChartAt I α α) r).exists_bound_of_continuousOn
      (hc k)
    exact ⟨∑ k, K k, fun y hy k => (le_abs_self _).trans ((Real.norm_eq_abs _).symm.trans_le
      ((hK k y hy).trans (Finset.single_le_sum (fun j _ => (norm_nonneg _).trans (hK j y hy))
        (Finset.mem_univ k))))⟩
  refine hasFDerivWithinAt_of_tendstoUniformlyOn_convex ((convex_Icc 0 T).prod (convex_ball _ _))
    (f := fun m q => chartRd g α (w m q.1) q.2)
    (f' := fun m q => combL g α a B (chartRd g α (timeDeriv T (w m) q.1) q.2)
      (fun k => chartRd g α (operatorFieldApply (I := I) (M := M) g (a + 1) a (insField g (B k))
        (covGrad (I := I) (M := M) g 0 a (w m q.1))) q.2) (chartRd g α (w m q.1) q.2) q.2)
    (g' := fun q => combL g α a B (limChart g α (fun m => timeDeriv T (w m)) q)
      (fun k => limChart g α (fun m t => operatorFieldApply (I := I) (M := M) g (a + 1) a
        (insField g (B k)) (covGrad (I := I) (M := M) g 0 a (w m t))) q)
      (limChart g α w q) q.2)
    (fun m q hq' => hasFDerivWithinAt_chartRd hT hball hB (hw.1 m) hq')
    (fun q hq' => u0.tendsto_at hq') ?_ ?_ hq
  · -- uniform convergence of the derivatives
    set Ctot : ℝ := 1 + ∑ k, ‖coordL (E := E) k‖ * (1 + |Kk|) with hCtot
    have hC : 0 < Ctot := by positivity
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hδ : 0 < ε / (2 * Ctot) := by positivity
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp ut _ hδ, Metric.tendstoUniformlyOn_iff.mp u0 _ hδ,
      Filter.eventually_all.2 fun k => Metric.tendstoUniformlyOn_iff.mp (uk k) _ hδ] with m h1 h2 h3
    intro q hq'
    rw [dist_eq_norm, combL_sub]
    refine (norm_combL_le α a B _ _ _ _).trans_lt ?_
    have e1 := h1 q hq'
    have e2 := h2 q hq'
    rw [dist_eq_norm] at e1 e2
    have e3 : ∀ k, ‖limChart g α (fun m t => operatorFieldApply (I := I) (M := M) g (a + 1) a
          (insField g (B k)) (covGrad (I := I) (M := M) g 0 a (w m t))) q -
        chartRd g α (operatorFieldApply (I := I) (M := M) g (a + 1) a (insField g (B k))
          (covGrad (I := I) (M := M) g 0 a (w m q.1))) q.2‖ < ε / (2 * Ctot) := fun k => by
      have := h3 k q hq'
      rwa [dist_eq_norm] at this
    have hK : ∀ k, ‖kerSum g α a (B k) q.2‖ ≤ |Kk| :=
      fun k => (hKk q.2 (Metric.ball_subset_closedBall hq'.2) k).trans (le_abs_self _)
    calc _ ≤ ε / (2 * Ctot) + ∑ k, ‖coordL (E := E) k‖ * (ε / (2 * Ctot) + |Kk| * (ε / (2 * Ctot))) := by
          refine add_le_add e1.le (Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left ?_
            (norm_nonneg _))
          exact add_le_add (e3 k).le (mul_le_mul (hK k) e2.le (norm_nonneg _) (abs_nonneg _))
      _ = ε / (2 * Ctot) * (1 + ∑ k, ‖coordL (E := E) k‖ * (1 + |Kk|)) := by
          conv_rhs => rw [mul_add, mul_one, Finset.mul_sum]
          congr 1
          exact Finset.sum_congr rfl fun k _ => by ring
      _ = ε / 2 := by rw [← hCtot]; field_simp
      _ < ε := half_lt_self hε
  · -- continuity of the limit derivative
    have hc := contDiffOn_combL (g := g) (n := 0) hball B (S := Icc 0 T)
      (contDiffOn_zero.2 ((continuousOn_limChart hball hgt).mono hsub))
      (fun k => contDiffOn_zero.2 ((continuousOn_limChart hball (hgk k)).mono hsub))
      (contDiffOn_zero.2 ((continuousOn_limChart hball hw).mono hsub))
    exact (contDiffOn_zero.1 hc)

/-- **The limit is `C^n` for every `n`** on the patch. -/
theorem contDiffOn_limChart {T : ℝ} (hT : 0 < T) {α : M} {r : ℝ}
    {B : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯}
    (hball : Metric.closedBall (extChartAt I α α) r ⊆ (extChartAt I α).target)
    (hB : ∀ y ∈ Metric.closedBall (extChartAt I α α) r, ∀ k,
      trivToE I α ((extChartAt I α).symm y) (B k ((extChartAt I α).symm y)) = Module.finBasis ℝ E k)
    {a : ℕ} : ∀ (n : ℕ) {w : ℕ → ℝ → SmoothCcTensor g 0 a}, Good T w →
      ContDiffOn ℝ n (limChart g α w) (Icc 0 T ×ˢ Metric.ball (extChartAt I α α) r)
  | 0, w, hw => by
    rw [Nat.cast_zero, contDiffOn_zero]
    exact (continuousOn_limChart hball hw).mono (prod_mono subset_rfl Metric.ball_subset_closedBall)
  | n + 1, w, hw => by
    have hU : UniqueDiffOn ℝ (Icc 0 T ×ˢ Metric.ball (extChartAt I α α) r) :=
      (uniqueDiffOn_Icc hT).prod Metric.isOpen_ball.uniqueDiffOn
    have hD := fun q (hq : q ∈ Icc 0 T ×ˢ Metric.ball (extChartAt I α α) r) =>
      hasFDerivWithinAt_limChart hT hball hB hw hq
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderivWithin hU]
    refine ⟨fun q hq => (hD q hq).differentiableWithinAt, fun h => absurd h (by simp), ?_⟩
    have hC := contDiffOn_combL (g := g) hball B (S := Icc 0 T)
      (contDiffOn_limChart hT hball hB n (hw.timeDeriv hT))
      (fun k => contDiffOn_limChart hT hball hB n (hw.opField_covGrad hT (insField g (B k))))
      (contDiffOn_limChart hT hball hB n hw)
    exact hC.congr fun q hq => (hD q hq).fderivWithin (hU q hq)

end ShortTime
