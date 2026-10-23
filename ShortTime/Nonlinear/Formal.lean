import ShortTime.Nonlinear.EqFibre
import ShortTime.Nonlinear.Cutoff
import ShortTime.Analysis.FaaDiBruno

/-!
# The formal power series solution (`lem:formal`)

For equation data `D` on `T⁰_s M` and an initial datum `u₀` with jets in the domain at `t = 0`, we
construct sections `a₀ = u₀, a₁, a₂, …` (`EquationData.formalCoeff`) such that every smooth `w` with
`∂ₜ^ℓ w(0) = a_ℓ` for `ℓ ≤ N` satisfies `∂ₜ^ℓ (∂ₜ w - F[w])(0) = 0` for `ℓ < N`
(`EquationData.formalCoeff_spec`).

* `a_{ℓ+1}` is the `ℓ`-th time derivative at `0` of `F[w_ℓ]`, where `w_ℓ = ∑_{i ≤ ℓ} t^i/i! a_i`
  (`EquationData.formalPoly`), on a short interval where the jets of `w_ℓ` lie in the domain
  (`EquationData.exists_time_jets_mem`, by openness of the domain and compactness of `M`).
* **Locality** (`EquationData.timeDerivIter_nonlinFamily_congr`): the time derivatives of `F[w]` at
  `0` up to order `n` only depend on those of `w`. Pointwise in `x`, `F[w](t, x)` is a smooth function
  of `(t, (∇^k w(t, x))_k)` (`modelF`), so this is the Faà di Bruno formula, together with
  `∂ₜ^j ∇^k w = ∇^k ∂ₜ^j w`.
* One-sided derivatives at `0` within `[0,T]` do not depend on `T`
  (`timeDerivIter_eqOn_of_le`).
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set Filter Topology
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Analysis.Sobolev
open scoped Manifold ContDiff

namespace ShortTime

/-! ### One-variable calculus -/

namespace Formal

section Calculus

variable {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- A continuous linear map commutes with iterated derivatives within a set. -/
theorem clm_iteratedDerivWithin {f : ℝ → Y} {S : Set ℝ} {z : ℝ} (hf : ContDiffOn ℝ ∞ f S)
    (hS : UniqueDiffOn ℝ S) (hz : z ∈ S) (L : Y →L[ℝ] Z) (j : ℕ) :
    L (iteratedDerivWithin j f S z) = iteratedDerivWithin j (L ∘ f) S z := by
  simp only [iteratedDerivWithin_eq_iteratedFDerivWithin]
  rw [L.iteratedFDerivWithin_comp_left (hf z hz) hS hz (by exact_mod_cast le_top)]
  rfl

/-- **Locality of the derivatives of a composition**: if `f₁` and `f₂` have the same derivatives
of order at most `n` at `z`, then so do `h ∘ f₁` and `h ∘ f₂` (Faà di Bruno). -/
theorem iteratedFDerivWithin_comp_congr {h : Y → Z} {f₁ f₂ : X → Y} {S : Set X} {t : Set Y}
    {n : ℕ} (hh : ContDiffOn ℝ n h t) (hf₁ : ContDiffOn ℝ n f₁ S) (hf₂ : ContDiffOn ℝ n f₂ S)
    (ht : UniqueDiffOn ℝ t) (hS : UniqueDiffOn ℝ S) (h₁ : MapsTo f₁ S t) (h₂ : MapsTo f₂ S t)
    {z : X} (hz : z ∈ S)
    (heq : ∀ j ≤ n, iteratedFDerivWithin ℝ j f₁ S z = iteratedFDerivWithin ℝ j f₂ S z) :
    iteratedFDerivWithin ℝ n (h ∘ f₁) S z = iteratedFDerivWithin ℝ n (h ∘ f₂) S z := by
  refine ContinuousMultilinearMap.ext fun v => ?_
  rw [FaaDiBruno.iteratedFDerivWithin_comp_apply_eq_sum hh hf₁ ht hS h₁ hz v,
    FaaDiBruno.iteratedFDerivWithin_comp_apply_eq_sum hh hf₂ ht hS h₂ hz v]
  have h0 : f₁ z = f₂ z := by
    have := congrArg (fun A => A (Fin.elim0 : Fin 0 → X)) (heq 0 (Nat.zero_le _))
    simpa only [iteratedFDerivWithin_zero_apply] using this
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [h0]
  congr 1
  funext i
  rw [heq _ (c.partSize_le i)]

theorem coeff_arith (i : ℕ) (t : ℝ) :
    ((i + 1 : ℕ) : ℝ) * t ^ (i + 1 - 1) / ((i + 1).factorial : ℝ) = t ^ i / (i.factorial : ℝ) := by
  rw [Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul]
  have h1 : ((i + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [mul_div_mul_left _ _ h1]

end Calculus

end Formal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

variable {g : SmoothRiemannianMetric I M}

namespace Formal

/-! ### Time derivatives of families -/

section Families

variable {a b : ℕ}

/-- The model values at `x` of a jointly smooth family are smooth in time. -/
theorem contDiffOn_toFun {T : ℝ} (hT : 0 < T) {A : ℝ → SmoothCcTensor g a b}
    (hA : JointlySmoothOn g a b (Icc 0 T) A) (x : M) :
    ContDiffOn ℝ ∞ (fun τ => (A τ).toFun x) (Icc 0 T) := by
  refine contDiffOn_of_differentiableOn_deriv fun m _ t ht => ?_
  exact (hasDerivWithinAt_timeDeriv hT (jointlySmoothOn_timeDerivIter hT hA m) ht x
    |>.differentiableWithinAt).congr
    (fun τ hτ => iteratedDerivWithin_eq_timeDerivIter hT hA x m τ hτ)
    (iteratedDerivWithin_eq_timeDerivIter hT hA x m t ht)

/-- **Time derivatives within `[0,T]` do not depend on `T`** (on the smaller interval). -/
theorem timeDerivIter_eqOn_of_le {T₁ T₂ : ℝ} (h1 : 0 < T₁) (h12 : T₁ ≤ T₂)
    {u : ℝ → SmoothCcTensor g a b} (hu : JointlySmoothOn g a b (Icc 0 T₂) u) :
    ∀ j, EqOn (timeDerivIter T₁ u j) (timeDerivIter T₂ u j) (Icc 0 T₁)
  | 0 => fun _ _ => rfl
  | j + 1 => fun t ht => by
    have hT2 : 0 < T₂ := h1.trans_le h12
    have hsub : Icc (0 : ℝ) T₁ ⊆ Icc 0 T₂ := Icc_subset_Icc_right h12
    have hu1 : JointlySmoothOn g a b (Icc 0 T₁) u := hu.mono (prod_mono subset_rfl hsub)
    have hj2 := jointlySmoothOn_timeDerivIter hT2 hu j
    have hj2' : JointlySmoothOn g a b (Icc 0 T₁) (timeDerivIter T₂ u j) :=
      hj2.mono (prod_mono subset_rfl hsub)
    change timeDeriv T₁ (timeDerivIter T₁ u j) t = timeDeriv T₂ (timeDerivIter T₂ u j) t
    rw [timeDeriv_congr h1 (jointlySmoothOn_timeDerivIter h1 hu1 j) hj2'
      (timeDerivIter_eqOn_of_le h1 h12 hu j) ht]
    exact timeDeriv_eq h1 hj2' ht fun x =>
      (hasDerivWithinAt_timeDeriv hT2 hj2 (hsub ht) x).mono hsub

theorem timeDerivIter_sub {T : ℝ} (hT : 0 < T) {A B : ℝ → SmoothCcTensor g a b}
    (hA : JointlySmoothOn g a b (Icc 0 T) A) (hB : JointlySmoothOn g a b (Icc 0 T) B) (j : ℕ)
    (t : ℝ) :
    timeDerivIter T (fun τ => A τ - B τ) j t = timeDerivIter T A j t - timeDerivIter T B j t := by
  have h : (fun τ => A τ - B τ) = fun τ => A τ + (-1 : ℝ) • B τ := by
    funext τ
    rw [neg_one_smul, sub_eq_add_neg]
  rw [h, timeDerivIter_add hT hA (jointlySmoothOn_smul (-1) hB) j,
    timeDerivIter_smul hT (-1) hB j]
  simp only [neg_one_smul, sub_eq_add_neg]

theorem toFun_sum {ι : Type*} (S : Finset ι) {k : ℕ} (F : ι → SmoothCcTensor g 0 k) (x : M) :
    (∑ i ∈ S, F i).toFun x = ∑ i ∈ S, (F i).toFun x := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Cutoff.toFun_zero]
  | insert i S hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, SmoothCcTensor.toFun_add, Pi.add_apply, ih]

end Families

/-! ### Polynomials in time -/

section Poly

variable {s : ℕ}

/-- The polynomial `t ↦ ∑_{i ≤ N} (t^i / i!) c_i`. -/
def polyOf (c : ℕ → SmoothCcTensor g 0 s) (N : ℕ) (t : ℝ) : SmoothCcTensor g 0 s :=
  ∑ i ∈ Finset.range (N + 1), (t ^ i / (i.factorial : ℝ)) • c i

theorem jointlySmoothOn_polyOf (c : ℕ → SmoothCcTensor g 0 s) (N : ℕ) (S : Set ℝ) :
    JointlySmoothOn g 0 s S (polyOf c N) :=
  jointlySmoothOn_sum _ fun i _ => Cutoff.jointlySmoothOn_fun_smul
    ((contDiff_id.pow i).div_const ((i.factorial : ℝ))).contDiffOn (jointlySmoothOn_const g S (c i))

theorem polyOf_zero (c : ℕ → SmoothCcTensor g 0 s) (N : ℕ) : polyOf c N 0 = c 0 := by
  rw [polyOf, Finset.sum_range_succ']
  simp

theorem polyOf_congr {c c' : ℕ → SmoothCcTensor g 0 s} {N : ℕ} (h : ∀ i ≤ N, c i = c' i) :
    polyOf c N = polyOf c' N := by
  funext t
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [h i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]

theorem polyOf_toFun (c : ℕ → SmoothCcTensor g 0 s) (N : ℕ) (t : ℝ) (x : M) :
    (polyOf c N t).toFun x = ∑ i ∈ Finset.range (N + 1), (t ^ i / (i.factorial : ℝ)) • (c i).toFun x := by
  rw [polyOf, toFun_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [SmoothCcTensor.toFun_smul, Pi.smul_apply]

theorem timeDeriv_polyOf {T : ℝ} (hT : 0 < T) (c : ℕ → SmoothCcTensor g 0 s) (N : ℕ) {t : ℝ}
    (ht : t ∈ Icc 0 T) : timeDeriv T (polyOf c (N + 1)) t = polyOf (fun i => c (i + 1)) N t := by
  refine timeDeriv_eq hT (jointlySmoothOn_polyOf c _ _) ht fun x => ?_
  have hfun : (fun τ => (polyOf c (N + 1) τ).toFun x) = fun τ =>
      ∑ i ∈ Finset.range (N + 1 + 1), (τ ^ i / (i.factorial : ℝ)) • (c i).toFun x := by
    funext τ
    exact polyOf_toFun c (N + 1) τ x
  rw [hfun, polyOf_toFun]
  have hd : HasDerivAt (fun τ => ∑ i ∈ Finset.range (N + 1 + 1),
      (τ ^ i / (i.factorial : ℝ)) • (c i).toFun x)
      (∑ i ∈ Finset.range (N + 1 + 1),
        (((i : ℝ) * t ^ (i - 1)) / (i.factorial : ℝ)) • (c i).toFun x) t := by
    apply HasDerivAt.fun_sum
    intro i _
    exact ((hasDerivAt_pow i t).div_const _).smul_const _
  refine hd.hasDerivWithinAt.congr_deriv ?_
  rw [Finset.sum_range_succ' _ (N + 1)]
  simp only [Nat.cast_zero, zero_mul, zero_div, zero_smul, add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Formal.coeff_arith]

theorem timeDerivIter_polyOf {T : ℝ} (hT : 0 < T) (N : ℕ) :
    ∀ (ℓ : ℕ) (c : ℕ → SmoothCcTensor g 0 s),
      EqOn (timeDerivIter T (polyOf c (N + ℓ)) ℓ) (polyOf (fun i => c (i + ℓ)) N) (Icc 0 T)
  | 0, c => fun t _ => rfl
  | ℓ + 1, c => fun t ht => by
    rw [timeDerivIter_succ']
    have h1 : EqOn (timeDeriv T (polyOf c (N + (ℓ + 1))))
        (polyOf (fun i => c (i + 1)) (N + ℓ)) (Icc 0 T) :=
      fun τ hτ => timeDeriv_polyOf hT c (N + ℓ) hτ
    rw [timeDerivIter_congr hT (jointlySmoothOn_timeDeriv hT (jointlySmoothOn_polyOf c _ _))
      (jointlySmoothOn_polyOf _ _ _) h1 ℓ ht]
    exact timeDerivIter_polyOf hT N ℓ (fun i => c (i + 1)) ht

/-- **The time derivatives at `0` of the polynomial are its coefficients.** -/
theorem timeDerivIter_polyOf_zero {T : ℝ} (hT : 0 < T) (c : ℕ → SmoothCcTensor g 0 s) {N ℓ : ℕ}
    (hℓ : ℓ ≤ N) : timeDerivIter T (polyOf c N) ℓ 0 = c ℓ := by
  obtain ⟨K, rfl⟩ := Nat.exists_eq_add_of_le' hℓ
  rw [timeDerivIter_polyOf hT K ℓ c ⟨le_rfl, hT.le⟩, polyOf_zero, zero_add]

end Poly

end Formal

namespace EquationData

open Formal

variable {s p : ℕ}

private theorem mem_jetBase_self' (r s N : ℕ) (x₀ : M) : x₀ ∈ jetBase (I := I) r s N x₀ :=
  ⟨mem_baseSet_trivializationAt _ _ x₀, mem_iInter.mpr fun _ => mem_baseSet_trivializationAt _ _ x₀⟩

private theorem isOpen_jetBase' (r s N : ℕ) (x₀ : M) : IsOpen (jetBase (I := I) r s N x₀) :=
  (trivAt I M r s x₀).open_baseSet.inter
    (isOpen_iInter_of_finite fun k => (trivAt I M r (s + k) x₀).open_baseSet)

/-! ### Short times with jets in the domain -/

/-- **Jets stay in the domain for a short time**: if the jets of `w(0)` lie in the domain, then so
do the jets of `w(t)` for `t ∈ [0, T₁]`, for some `T₁ > 0` (openness of the domain and compactness
of `M`). -/
theorem exists_time_jets_mem (D : EquationData I M 0 s p) {T : ℝ} (hT : 0 < T)
    {w : ℝ → SmoothCcTensor g 0 s} (hw : JointlySmoothOn g 0 s (Icc 0 T) w)
    (h0 : ∀ x, covJet g 0 s (2 * p) (w 0) x ∈ D.dom 0 x) :
    ∃ T₁, 0 < T₁ ∧ T₁ ≤ T ∧ T₁ ≤ D.T₀ ∧
      ∀ t ∈ Icc (0 : ℝ) T₁, ∀ x, covJet g 0 s (2 * p) (w t) x ∈ D.dom t x := by
  have hloc : ∀ y₀ ∈ (univ : Set M), ∀ᶠ z : ℝ × M in 𝓝 ((0 : ℝ), y₀),
      (z.1 ∈ Icc 0 T → z.1 ≤ D.T₀ → covJet g 0 s (2 * p) (w z.1) z.2 ∈ D.dom z.1 z.2) := by
    intro y₀ _
    obtain ⟨U, hUo, hU⟩ := D.dom_relOpen y₀
    have hB := isOpen_jetBase' (I := I) 0 s (2 * p) y₀
    have hy₀ := mem_jetBase_self' (I := I) 0 s (2 * p) y₀
    set Fc : M × ℝ → ℝ × M × JetModel E 0 s (2 * p) :=
      fun q => (q.2, q.1, trivJet y₀ q.1 (covJet g 0 s (2 * p) (w q.2) q.1)) with hFc
    have hc : ContinuousOn Fc (jetBase (I := I) 0 s (2 * p) y₀ ×ˢ Icc 0 T) :=
      continuousOn_snd.prodMk (continuousOn_fst.prodMk
        (contMDiffOn_trivJet_covJet (N := 2 * p) hw y₀).continuousOn)
    have hin : Fc (y₀, 0) ∈ U := by
      have h : Fc (y₀, 0) ∈ localDom 0 s (2 * p) D.T₀ D.dom y₀ := by
        refine ⟨⟨⟨le_rfl, D.T₀_pos.le⟩, hy₀⟩, ?_⟩
        change jetOfModel 0 s (2 * p) y₀ y₀ (trivJet y₀ y₀ (covJet g 0 s (2 * p) (w 0) y₀)) ∈
          D.dom 0 y₀
        rw [jetOfModel_trivJet hy₀]
        exact h0 y₀
      rw [hU] at h
      exact h.1
    have hev : ∀ᶠ q in 𝓝 (y₀, (0 : ℝ)),
        q ∈ jetBase (I := I) 0 s (2 * p) y₀ ×ˢ Icc 0 T → Fc q ∈ U :=
      eventually_nhdsWithin_iff.mp
        ((hc _ ⟨hy₀, le_rfl, hT.le⟩).preimage_mem_nhdsWithin (hUo.mem_nhds hin))
    have hbase : ∀ᶠ q : M × ℝ in 𝓝 (y₀, (0 : ℝ)), q.1 ∈ jetBase (I := I) 0 s (2 * p) y₀ := by
      filter_upwards [prod_mem_nhds (hB.mem_nhds hy₀) (univ_mem : (univ : Set ℝ) ∈ 𝓝 (0 : ℝ))]
        with q hq
      exact hq.1
    have hsw : Tendsto (Prod.swap : ℝ × M → M × ℝ) (𝓝 ((0 : ℝ), y₀)) (𝓝 (y₀, (0 : ℝ))) :=
      continuous_swap.continuousAt
    filter_upwards [hsw.eventually (hev.and hbase)] with z hz hzT hzT₀
    obtain ⟨hzU, hzB⟩ := hz
    have hzB' : z.2 ∈ jetBase (I := I) 0 s (2 * p) y₀ := hzB
    have hmem : Fc (z.2, z.1) ∈ localDom 0 s (2 * p) D.T₀ D.dom y₀ := by
      rw [hU]
      exact ⟨hzU ⟨hzB', hzT⟩, ⟨hzT.1, hzT₀⟩, hzB'⟩
    have h2 := hmem.2
    change jetOfModel 0 s (2 * p) y₀ z.2 (trivJet y₀ z.2 (covJet g 0 s (2 * p) (w z.1) z.2)) ∈
      D.dom z.1 z.2 at h2
    rwa [jetOfModel_trivJet hzB'] at h2
  have hall := isCompact_univ.eventually_forall_of_forall_eventually
    (P := fun τ y => τ ∈ Icc 0 T → τ ≤ D.T₀ → covJet g 0 s (2 * p) (w τ) y ∈ D.dom τ y) hloc
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hall
  have hm1 : min (ε / 2) (min T D.T₀) ≤ ε / 2 := min_le_left _ _
  have hm2 : min (ε / 2) (min T D.T₀) ≤ T := (min_le_right _ _).trans (min_le_left _ _)
  have hm3 : min (ε / 2) (min T D.T₀) ≤ D.T₀ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨min (ε / 2) (min T D.T₀), lt_min (half_pos hε) (lt_min hT D.T₀_pos), hm2, hm3, ?_⟩
  intro t ht x
  have hdist : dist t 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
    linarith [ht.2]
  exact hball hdist x (mem_univ x) ⟨ht.1, ht.2.trans hm2⟩ (ht.2.trans hm3)

/-! ### The nonlinearity along a family -/

theorem nonlinFamily_spec (D : EquationData I M 0 s p) {T : ℝ} (hTT : T ≤ D.T₀)
    {w : ℝ → SmoothCcTensor g 0 s} (hw : JointlySmoothOn g 0 s (Icc 0 T) w)
    (hdom : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, covJet g 0 s (2 * p) (w t) x ∈ D.dom t x) :
    (∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      (D.nonlinFamily w t).toSection x = D.F t x (covJet g 0 s (2 * p) (w t) x)) ∧
    JointlySmoothOn g 0 s (Icc 0 T) (D.nonlinFamily w) := by
  have h := FibreMap.jointlySmoothOn_fibreApply D.toFibreMap 0 hTT (V := jetFamily (p := p) w)
    (fun k => jointlySmoothOn_iteratedCovGrad hw k) (fun t ht x => hdom t ht x)
  exact ⟨fun t ht x => FibreMap.apply_toSection _ _ _ _ (h.1 t ht) x, h.2⟩

/-- A jet with the given model values. -/
def ofModelJet {N : ℕ} (x : M) (z : JetModel E 0 s N) : CovJetFiber I 0 s N x :=
  fun k => TensorRSSpace.ofModel (z k)

/-- `F(t, ·)` at `x`, on jets given by their model values. -/
def modelF (D : EquationData I M 0 s p) (x : M) (q : ℝ × JetModel E 0 s (2 * p)) :
    TensorRSModel 0 s ℝ E :=
  TensorRSSpace.toModel (D.F q.1 x (ofModelJet x q.2))

/-- The curve `t ↦ (t, (∇^k w(t, x))_k)` in model values. -/
def jetCurve (w : ℝ → SmoothCcTensor g 0 s) (x : M) (τ : ℝ) : ℝ × JetModel E 0 s (2 * p) :=
  (τ, fun k => (iteratedCovGrad g 0 s k (w τ)).toFun x)

theorem ofModelJet_jetCurve (w : ℝ → SmoothCcTensor g 0 s) (x : M) (τ : ℝ) :
    ofModelJet x (jetCurve (p := p) w x τ).2 = covJet g 0 s (2 * p) (w τ) x := by
  funext k
  exact TensorRSSpace.ofModel_toModel _

private theorem toModel_eq_clmAt {a b : ℕ} {x : M} (v : TensorRSSpace a b I x) :
    TensorRSSpace.toModel v =
      ((tensorRSSpaceContinuousLinearEquiv (I := I) a b x).toContinuousLinearMap.comp
        ((trivAt I M a b x).symmL ℝ x)) ((trivAt I M a b x).continuousLinearMapAt ℝ x v) := by
  rw [ContinuousLinearMap.comp_apply,
    Trivialization.symmL_continuousLinearMapAt _ (mem_baseSet_trivializationAt _ _ x)]
  rfl

/-- `modelF` is smooth on a set with unique derivatives containing the domain. -/
theorem exists_modelF_smooth (D : EquationData I M 0 s p) (x : M) :
    ∃ t : Set (ℝ × JetModel E 0 s (2 * p)), UniqueDiffOn ℝ t ∧ ContDiffOn ℝ ∞ (D.modelF x) t ∧
      ∀ τ ∈ Icc (0 : ℝ) D.T₀, ∀ z : JetModel E 0 s (2 * p), ofModelJet x z ∈ D.dom τ x →
        (τ, z) ∈ t := by
  obtain ⟨U, hUo, hU⟩ := D.dom_relOpen x
  let B : JetModel E 0 s (2 * p) →L[ℝ] JetModel E 0 s (2 * p) :=
    ContinuousLinearMap.pi fun k => ((trivAt I M 0 (s + k) x).continuousLinearMapAt ℝ x).comp
      ((tensorRSSpaceContinuousLinearEquiv (I := I) 0 (s + k) x).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.proj k))
  have hx := mem_jetBase_self' (I := I) 0 s (2 * p) x
  have hBj : ∀ z, jetOfModel 0 s (2 * p) x x (B z) = ofModelJet x z := fun z => by
    have hB : B z = trivJet x x (ofModelJet (I := I) x z) := rfl
    rw [hB, jetOfModel_trivJet hx]
  let ψ : ℝ × JetModel E 0 s (2 * p) → ℝ × M × JetModel E 0 s (2 * p) := fun q => (q.1, x, B q.2)
  have hψc : Continuous ψ :=
    continuous_fst.prodMk (continuous_const.prodMk (B.continuous.comp continuous_snd))
  refine ⟨(Icc 0 D.T₀ ×ˢ univ) ∩ ψ ⁻¹' U,
    ((uniqueDiffOn_Icc D.T₀_pos).prod uniqueDiffOn_univ).inter (hUo.preimage hψc), ?_, ?_⟩
  · have hmaps : MapsTo ψ ((Icc 0 D.T₀ ×ˢ univ) ∩ ψ ⁻¹' U) (localDom 0 s (2 * p) D.T₀ D.dom x) := by
      intro q hq
      rw [hU]
      exact ⟨hq.2, hq.1.1, hx⟩
    have hψ : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, JetModel E 0 s (2 * p)))
        (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, JetModel E 0 s (2 * p)))) ∞ ψ :=
      contMDiff_fst.prodMk (contMDiff_const.prodMk (B.contDiff.contMDiff.comp contMDiff_snd))
    have h1 := (D.smooth x).comp hψ.contMDiffOn hmaps
    set A := (tensorRSSpaceContinuousLinearEquiv (I := I) 0 s x).toContinuousLinearMap.comp
      ((trivAt I M 0 s x).symmL ℝ x) with hA
    have h2 := A.contDiff.contMDiff.comp_contMDiffOn h1
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h2
    refine (contMDiffOn_iff_contDiffOn.mp h2).congr fun q _ => ?_
    change TensorRSSpace.toModel (D.F q.1 x (ofModelJet x q.2)) =
      A ((trivAt I M 0 s x).continuousLinearMapAt ℝ x
        (D.F q.1 x (jetOfModel 0 s (2 * p) x x (B q.2))))
    rw [hBj, hA]
    exact toModel_eq_clmAt _
  · intro τ hτ z hz
    refine ⟨⟨hτ, mem_univ _⟩, ?_⟩
    have h : ψ (τ, z) ∈ localDom 0 s (2 * p) D.T₀ D.dom x := by
      refine ⟨⟨hτ, hx⟩, ?_⟩
      change jetOfModel 0 s (2 * p) x x (B z) ∈ D.dom τ x
      rw [hBj]
      exact hz
    rw [hU] at h
    exact h.1

theorem contDiffOn_jetCurve {T : ℝ} (hT : 0 < T) {w : ℝ → SmoothCcTensor g 0 s}
    (hw : JointlySmoothOn g 0 s (Icc 0 T) w) (x : M) :
    ContDiffOn ℝ ∞ (jetCurve (p := p) w x) (Icc 0 T) :=
  contDiffOn_id.prodMk (contDiffOn_pi.mpr fun k =>
    contDiffOn_toFun hT (jointlySmoothOn_iteratedCovGrad hw k) x)

theorem jetCurve_iteratedDerivWithin_fst {T : ℝ} (hT : 0 < T) {w : ℝ → SmoothCcTensor g 0 s}
    (hw : JointlySmoothOn g 0 s (Icc 0 T) w) (x : M) (j : ℕ) :
    (iteratedDerivWithin j (jetCurve (p := p) w x) (Icc 0 T) 0).1 =
      iteratedDerivWithin j (fun τ : ℝ => τ) (Icc 0 T) 0 :=
  clm_iteratedDerivWithin (contDiffOn_jetCurve hT hw x) (uniqueDiffOn_Icc hT) ⟨le_rfl, hT.le⟩
    (ContinuousLinearMap.fst ℝ ℝ (JetModel E 0 s (2 * p))) j

theorem jetCurve_iteratedDerivWithin_snd {T : ℝ} (hT : 0 < T) {w : ℝ → SmoothCcTensor g 0 s}
    (hw : JointlySmoothOn g 0 s (Icc 0 T) w) (x : M) (j : ℕ) (k : Fin (2 * p + 1)) :
    (iteratedDerivWithin j (jetCurve (p := p) w x) (Icc 0 T) 0).2 k =
      (iteratedCovGrad g 0 s k (timeDerivIter T w j 0)).toFun x := by
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  have h := clm_iteratedDerivWithin (contDiffOn_jetCurve hT hw x) (uniqueDiffOn_Icc hT) h0
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun k : Fin (2 * p + 1) =>
      TensorRSModel 0 (s + (k : ℕ)) ℝ E) k).comp
      (ContinuousLinearMap.snd ℝ ℝ (JetModel E 0 s (2 * p)))) j
  calc (iteratedDerivWithin j (jetCurve (p := p) w x) (Icc 0 T) 0).2 k
      = iteratedDerivWithin j (fun τ => (iteratedCovGrad g 0 s k (w τ)).toFun x) (Icc 0 T) 0 := h
    _ = (timeDerivIter T (fun τ => iteratedCovGrad g 0 s k (w τ)) j 0).toFun x :=
        iteratedDerivWithin_eq_timeDerivIter hT (jointlySmoothOn_iteratedCovGrad hw k) x j 0 h0
    _ = (iteratedCovGrad g 0 s k (timeDerivIter T w j 0)).toFun x := by
        rw [timeDerivIter_iteratedCovGrad hT hw k j h0]

/-- **Locality of `F[w]` in time**: the time derivatives of `F[w]` at `0` up to order `n` only
depend on those of `w`. -/
theorem timeDerivIter_nonlinFamily_congr (D : EquationData I M 0 s p) {T : ℝ} (hT : 0 < T)
    (hTT : T ≤ D.T₀) {w w' : ℝ → SmoothCcTensor g 0 s} (hw : JointlySmoothOn g 0 s (Icc 0 T) w)
    (hw' : JointlySmoothOn g 0 s (Icc 0 T) w')
    (hdom : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, covJet g 0 s (2 * p) (w t) x ∈ D.dom t x)
    (hdom' : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, covJet g 0 s (2 * p) (w' t) x ∈ D.dom t x) (n : ℕ)
    (heq : ∀ j ≤ n, timeDerivIter T w j 0 = timeDerivIter T w' j 0) :
    timeDerivIter T (D.nonlinFamily w) n 0 = timeDerivIter T (D.nonlinFamily w') n 0 := by
  obtain ⟨hF1, hF2⟩ := D.nonlinFamily_spec hTT hw hdom
  obtain ⟨hF1', hF2'⟩ := D.nonlinFamily_spec hTT hw' hdom'
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  refine smoothCcTensor_eq_of_toFun fun x => ?_
  rw [← iteratedDerivWithin_eq_timeDerivIter hT hF2 x n 0 h0,
    ← iteratedDerivWithin_eq_timeDerivIter hT hF2' x n 0 h0]
  have hval : ∀ {v : ℝ → SmoothCcTensor g 0 s},
      (∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
        (D.nonlinFamily v t).toSection x = D.F t x (covJet g 0 s (2 * p) (v t) x)) →
      EqOn (fun τ => (D.nonlinFamily v τ).toFun x) (D.modelF x ∘ jetCurve v x) (Icc 0 T) := by
    intro v hv τ hτ
    change TensorRSSpace.toModel ((D.nonlinFamily v τ).toSection x) =
      TensorRSSpace.toModel (D.F τ x (ofModelJet x (jetCurve (p := p) v x τ).2))
    rw [hv τ hτ x, ofModelJet_jetCurve]
  rw [iteratedDerivWithin_congr (hval hF1) h0, iteratedDerivWithin_congr (hval hF1') h0]
  obtain ⟨t, htU, htF, htmem⟩ := D.exists_modelF_smooth x
  have hmaps : ∀ {v : ℝ → SmoothCcTensor g 0 s},
      (∀ t ∈ Icc (0 : ℝ) T, ∀ x, covJet g 0 s (2 * p) (v t) x ∈ D.dom t x) →
      MapsTo (jetCurve (p := p) v x) (Icc 0 T) t := by
    intro v hv τ hτ
    refine htmem τ ⟨hτ.1, hτ.2.trans hTT⟩ (jetCurve (p := p) v x τ).2 ?_
    rw [ofModelJet_jetCurve (p := p)]
    exact hv τ hτ x
  have hcurve : ∀ j ≤ n, iteratedFDerivWithin ℝ j (jetCurve (p := p) w x) (Icc 0 T) 0 =
      iteratedFDerivWithin ℝ j (jetCurve (p := p) w' x) (Icc 0 T) 0 := by
    intro j hj
    refine ContinuousMultilinearMap.ext fun v => ?_
    rw [iteratedFDerivWithin_apply_eq_iteratedDerivWithin_mul_prod,
      iteratedFDerivWithin_apply_eq_iteratedDerivWithin_mul_prod]
    congr 1
    refine Prod.ext ?_ (funext fun k => ?_)
    · rw [jetCurve_iteratedDerivWithin_fst hT hw, jetCurve_iteratedDerivWithin_fst hT hw']
    · rw [jetCurve_iteratedDerivWithin_snd hT hw, jetCurve_iteratedDerivWithin_snd hT hw',
        heq j hj]
  have hle : ((n : ℕ) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have key := iteratedFDerivWithin_comp_congr (htF.of_le hle)
    ((contDiffOn_jetCurve hT hw x).of_le hle) ((contDiffOn_jetCurve hT hw' x).of_le hle)
    htU (uniqueDiffOn_Icc hT) (hmaps hdom) (hmaps hdom') h0 hcurve
  rw [iteratedDerivWithin_eq_iteratedFDerivWithin, iteratedDerivWithin_eq_iteratedFDerivWithin, key]

/-! ### The formal solution -/

open Classical in
/-- The coefficient following `c₀, …, c_ℓ`: the `ℓ`-th time derivative at `0` of `F[w_ℓ]`,
`w_ℓ = ∑_{i ≤ ℓ} t^i/i! c_i`, on an interval where the jets of `w_ℓ` lie in the domain. -/
def nextCoeff (D : EquationData I M 0 s p) (c : ℕ → SmoothCcTensor g 0 s) (ℓ : ℕ) :
    SmoothCcTensor g 0 s :=
  if h : ∃ T : ℝ, 0 < T ∧ T ≤ D.T₀ ∧
      ∀ t ∈ Icc (0 : ℝ) T, ∀ x, covJet g 0 s (2 * p) (polyOf c ℓ t) x ∈ D.dom t x then
    timeDerivIter h.choose (D.nonlinFamily (polyOf c ℓ)) ℓ 0
  else 0

theorem nextCoeff_congr (D : EquationData I M 0 s p) {c c' : ℕ → SmoothCcTensor g 0 s} {ℓ : ℕ}
    (h : ∀ i ≤ ℓ, c i = c' i) : D.nextCoeff c ℓ = D.nextCoeff c' ℓ := by
  rw [nextCoeff, nextCoeff, polyOf_congr h]

/-- **The coefficients `a_ℓ` of the formal solution** (`lem:formal`): `a₀ = u₀`, and `a_{ℓ+1}` is
the `ℓ`-th time derivative at `0` of `F[∑_{i ≤ ℓ} t^i/i! a_i]`. -/
def formalCoeff (D : EquationData I M 0 s p) (g : SmoothRiemannianMetric I M)
    (u₀ : SmoothCcTensor g 0 s) : ℕ → SmoothCcTensor g 0 s
  | 0 => u₀
  | ℓ + 1 => D.nextCoeff (fun i => if h : i ≤ ℓ then D.formalCoeff g u₀ i else 0) ℓ
termination_by ℓ => ℓ
decreasing_by omega

/-- **The truncated formal solution** `t ↦ ∑_{ℓ ≤ N} (t^ℓ/ℓ!) a_ℓ`. -/
def formalPoly (D : EquationData I M 0 s p) (g : SmoothRiemannianMetric I M)
    (u₀ : SmoothCcTensor g 0 s) (N : ℕ) : ℝ → SmoothCcTensor g 0 s :=
  polyOf (D.formalCoeff g u₀) N

variable (D : EquationData I M 0 s p) (u₀ : SmoothCcTensor g 0 s)

@[simp] theorem formalCoeff_zero : D.formalCoeff g u₀ 0 = u₀ := by
  rw [formalCoeff]

theorem formalCoeff_succ (ℓ : ℕ) :
    D.formalCoeff g u₀ (ℓ + 1) = D.nextCoeff (D.formalCoeff g u₀) ℓ := by
  rw [formalCoeff]
  exact D.nextCoeff_congr fun i hi => by rw [dif_pos hi]

theorem formalPoly_zero (N : ℕ) : D.formalPoly g u₀ N 0 = u₀ := by
  rw [formalPoly, polyOf_zero, formalCoeff_zero]

theorem jointlySmoothOn_formalPoly (N : ℕ) (S : Set ℝ) :
    JointlySmoothOn g 0 s S (D.formalPoly g u₀ N) :=
  jointlySmoothOn_polyOf _ N S

/-- The time derivatives at `0` of the truncated formal solution are the coefficients `a_ℓ`. -/
theorem timeDerivIter_formalPoly {T : ℝ} (hT : 0 < T) {N ℓ : ℕ} (hℓ : ℓ ≤ N) :
    timeDerivIter T (D.formalPoly g u₀ N) ℓ 0 = D.formalCoeff g u₀ ℓ :=
  timeDerivIter_polyOf_zero hT _ hℓ

variable {D u₀}

/-- The jets of the truncated formal solution lie in the domain for a short time. -/
theorem exists_formalPoly_dom (h₀ : ∀ x, covJet g 0 s (2 * p) u₀ x ∈ D.dom 0 x) (N : ℕ) :
    ∃ T₁, 0 < T₁ ∧ T₁ ≤ D.T₀ ∧
      ∀ t ∈ Icc (0 : ℝ) T₁, ∀ x, covJet g 0 s (2 * p) (D.formalPoly g u₀ N t) x ∈ D.dom t x := by
  obtain ⟨T₁, h1, -, h3, h4⟩ := D.exists_time_jets_mem D.T₀_pos
    (D.jointlySmoothOn_formalPoly u₀ N _) (fun x => by rw [formalPoly_zero]; exact h₀ x)
  exact ⟨T₁, h1, h3, h4⟩

/-- **`lem:formal`**, derivative form: `∂ₜ^{ℓ+1} w(0) = ∂ₜ^ℓ F[w](0)` for `ℓ < N`. -/
theorem formalCoeff_spec' (h₀ : ∀ x, covJet g 0 s (2 * p) u₀ x ∈ D.dom 0 x) {N : ℕ} {T' : ℝ}
    (hT' : 0 < T') (hTT : T' ≤ D.T₀) {w : ℝ → SmoothCcTensor g 0 s}
    (hw : JointlySmoothOn g 0 s (Icc 0 T') w)
    (hdom : ∀ t ∈ Icc (0 : ℝ) T', ∀ x, covJet g 0 s (2 * p) (w t) x ∈ D.dom t x)
    (hcoeff : ∀ ℓ ≤ N, timeDerivIter T' w ℓ 0 = D.formalCoeff g u₀ ℓ) {ℓ : ℕ} (hℓ : ℓ < N) :
    timeDerivIter T' w (ℓ + 1) 0 = timeDerivIter T' (D.nonlinFamily w) ℓ 0 := by
  have hex : ∃ T : ℝ, 0 < T ∧ T ≤ D.T₀ ∧ ∀ t ∈ Icc (0 : ℝ) T, ∀ x,
      covJet g 0 s (2 * p) (polyOf (D.formalCoeff g u₀) ℓ t) x ∈ D.dom t x :=
    exists_formalPoly_dom (D := D) h₀ ℓ
  rw [hcoeff (ℓ + 1) hℓ, formalCoeff_succ, nextCoeff]
  rw [dif_pos hex]
  obtain ⟨hT1, hT1T₀, hdom1⟩ := hex.choose_spec
  generalize hex.choose = T₁ at hT1 hT1T₀ hdom1 ⊢
  have hT₂ : 0 < min T₁ T' := lt_min hT1 hT'
  have h0₂ : (0 : ℝ) ∈ Icc 0 (min T₁ T') := ⟨le_rfl, hT₂.le⟩
  have hsub1 : Icc (0 : ℝ) (min T₁ T') ⊆ Icc 0 T₁ := Icc_subset_Icc_right (min_le_left _ _)
  have hsub2 : Icc (0 : ℝ) (min T₁ T') ⊆ Icc 0 T' := Icc_subset_Icc_right (min_le_right _ _)
  have hP := jointlySmoothOn_polyOf (D.formalCoeff g u₀) ℓ (Icc 0 T₁)
  have hFP := (D.nonlinFamily_spec hT1T₀ hP hdom1).2
  have hFw := (D.nonlinFamily_spec hTT hw hdom).2
  rw [← timeDerivIter_eqOn_of_le hT₂ (min_le_left _ _) hFP ℓ h0₂,
    ← timeDerivIter_eqOn_of_le hT₂ (min_le_right _ _) hFw ℓ h0₂]
  refine D.timeDerivIter_nonlinFamily_congr hT₂ ((min_le_left _ _).trans hT1T₀)
    (hP.mono (prod_mono subset_rfl hsub1)) (hw.mono (prod_mono subset_rfl hsub2))
    (fun t ht => hdom1 t (hsub1 ht)) (fun t ht => hdom t (hsub2 ht)) ℓ fun j hj => ?_
  rw [timeDerivIter_eqOn_of_le hT₂ (min_le_left _ _) hP j h0₂,
    timeDerivIter_eqOn_of_le hT₂ (min_le_right _ _) hw j h0₂,
    timeDerivIter_polyOf_zero hT1 _ hj, hcoeff j (by omega)]

/-- **`lem:formal`** (formal solution): if `w` is smooth on `M × [0,T']` with jets in the domain
and `∂ₜ^ℓ w(0) = a_ℓ` for `ℓ ≤ N`, then `∂ₜ^ℓ (∂ₜ w - F[w])(0) = 0` for `ℓ < N`. -/
theorem formalCoeff_spec (h₀ : ∀ x, covJet g 0 s (2 * p) u₀ x ∈ D.dom 0 x) {N : ℕ} {T' : ℝ}
    (hT' : 0 < T') (hTT : T' ≤ D.T₀) {w : ℝ → SmoothCcTensor g 0 s}
    (hw : JointlySmoothOn g 0 s (Icc 0 T') w)
    (hdom : ∀ t ∈ Icc (0 : ℝ) T', ∀ x, covJet g 0 s (2 * p) (w t) x ∈ D.dom t x)
    (hcoeff : ∀ ℓ ≤ N, timeDerivIter T' w ℓ 0 = D.formalCoeff g u₀ ℓ) {ℓ : ℕ} (hℓ : ℓ < N) :
    timeDerivIter T' (fun t => timeDeriv T' w t - D.nonlinFamily w t) ℓ 0 = 0 := by
  rw [timeDerivIter_sub hT' (jointlySmoothOn_timeDeriv hT' hw)
    (D.nonlinFamily_spec hTT hw hdom).2 ℓ 0, ← timeDerivIter_succ',
    formalCoeff_spec' h₀ hT' hTT hw hdom hcoeff hℓ, sub_self]

end EquationData

end ShortTime
