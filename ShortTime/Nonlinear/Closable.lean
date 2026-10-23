import ShortTime.Nonlinear.ClosablePair

/-!
# Closability: an element of `𝒫^m` is determined by its continuous representative

For `m ≥ 1` and `n/2 + 1 ≤ 2p(m - 1)`, the evaluation `evalJet 0 0 t x` (the continuous
representative of `v ∈ 𝒫^m`, `Evaluation.lean`) is injective on `𝒫^m`
(`ParabolicSpace.eq_zero_of_evalJet_eq_zero`). Hence an element of `𝒫^m` whose continuous
representative is a jointly smooth family `u` is `ofSmooth u` (`ParabolicSpace.eq_ofSmooth_of_evalJet_eq`).

Proof. The jet maps `u ↦ ∇^i ∂ₜ^j u` extend to bounded maps `jetExt j i : 𝒫^m → 𝒫^0` (for
`2pj + i ≤ 2pm`), where `𝒫^0` (rank `s + i`) is the completion of the smooth families under
`∫₀ᵀ ‖·‖²_{L²}`, and `‖v‖²_{𝒫^m} = Σ_{j,i} ‖jetExt j i v‖²_{𝒫^0}` (`norm_sq_eq_sum_jetExt`). We show
`jetExt j i v = 0` by induction:
* `(0,0)`: the smooth approximants `u` satisfy `|u(t,x)|² = |evalJet (u - v)|² ≤ C ‖u - v‖²`, so
  `‖jetExt 0 0 v‖ ≤ (1 + √(C T vol M)) ‖v - u‖` (`jetExt_zero_zero_eq_zero`).
* `(j, i) → (j, i+1)`: `⟨jetExt j (i+1) v, Ψ⟩ = -⟨jetExt j i v, div Ψ⟩` for smooth `Ψ`
  (`inner_jetExt_space`), and the smooth families are dense in `𝒫^0`.
* `(j, i) → (j+1, i)`: `⟨jetExt (j+1) i v, ψ⟩ = -⟨jetExt j i v, ∂ₜψ⟩` for smooth `ψ` with
  `ψ(0) = ψ(T) = 0` (`inner_jetExt_time`), and these are dense in `𝒫^0` (cutoff `bump`,
  `eq_zero_of_inner_vanishing`).
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral DifferentialGeometry.Analysis.Elliptic
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

namespace ParabolicSpace

open Closable

variable {s p m : ℕ} {T : ℝ}

theorem inner_sq_le_aux {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (x y : V) :
    inner ℝ x y ^ 2 ≤ ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
  have h1 := abs_real_inner_le_norm x y
  calc inner ℝ x y ^ 2 = |inner ℝ x y| ^ 2 := (sq_abs _).symm
    _ ≤ (‖x‖ * ‖y‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
    _ = ‖x‖ ^ 2 * ‖y‖ ^ 2 := by ring

theorem mixedInner_le_parabolicInner_of_mem {u : ℝ → SmoothCcTensor g 0 s} {j i : ℕ} (hj : j ≤ m)
    (hi : i ≤ 2 * p * (m - j)) :
    mixedInner g s T u u j i ≤ parabolicInner g s p m T u u := by
  unfold parabolicInner
  refine le_trans ?_ (Finset.single_le_sum
    (f := fun j => ∑ i ∈ Finset.range (2 * p * (m - j) + 1), mixedInner g s T u u j i)
    (fun j _ => Finset.sum_nonneg fun i _ => mixedInner_self_nonneg _ j i)
    (Finset.mem_range.mpr (show j < m + 1 by omega)))
  exact Finset.single_le_sum (f := fun i => mixedInner g s T u u j i)
    (fun i _ => mixedInner_self_nonneg _ j i)
    (Finset.mem_range.mpr (show i < 2 * p * (m - j) + 1 by omega))

/-! ### The jet maps `𝒫^m → 𝒫^0` -/

theorem family_smooth {a q n : ℕ} (u : ParabolicPre g a q n T) :
    JointlySmoothOn g 0 a (Icc 0 T) u.family := u.2

variable (g s p m T) in
/-- `u ↦ ∇^i ∂ₜ^j u` on smooth families, into the smooth families of rank `s + i`, with the
`𝒫^0` norm. -/
def jetPre (hT : 0 < T) (j i : ℕ) : ParabolicPre g s p m T →ₗ[ℝ] ParabolicPre g (s + i) p 0 T where
  toFun u := ParabolicPre.mk (jetFam T j i u.family) (jointlySmoothOn_jetFam hT (family_smooth u) j i)
  map_add' u v := Subtype.ext (funext fun t => by
    change iteratedCovGrad g 0 s i (timeDerivIter T (fun τ => u.family τ + v.family τ) j t) =
      iteratedCovGrad g 0 s i (timeDerivIter T u.family j t) +
        iteratedCovGrad g 0 s i (timeDerivIter T v.family j t)
    rw [timeDerivIter_add_apply (family_smooth u) (family_smooth v), Analysis.Spectral.iteratedCovGrad_add])
  map_smul' c u := Subtype.ext (funext fun t => by
    change iteratedCovGrad g 0 s i (timeDerivIter T (fun τ => c • u.family τ) j t) =
      c • iteratedCovGrad g 0 s i (timeDerivIter T u.family j t)
    rw [timeDerivIter_smul_apply c (family_smooth u), Analysis.Spectral.iteratedCovGrad_smul])

theorem jetPre_family (hT : 0 < T) (j i : ℕ) (u : ParabolicPre g s p m T) :
    (jetPre g s p m T hT j i u).family = jetFam T j i u.family := rfl

theorem norm_jetPre_sq (hT : 0 < T) (j i : ℕ) (u : ParabolicPre g s p m T) :
    ‖jetPre g s p m T hT j i u‖ ^ 2 = mixedInner g s T u.family u.family j i := by
  rw [ParabolicPre.norm_sq_eq, jetPre_family,
    parabolicInner_zero_eq hT (jointlySmoothOn_jetFam hT (family_smooth u) j i) (jointlySmoothOn_jetFam hT (family_smooth u) j i),
    mixedInner_eq_pair hT (family_smooth u) (family_smooth u)]

theorem norm_jetPre_le (hT : 0 < T) {j i : ℕ} (hj : j ≤ m) (hi : i ≤ 2 * p * (m - j))
    (u : ParabolicPre g s p m T) : ‖jetPre g s p m T hT j i u‖ ≤ ‖u‖ := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp ?_
  rw [norm_jetPre_sq, ParabolicPre.norm_sq_eq]
  exact mixedInner_le_parabolicInner_of_mem hj hi

variable (g s p m T) in
/-- **The jet map `∇^i ∂ₜ^j : 𝒫^m → 𝒫^0`** (meaningful for `2pj + i ≤ 2pm`): the continuous
extension of `jetPre`. -/
def jetExt (hT : 0 < T) (j i : ℕ) : ParabolicSpace g s p m T →L[ℝ] ParabolicSpace g (s + i) p 0 T :=
  ((UniformSpace.Completion.toComplL (𝕜 := ℝ) (E := ParabolicPre g (s + i) p 0 T)).toLinearMap ∘ₗ
    jetPre g s p m T hT j i).extendOfNorm
    (UniformSpace.Completion.toComplL (𝕜 := ℝ) (E := ParabolicPre g s p m T)).toLinearMap

theorem jetExt_coe (hT : 0 < T) {j i : ℕ} (hj : j ≤ m) (hi : i ≤ 2 * p * (m - j))
    (u : ParabolicPre g s p m T) :
    jetExt g s p m T hT j i (u : ParabolicSpace g s p m T) =
      ((jetPre g s p m T hT j i u : ParabolicPre g (s + i) p 0 T) :
        ParabolicSpace g (s + i) p 0 T) :=
  LinearMap.extendOfNorm_eq denseRange_toComplL ⟨1, fun u => by
    rw [norm_toComplL, one_mul]
    exact (norm_toComplL _).trans_le (norm_jetPre_le hT hj hi u)⟩ u

theorem norm_jetExt_le (hT : 0 < T) {j i : ℕ} (hj : j ≤ m) (hi : i ≤ 2 * p * (m - j))
    (v : ParabolicSpace g s p m T) : ‖jetExt g s p m T hT j i v‖ ≤ ‖v‖ := by
  have h := LinearMap.norm_extendOfNorm_apply_le
    (f := (UniformSpace.Completion.toComplL (𝕜 := ℝ) (E := ParabolicPre g (s + i) p 0 T)).toLinearMap ∘ₗ
      jetPre g s p m T hT j i) denseRange_toComplL 1 (fun u => by
        rw [norm_toComplL, one_mul]
        exact (norm_toComplL _).trans_le (norm_jetPre_le hT hj hi u)) v
  rwa [one_mul] at h

/-- **`‖v‖²_{𝒫^m} = Σ_{2pj+i ≤ 2pm} ‖∇^i ∂ₜ^j v‖²_{𝒫^0}`.** -/
theorem norm_sq_eq_sum_jetExt (hT : 0 < T) (v : ParabolicSpace g s p m T) :
    ‖v‖ ^ 2 = ∑ j ∈ Finset.range (m + 1), ∑ i ∈ Finset.range (2 * p * (m - j) + 1),
      ‖jetExt g s p m T hT j i v‖ ^ 2 := by
  refine UniformSpace.Completion.induction_on v (isClosed_eq (continuous_norm.pow 2)
    (continuous_finset_sum _ fun j _ => continuous_finset_sum _ fun i _ =>
      (jetExt g s p m T hT j i).continuous.norm.pow 2)) fun u => ?_
  rw [UniformSpace.Completion.norm_coe, ParabolicPre.norm_sq_eq]
  unfold parabolicInner
  refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun i hi => ?_
  have hj' := Finset.mem_range.mp hj
  have hi' := Finset.mem_range.mp hi
  rw [jetExt_coe hT (by omega) (by omega), UniformSpace.Completion.norm_coe, norm_jetPre_sq]

/-- An element all of whose jets vanish is `0`. -/
theorem eq_zero_of_jetExt (hT : 0 < T) {v : ParabolicSpace g s p m T}
    (h : ∀ j i, j ≤ m → i ≤ 2 * p * (m - j) → jetExt g s p m T hT j i v = 0) : v = 0 := by
  have hn := norm_sq_eq_sum_jetExt hT v
  have hz : ∑ j ∈ Finset.range (m + 1), ∑ i ∈ Finset.range (2 * p * (m - j) + 1),
      ‖jetExt g s p m T hT j i v‖ ^ 2 = 0 :=
    Finset.sum_eq_zero fun j hj => Finset.sum_eq_zero fun i hi => by
      have hj' := Finset.mem_range.mp hj
      have hi' := Finset.mem_range.mp hi
      rw [h j i (by omega) (by omega), norm_zero]
      norm_num
  rw [hz] at hn
  exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hn)

/-! ### Pairings with smooth test families in `𝒫^0` -/

theorem inner_coe_ofSmooth {a : ℕ} (u : ParabolicPre g a p 0 T) {ψ : ℝ → SmoothCcTensor g 0 a}
    (hψ : JointlySmoothOn g 0 a (Icc 0 T) ψ) :
    inner ℝ (u : ParabolicSpace g a p 0 T) (ofSmooth ψ hψ) = parabolicInner g a p 0 T u.family ψ := by
  unfold ofSmooth
  exact UniformSpace.Completion.inner_coe _ _

/-- The smooth families are dense in `𝒫^0`: an element orthogonal to all of them is `0`. -/
theorem eq_zero_of_inner_ofSmooth {a : ℕ} (w : ParabolicSpace g a p 0 T)
    (h : ∀ ψ (hψ : JointlySmoothOn g 0 a (Icc 0 T) ψ), inner ℝ w (ofSmooth ψ hψ) = 0) : w = 0 := by
  have h' : ∀ z : ParabolicSpace g a p 0 T, inner ℝ w z = 0 := fun z =>
    UniformSpace.Completion.induction_on z
      (isClosed_eq (continuous_const.inner continuous_id) continuous_const) fun u => h u.family u.2
  exact inner_self_eq_zero.mp (h' w)

/-- The smooth families vanishing at `t = 0` and `t = T` are dense in `𝒫^0`. -/
theorem eq_zero_of_inner_vanishing (hT : 0 < T) {a : ℕ} (w : ParabolicSpace g a p 0 T)
    (h : ∀ ψ (hψ : JointlySmoothOn g 0 a (Icc 0 T) ψ), ψ 0 = 0 → ψ T = 0 →
      inner ℝ w (ofSmooth ψ hψ) = 0) : w = 0 := by
  refine eq_zero_of_inner_ofSmooth w fun f hf => ?_
  obtain ⟨C, hC⟩ := exists_pair_cutoff_le hT hf
  have key : ∀ δ : ℝ, 0 < δ → δ < T / 2 →
      inner ℝ w (ofSmooth (p := p) (m := 0) f hf) ^ 2 ≤ (‖w‖ ^ 2 * C) * δ := by
    intro δ hδ hδT
    have hφ := jointlySmoothOn_bump_smul hf δ
    have hη := jointlySmoothOn_one_sub_bump_smul hf δ
    have e : ofSmooth (p := p) (m := 0) f hf =
        ofSmooth (fun t => bump T δ t • f t) hφ +
          ofSmooth (fun t => (1 - bump T δ t) • f t) hη := by
      unfold ofSmooth
      rw [← UniformSpace.Completion.coe_add]
      congr 1
      exact Subtype.ext (funext fun t => by
        change f t = bump T δ t • f t + (1 - bump T δ t) • f t
        rw [← add_smul, add_sub_cancel, one_smul])
    have hz0 : (fun t => bump T δ t • f t) 0 = 0 := by
      change bump T δ 0 • f 0 = 0
      rw [bump_zero, zero_smul]
    have hzT : (fun t => bump T δ t • f t) T = 0 := by
      change bump T δ T • f T = 0
      rw [bump_self, zero_smul]
    rw [e, inner_add_right, h _ hφ hz0 hzT, zero_add]
    have h2 : ‖ofSmooth (p := p) (m := 0) (fun t => (1 - bump T δ t) • f t) hη‖ ^ 2 ≤ C * δ := by
      rw [norm_ofSmooth_sq, parabolicInner_zero_eq hT hη hη]
      exact hC δ hδ (by linarith)
    refine (inner_sq_le_aux _ _).trans ?_
    calc ‖w‖ ^ 2 * ‖ofSmooth (p := p) (m := 0) (fun t => (1 - bump T δ t) • f t) hη‖ ^ 2
        ≤ ‖w‖ ^ 2 * (C * δ) := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      _ = (‖w‖ ^ 2 * C) * δ := by ring
  have h3 := le_zero_of_forall_le_mul (half_pos hT) key
  exact pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm h3 (sq_nonneg _))

/-! ### Weak derivative identities for the jets of `v ∈ 𝒫^m` -/

/-- **Time step**: `⟨∇^i ∂ₜ^{j+1} v, ψ⟩ = -⟨∇^i ∂ₜ^j v, ∂ₜψ⟩` for `ψ(0) = ψ(T) = 0`. -/
theorem inner_jetExt_time (hT : 0 < T) {j i : ℕ} (hj : j + 1 ≤ m)
    (hi : i ≤ 2 * p * (m - (j + 1))) {ψ : ℝ → SmoothCcTensor g 0 (s + i)}
    (hψ : JointlySmoothOn g 0 (s + i) (Icc 0 T) ψ) (h0 : ψ 0 = 0) (hTz : ψ T = 0)
    (v : ParabolicSpace g s p m T) :
    inner ℝ (jetExt g s p m T hT (j + 1) i v) (ofSmooth (p := p) (m := 0) ψ hψ) =
      - inner ℝ (jetExt g s p m T hT j i v)
        (ofSmooth (p := p) (m := 0) (timeDeriv T ψ) (jointlySmoothOn_timeDeriv hT hψ)) := by
  have hi' : i ≤ 2 * p * (m - j) := hi.trans (Nat.mul_le_mul_left _ (by omega))
  refine UniformSpace.Completion.induction_on v
    (isClosed_eq ((jetExt g s p m T hT (j + 1) i).continuous.inner continuous_const)
      ((jetExt g s p m T hT j i).continuous.inner continuous_const).neg) fun u => ?_
  rw [jetExt_coe hT hj hi, jetExt_coe hT (by omega) hi', inner_coe_ofSmooth, inner_coe_ofSmooth,
    jetPre_family, jetPre_family,
    parabolicInner_zero_eq hT (jointlySmoothOn_jetFam hT (family_smooth u) _ _) hψ,
    parabolicInner_zero_eq hT (jointlySmoothOn_jetFam hT (family_smooth u) _ _) (jointlySmoothOn_timeDeriv hT hψ),
    pair_congr_left (jetFam_succ_time hT (family_smooth u) j i)]
  exact pair_timeDeriv hT (jointlySmoothOn_jetFam hT (family_smooth u) j i) hψ h0 hTz

/-- **Space step**: `⟨∇^{i+1} ∂ₜ^j v, Ψ⟩ = -⟨∇^i ∂ₜ^j v, div Ψ⟩`. -/
theorem inner_jetExt_space (hT : 0 < T) {j i : ℕ} (hj : j ≤ m) (hi : i + 1 ≤ 2 * p * (m - j))
    {Ψ : ℝ → SmoothCcTensor g 0 (s + i + 1)} (hΨ : JointlySmoothOn g 0 (s + i + 1) (Icc 0 T) Ψ)
    (v : ParabolicSpace g s p m T) :
    inner ℝ (jetExt g s p m T hT j (i + 1) v) (ofSmooth (p := p) (m := 0) Ψ hΨ) =
      - inner ℝ (jetExt g s p m T hT j i v)
        (ofSmooth (p := p) (m := 0) (fun t => covDivergence (I := I) (M := M) g (s + i) (Ψ t))
          (jointlySmoothOn_covDivergence hΨ)) := by
  refine UniformSpace.Completion.induction_on v
    (isClosed_eq ((jetExt g s p m T hT j (i + 1)).continuous.inner continuous_const)
      ((jetExt g s p m T hT j i).continuous.inner continuous_const).neg) fun u => ?_
  rw [jetExt_coe hT hj hi, jetExt_coe hT hj (by omega), inner_coe_ofSmooth, inner_coe_ofSmooth,
    jetPre_family, jetPre_family,
    parabolicInner_zero_eq hT (jointlySmoothOn_jetFam hT (family_smooth u) _ _) hΨ,
    parabolicInner_zero_eq hT (jointlySmoothOn_jetFam hT (family_smooth u) _ _) (jointlySmoothOn_covDivergence hΨ)]
  exact pair_covGrad (jetFam T j i u.family) Ψ

/-! ### The base case: the `L²` class is determined by the continuous representative -/

theorem jetExt_zero_zero_eq_zero (hT : 0 < T) (hm : 1 ≤ m)
    (hk : Module.finrank ℝ E / 2 + 1 ≤ 2 * p * (m - 1)) (v : ParabolicSpace g s p m T)
    (h : ∀ t ∈ Icc 0 T, ∀ x, evalJet g s p m T 0 0 t x v = 0) :
    jetExt g s p m T hT 0 0 v = 0 := by
  have hm0 : 0 < m := hm
  have hk0 : Module.finrank ℝ E / 2 + 1 + 0 ≤ 2 * p * (m - 0 - 1) := by
    rw [add_zero, Nat.sub_zero]; exact hk
  obtain ⟨C, hC0, hC⟩ := exists_fiberNormSq_evalJet_le (g := g) (s := s) (p := p) hT hm0 hk0
  have hvol : 0 ≤ (riemannianVolumeMeasure (I := I) (M := M) g).real univ := measureReal_nonneg
  have hK : 0 ≤ C * (T * (riemannianVolumeMeasure (I := I) (M := M) g).real univ) :=
    mul_nonneg hC0 (mul_nonneg hT.le hvol)
  have hpre : ∀ u : ParabolicPre g s p m T, ‖jetPre g s p m T hT 0 0 u‖ ≤
      √(C * (T * (riemannianVolumeMeasure (I := I) (M := M) g).real univ)) *
        ‖v - (u : ParabolicSpace g s p m T)‖ := by
    intro u
    refine le_sqrt_mul_of_sq (norm_nonneg _) (norm_nonneg _) hK ?_
    rw [norm_jetPre_sq]
    have hjet : ∀ t ∈ Icc 0 T, ∀ x, jetSq g T u.family 0 0 t x ≤
        C * ‖v - (u : ParabolicSpace g s p m T)‖ ^ 2 := by
      intro t ht x
      have h1 := hC t ht x ((u : ParabolicSpace g s p m T) - v)
      rw [map_sub, h t ht x, sub_zero, evalJet_coe hT hm0 hk0 ht x u, evalPre_apply,
        TensorRSSpace.ofModel_toModel, norm_sub_rev] at h1
      exact h1
    have h2 := mixedInner_le_of_jetSq_le (p := p) (N := 0) (ι := Fin 0) (b := fun _ => 0)
      (V := fun _ _ => 0) (C := C * ‖v - (u : ParabolicSpace g s p m T)‖ ^ 2) (j := 0) (i := 0)
      hT (family_smooth u) (fun c => c.elim0) (fun t ht x => by
        simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, mul_one]
        exact hjet t ht x)
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero] at h2
    refine h2.trans_eq ?_
    ring
  have hbound : ∀ u : ParabolicPre g s p m T, ‖jetExt g s p m T hT 0 0 v‖ ≤
      (1 + √(C * (T * (riemannianVolumeMeasure (I := I) (M := M) g).real univ))) *
        ‖v - (u : ParabolicSpace g s p m T)‖ := by
    intro u
    have e : jetExt g s p m T hT 0 0 v = jetExt g s p m T hT 0 0 (v - (u : ParabolicSpace g s p m T)) +
        ((jetPre g s p m T hT 0 0 u : ParabolicPre g (s + 0) p 0 T) :
          ParabolicSpace g (s + 0) p 0 T) := by
      rw [map_sub, jetExt_coe hT (Nat.zero_le _) (Nat.zero_le _) u, sub_add_cancel]
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [UniformSpace.Completion.norm_coe]
    have h1 := norm_jetExt_le hT (Nat.zero_le m) (Nat.zero_le (2 * p * (m - 0)))
      (v - (u : ParabolicSpace g s p m T))
    have h2 := hpre u
    linarith
  have h3 : ‖jetExt g s p m T hT 0 0 v‖ ≤ 0 := by
    refine le_zero_of_forall_le_mul (K := 1 + √(C * (T *
      (riemannianVolumeMeasure (I := I) (M := M) g).real univ))) one_pos fun δ hδ _ => ?_
    obtain ⟨u, hu⟩ :=
      (UniformSpace.Completion.denseRange_coe (α := ParabolicPre g s p m T)).exists_dist_lt v hδ
    rw [dist_eq_norm] at hu
    exact (hbound u).trans (mul_le_mul_of_nonneg_left hu.le (by positivity))
  exact norm_le_zero_iff.mp h3

/-! ### The main theorem -/

/-- **Closability** (`lem:embedding`): for `m ≥ 1` and `n/2 + 1 ≤ 2p(m-1)`, an element of `𝒫^m`
whose continuous representative vanishes on `[0,T] × M` is `0`. -/
theorem eq_zero_of_evalJet_eq_zero (hT : 0 < T) (hm : 1 ≤ m)
    (hk : Module.finrank ℝ E / 2 + 1 ≤ 2 * p * (m - 1)) (v : ParabolicSpace g s p m T)
    (h : ∀ t ∈ Icc 0 T, ∀ x, evalJet g s p m T 0 0 t x v = 0) : v = 0 := by
  have h00 := jetExt_zero_zero_eq_zero hT hm hk v h
  have hsp : ∀ j i, j ≤ m → i + 1 ≤ 2 * p * (m - j) → jetExt g s p m T hT j i v = 0 →
      jetExt g s p m T hT j (i + 1) v = 0 := by
    intro j i hj hi hz
    refine eq_zero_of_inner_ofSmooth _ fun Ψ hΨ => ?_
    rw [inner_jetExt_space hT hj hi hΨ v, hz, inner_zero_left, neg_zero]
  have htm : ∀ j i, j + 1 ≤ m → i ≤ 2 * p * (m - (j + 1)) → jetExt g s p m T hT j i v = 0 →
      jetExt g s p m T hT (j + 1) i v = 0 := by
    intro j i hj hi hz
    refine eq_zero_of_inner_vanishing hT _ fun ψ hψ h0 hTz => ?_
    rw [inner_jetExt_time hT hj hi hψ h0 hTz v, hz, inner_zero_left, neg_zero]
  have h0i : ∀ i, i ≤ 2 * p * m → jetExt g s p m T hT 0 i v = 0 := by
    intro i
    induction i with
    | zero => intro _; exact h00
    | succ i ih =>
      intro hi
      exact hsp 0 i (Nat.zero_le _) (by rw [Nat.sub_zero]; exact hi) (ih (by omega))
  have hall : ∀ j, j ≤ m → ∀ i, i ≤ 2 * p * (m - j) → jetExt g s p m T hT j i v = 0 := by
    intro j
    induction j with
    | zero => intro _ i hi; exact h0i i (by rw [Nat.sub_zero] at hi; exact hi)
    | succ j ih =>
      intro hj i hi
      have hi' : i ≤ 2 * p * (m - j) := hi.trans (Nat.mul_le_mul_left _ (by omega))
      exact htm j i hj hi (ih (by omega) i hi')
  exact eq_zero_of_jetExt hT fun j i hj hi => hall j hj i hi

/-- **An element of `𝒫^m` with a smooth continuous representative is that smooth family.** If
`evalJet 0 0 t x v = u(t, x)` on `[0,T] × M` for a jointly smooth `u`, then `v = ofSmooth u`. -/
theorem eq_ofSmooth_of_evalJet_eq (hT : 0 < T) (hm : 1 ≤ m)
    (hk : Module.finrank ℝ E / 2 + 1 ≤ 2 * p * (m - 1)) (v : ParabolicSpace g s p m T)
    {u : ℝ → SmoothCcTensor g 0 s} (hu : JointlySmoothOn g 0 s (Icc 0 T) u)
    (h : ∀ t ∈ Icc 0 T, ∀ x, evalJet g s p m T 0 0 t x v = TensorRSSpace.toModel ((u t).toSection x)) :
    v = ofSmooth u hu := by
  have hk0 : Module.finrank ℝ E / 2 + 1 + 0 ≤ 2 * p * (m - 0 - 1) := by
    rw [add_zero, Nat.sub_zero]; exact hk
  refine sub_eq_zero.mp (eq_zero_of_evalJet_eq_zero hT hm hk _ fun t ht x => ?_)
  rw [map_sub, h t ht x, evalJet_ofSmooth hT hm hk0 ht x hu]
  exact sub_self _

end ParabolicSpace

end ShortTime
