import ShortTime.Nonlinear.FlowsParabolicBound
import ShortTime.Nonlinear.Existence

/-!
# The horizontal pullback on the parabolic spaces

Paper: Lemma `lem:flows` (a), (b), in `𝒫`-form.

* `hpullExt σ : 𝒫^m →L 𝒫^m`, the continuous extension of `u ↦ Π_σ u` from smooth families
  (`hpullExt_ofSmooth`), with norms uniformly bounded on `|σ| ≤ R` (`exists_norm_hpullExt_le`).
  It preserves `𝒫^m_0` (`hpullExt_mem_zeroAtStart`), `hpullExt 0 = id`, and
  `hpullExt σ ∘ hpullExt τ = hpullExt (σ + τ)`.
* `contDiff_hpullExt_ofSmooth`: for smooth `u`, `σ ↦ Π_σ u` is `C^∞` into `𝒫^m`, with derivative
  `Π_σ ∇_X u` (`hasDerivAt_hpullExt_ofSmooth`).
* `continuous_hpullExt_apply`: for every `v ∈ 𝒫^m`, `σ ↦ Π_σ v` is continuous.
* `hpullExt_comp_timeDerivExt`: `Π_σ ∘ ∂ₜ = ∂ₜ ∘ Π_σ`.
-/

noncomputable section

open Bundle Manifold Set Filter
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2
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

variable (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
variable (g : SmoothRiemannianMetric I M) (s : ℕ)
variable {p m : ℕ} {T : ℝ}

open ParabolicSpace

theorem ofSmooth_eq_of_eq {u v : ℝ → SmoothCcTensor g 0 s} (h : u = v)
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u) (hv : JointlySmoothOn g 0 s (Icc 0 T) v) :
    ofSmooth (p := p) (m := m) u hu = ofSmooth v hv := by
  subst h; rfl

/-- `Π_σ` on smooth families. -/
def hpullPre (σ : ℝ) : ParabolicPre g s p m T →ₗ[ℝ] ParabolicPre g s p m T where
  toFun u := ⟨fun t => hpull X g s σ (u.family t), jointlySmoothOn_hpull X g s σ u.2⟩
  map_add' u v := Subtype.ext (funext fun t => hpull_add X g s σ (u.family t) (v.family t))
  map_smul' c u := Subtype.ext (funext fun t => hpull_smul X g s σ c (u.family t))

theorem hpullPre_family (σ : ℝ) (u : ParabolicPre g s p m T) :
    (hpullPre X g s σ u).family = fun t => hpull X g s σ (u.family t) := rfl

theorem norm_hpullPre_le (hT : 0 < T) (R : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ σ : ℝ, |σ| ≤ R → ∀ u : ParabolicPre g s p m T,
      ‖hpullPre X g s σ u‖ ≤ C * ‖u‖ := by
  obtain ⟨C, hC0, hC⟩ := exists_parabolicInner_hpull_le X g s hT p m R
  refine ⟨Real.sqrt C, Real.sqrt_nonneg _, fun σ hσ u => ?_⟩
  have h1 : ‖hpullPre X g s σ u‖ ^ 2 ≤ C * ‖u‖ ^ 2 := by
    rw [ParabolicPre.norm_sq_eq, ParabolicPre.norm_sq_eq, hpullPre_family]
    exact hC σ hσ u.2
  have h2 := Real.le_sqrt_of_sq_le h1
  rwa [Real.sqrt_mul hC0, Real.sqrt_sq (norm_nonneg _)] at h2

variable (p m T) in
/-- **The horizontal pullback `Π_σ : 𝒫^m → 𝒫^m`**, the continuous extension of `u ↦ Π_σ u`. -/
def hpullExt (σ : ℝ) : ParabolicSpace g s p m T →L[ℝ] ParabolicSpace g s p m T :=
  ((UniformSpace.Completion.toComplL (𝕜 := ℝ) (E := ParabolicPre g s p m T)).toLinearMap ∘ₗ
    hpullPre X g s σ).extendOfNorm
    (UniformSpace.Completion.toComplL (𝕜 := ℝ) (E := ParabolicPre g s p m T)).toLinearMap

theorem hpullExt_coe (hT : 0 < T) (σ : ℝ) (u : ParabolicPre g s p m T) :
    hpullExt X g s p m T σ (u : ParabolicSpace g s p m T) =
      ((hpullPre X g s σ u : ParabolicPre g s p m T) : ParabolicSpace g s p m T) := by
  obtain ⟨C, -, hC⟩ := norm_hpullPre_le X g s (p := p) (m := m) hT |σ|
  exact LinearMap.extendOfNorm_eq denseRange_toComplL ⟨C, fun u => by
    rw [norm_toComplL]
    exact (norm_toComplL _).trans_le (hC σ le_rfl u)⟩ u

/-- `Π_σ` on smooth families. -/
theorem hpullExt_ofSmooth (hT : 0 < T) (σ : ℝ) {u : ℝ → SmoothCcTensor g 0 s}
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u) :
    hpullExt X g s p m T σ (ofSmooth u hu) =
      ofSmooth (fun t => hpull X g s σ (u t)) (jointlySmoothOn_hpull X g s σ hu) :=
  hpullExt_coe X g s hT σ _

/-- **Uniform bounds** (`lem:flows` (b)): `‖Π_σ v‖_{𝒫^m} ≤ C ‖v‖_{𝒫^m}` for `|σ| ≤ R`. -/
theorem exists_norm_hpullExt_le (hT : 0 < T) (R : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ σ : ℝ, |σ| ≤ R → ∀ v : ParabolicSpace g s p m T,
      ‖hpullExt X g s p m T σ v‖ ≤ C * ‖v‖ := by
  obtain ⟨C, hC0, hC⟩ := norm_hpullPre_le X g s (p := p) (m := m) hT R
  exact ⟨C, hC0, fun σ hσ v => LinearMap.norm_extendOfNorm_apply_le denseRange_toComplL C
    (fun u => by
      rw [norm_toComplL]
      exact (norm_toComplL _).trans_le (hC σ hσ u)) v⟩

/-- **`Π_σ` preserves `𝒫^m_0`.** -/
theorem hpullExt_mem_zeroAtStart (hT : 0 < T) (σ : ℝ) {v : ParabolicSpace g s p m T}
    (hv : v ∈ zeroAtStart g s p m T) : hpullExt X g s p m T σ v ∈ zeroAtStart g s p m T := by
  have hle : ParabolicPre.zeroAtStart.map
      (UniformSpace.Completion.toComplL (𝕜 := ℝ) (E := ParabolicPre g s p m T)).toLinearMap ≤
      (zeroAtStart g s p m T).comap (hpullExt X g s p m T σ).toLinearMap := by
    rintro _ ⟨u, hu0, rfl⟩
    change hpullExt X g s p m T σ (u : ParabolicSpace g s p m T) ∈ zeroAtStart g s p m T
    rw [hpullExt_coe X g s hT σ u]
    refine Submodule.le_topologicalClosure _ (Submodule.mem_map.mpr ⟨hpullPre X g s σ u, ?_, rfl⟩)
    change hpull X g s σ (u.family 0) = 0
    rw [show u.family 0 = 0 from hu0]
    exact (hpullL X g s σ).map_zero
  have hcl : IsClosed (((zeroAtStart g s p m T).comap (hpullExt X g s p m T σ).toLinearMap :
      Submodule ℝ (ParabolicSpace g s p m T)) : Set (ParabolicSpace g s p m T)) :=
    (Submodule.isClosed_topologicalClosure _).preimage (hpullExt X g s p m T σ).continuous
  exact Submodule.topologicalClosure_minimal _ hle hcl hv

theorem hpullExt_zero (hT : 0 < T) :
    hpullExt X g s p m T 0 = ContinuousLinearMap.id ℝ (ParabolicSpace g s p m T) :=
  clm_ext_ofSmooth fun u hu => by
    rw [hpullExt_ofSmooth X g s hT 0 hu, ContinuousLinearMap.id_apply]
    exact ofSmooth_eq_of_eq g s (funext fun t => hpull_zero X g s (u t)) _ _

/-- **The group law** on `𝒫^m`. -/
theorem hpullExt_comp (hT : 0 < T) (σ τ : ℝ) :
    (hpullExt X g s p m T σ).comp (hpullExt X g s p m T τ) = hpullExt X g s p m T (σ + τ) :=
  clm_ext_ofSmooth fun u hu => by
    rw [ContinuousLinearMap.comp_apply, hpullExt_ofSmooth X g s hT τ hu,
      hpullExt_ofSmooth X g s hT σ (jointlySmoothOn_hpull X g s τ hu),
      hpullExt_ofSmooth X g s hT (σ + τ) hu]
    exact ofSmooth_eq_of_eq g s (funext fun t => hpull_hpull X g s σ τ (u t)) _ _

/-- **Derivative in `σ` for smooth data** (`lem:flows` (a)): `d/dσ Π_σ u = Π_σ ∇_X u` in `𝒫^m`. -/
theorem hasDerivAt_hpullExt_ofSmooth (hT : 0 < T) {u : ℝ → SmoothCcTensor g 0 s}
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u) (σ : ℝ) :
    HasDerivAt (fun τ => hpullExt X g s p m T τ (ofSmooth u hu))
      (hpullExt X g s p m T σ (ofSmooth (fun t => covAlong X g s (u t))
        (jointlySmoothOn_covAlong X g s hu))) σ := by
  rw [hpullExt_ofSmooth X g s hT σ (jointlySmoothOn_covAlong X g s hu)]
  have h := hasDerivAt_ofSmooth_hpull X g s (p := p) (m := m) hT hu σ
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun τ => ?_)
  exact hpullExt_ofSmooth X g s hT τ hu

/-- **Smoothness in `σ` for smooth data** (`lem:flows` (a)): `σ ↦ Π_σ u` is `C^∞` into `𝒫^m`. -/
theorem contDiff_hpullExt_ofSmooth (hT : 0 < T) {u : ℝ → SmoothCcTensor g 0 s}
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u) :
    ContDiff ℝ ∞ (fun τ => hpullExt X g s p m T τ (ofSmooth u hu)) := by
  have h : (fun τ => hpullExt X g s p m T τ (ofSmooth u hu)) = fun τ =>
      ofSmooth (p := p) (m := m) (fun t => hpull X g s τ (u t)) (jointlySmoothOn_hpull X g s τ hu) :=
    funext fun τ => hpullExt_ofSmooth X g s hT τ hu
  rw [h]
  exact contDiff_ofSmooth_hpull X g s hT hu

/-- **Continuity in `σ` for every `v ∈ 𝒫^m`** (`lem:flows` (b)). -/
theorem continuous_hpullExt_apply (hT : 0 < T) (v : ParabolicSpace g s p m T) :
    Continuous fun σ => hpullExt X g s p m T σ v := by
  rw [continuous_iff_continuousAt]
  intro σ₀
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨C, hC0, hC⟩ := exists_norm_hpullExt_le X g s (p := p) (m := m) hT (|σ₀| + 1)
  set η := ε / (3 * (C + 1)) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨u, hu⟩ := Metric.denseRange_iff.mp UniformSpace.Completion.denseRange_coe v η hη0
  have hfc : Continuous fun σ => hpullExt X g s p m T σ (u : ParabolicSpace g s p m T) := by
    have h := (contDiff_ofSmooth_hpull X g s (p := p) (m := m) hT u.2).continuous
    refine h.congr fun σ => ?_
    rw [hpullExt_coe X g s hT σ u]
    rfl
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := Metric.continuousAt_iff.mp hfc.continuousAt (ε / 3) (by positivity)
  refine ⟨min 1 δ₁, lt_min one_pos hδ₁, fun σ hσ => ?_⟩
  have hσ1 : |σ| ≤ |σ₀| + 1 := by
    have h1 : |σ - σ₀| < 1 := by
      rw [← Real.dist_eq]; exact hσ.trans_le (min_le_left _ _)
    calc |σ| = |σ₀ + (σ - σ₀)| := by ring_nf
      _ ≤ |σ₀| + |σ - σ₀| := abs_add_le _ _
      _ ≤ |σ₀| + 1 := by linarith
  have hσ₀1 : |σ₀| ≤ |σ₀| + 1 := by linarith
  have h2 := hδ₁' (hσ.trans_le (min_le_right _ _))
  have hvu : ‖v - (u : ParabolicSpace g s p m T)‖ < η := by rw [← dist_eq_norm]; exact hu
  have huv : ‖(u : ParabolicSpace g s p m T) - v‖ < η := by rw [norm_sub_rev]; exact hvu
  set A := hpullExt X g s p m T σ
  set A₀ := hpullExt X g s p m T σ₀
  have hsplit : A v - A₀ v = A (v - u) + (A u - A₀ u) + A₀ (u - v) := by
    rw [map_sub, map_sub]; abel
  rw [dist_eq_norm, hsplit]
  have hCη : C * η ≤ ε / 3 * (C / (C + 1)) := by
    rw [hη]; field_simp; nlinarith
  have hfrac : C / (C + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
  calc ‖A (v - u) + (A u - A₀ u) + A₀ (u - v)‖
      ≤ ‖A (v - u)‖ + ‖A u - A₀ u‖ + ‖A₀ (u - v)‖ := norm_add₃_le
    _ ≤ C * η + ε / 3 + C * η := by
        refine add_le_add (add_le_add ?_ ?_) ?_
        · exact (hC σ hσ1 _).trans (mul_le_mul_of_nonneg_left hvu.le hC0)
        · rw [← dist_eq_norm]; exact h2.le
        · exact (hC σ₀ hσ₀1 _).trans (mul_le_mul_of_nonneg_left huv.le hC0)
    _ < ε := by nlinarith

/-- **`Π_σ` commutes with `∂ₜ`** on `𝒫^m`. -/
theorem hpullExt_comp_timeDerivExt (hT : 0 < T) (hm : 1 ≤ m) (σ : ℝ) :
    (hpullExt X g s p (m - 1) T σ).comp (timeDerivExt (g := g) (s := s) (p := p) hT hm) =
      (timeDerivExt hT hm).comp (hpullExt X g s p m T σ) :=
  clm_ext_ofSmooth fun u hu => by
    simp only [ContinuousLinearMap.comp_apply]
    rw [timeDerivExt_ofSmooth hT hm hu,
      hpullExt_ofSmooth X g s hT σ (jointlySmoothOn_timeDeriv hT hu),
      hpullExt_ofSmooth X g s hT σ hu,
      timeDerivExt_ofSmooth hT hm (jointlySmoothOn_hpull X g s σ hu)]
    exact ofSmooth_congr hT _ _ fun t ht => (timeDeriv_hpull X g s hT hu σ ht).symm

end HFlow

end ShortTime
