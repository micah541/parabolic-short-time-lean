import ShortTime.Nonlinear.ExistenceTube
import ShortTime.Nonlinear.Nemytskii
import ShortTime.Nonlinear.Cutoff
import ShortTime.Linear.ModelSolve

/-!
# Existence in parabolic spaces (`prop:existence`, covariant bundles)

Let `u₀` be parabolic. Take the truncated formal solution `w = Σ_{ℓ ≤ m} a_ℓ t^ℓ/ℓ!`
(`EquationData.formalPoly`). On a short interval `[0, T₁]` its jets are parabolic with a uniform
Legendre constant (`EquationData.exists_legendre_interval`), so the linearization `L_w` is parabolic and
`∂ₜ - L_w : 𝒫^m_0 → 𝒫^{m-1}` is an isomorphism (`LinearOp.isomorphism`). The map

  `G(v) = ∂ₜ(w + v) - 𝒩(w + v)`  on `𝒫^m_0`

(`ParabolicSpace.existenceMap`) is `C¹` at `0` with `G(0) = f = ∂ₜw - F[w]` and `DG(0) = ∂ₜ - L_w`
(`ParabolicSpace.timeDerivExt_sub_eq_heatExt`, `LinearOp.isomorphism_eq_heatExt`). By the inverse
function theorem (`exists_injOn_and_image_mem_nhds`) `G` is injective near `0` and maps every
neighbourhood of `0` onto a neighbourhood of `f`. Since `∂ₜ^ℓ f(0) = 0` for `ℓ < m`
(`EquationData.formalCoeff_spec`), the cut-off right-hand sides `f_ε = χ(t/ε) f` tend to `f` in
`𝒫^{m-1}` (`ParabolicSpace.tendsto_cutoff`), so `G(v) = f_ε` has a small solution `v ∈ 𝒫^m_0`
(`EquationData.exists_parabolicSpace_solution`). As `f_ε = 0` for `t ≤ ε`, `u = w + v` solves the
equation on `[0, ε]` in `𝒫^{m-1}`; its regularity is a separate step (`prop:regularity`).

* `ParabolicSpace.timeDerivExt`: `∂ₜ : 𝒫^m → 𝒫^{m-1}`, the extension of the time derivative
  (`heatExt` of the zero operator).
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set Filter Topology MeasureTheory Metric
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Spectral
open scoped Manifold ContDiff BigOperators

namespace ShortTime

/-! ### The inverse function theorem around an affine point -/

section IFT

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y] [CompleteSpace Y]

/-- **Inverse function theorem for `v ↦ A(W + v) - 𝒩(W + v)` on a complete subspace.** If `A` is
continuous linear, `𝒩` is `C¹` at `W`, and `A - D𝒩(W)` restricts to an isomorphism `Z ≃ Y`, then
`G(v) = A(W + v) - 𝒩(W + v)` is injective near `0 ∈ Z` and maps every neighbourhood of `0` onto a
neighbourhood of `G(0)`. -/
theorem exists_injOn_and_image_mem_nhds (Z : Submodule ℝ X) [CompleteSpace Z] (A : X →L[ℝ] Y)
    (𝒩 : X → Y) (W : X) (h𝒩 : ContDiffAt ℝ 1 𝒩 W) (Φ : Z ≃L[ℝ] Y)
    (hΦ : ∀ z : Z, Φ z = A z - fderiv ℝ 𝒩 W z) :
    (∃ U ∈ 𝓝 (0 : Z), InjOn (fun v : Z => A (W + v) - 𝒩 (W + v)) U) ∧
      ∀ V ∈ 𝓝 (0 : Z), (fun v : Z => A (W + v) - 𝒩 (W + v)) '' V ∈ 𝓝 (A W - 𝒩 W) := by
  set G : Z → Y := fun v => A (W + v) - 𝒩 (W + v) with hG
  have h0 : W + ((0 : Z) : X) = W := by rw [Submodule.coe_zero, add_zero]
  have haff : HasFDerivAt (fun v : Z => W + (v : X)) Z.subtypeL (0 : Z) :=
    Z.subtypeL.hasFDerivAt.const_add W
  have hd : HasFDerivAt 𝒩 (fderiv ℝ 𝒩 W) (W + ((0 : Z) : X)) := by
    rw [h0]
    exact (h𝒩.differentiableAt one_ne_zero).hasFDerivAt
  have hGd : HasFDerivAt G (A.comp Z.subtypeL - (fderiv ℝ 𝒩 W).comp Z.subtypeL) 0 :=
    (A.hasFDerivAt.comp (0 : Z) haff).sub (hd.comp (0 : Z) haff)
  have hc1 : ContDiffAt ℝ 1 (fun v : Z => W + (v : X)) 0 :=
    contDiffAt_const.add Z.subtypeL.contDiff.contDiffAt
  have h𝒩' : ContDiffAt ℝ 1 𝒩 (W + ((0 : Z) : X)) := by
    rw [h0]
    exact h𝒩
  have hGc : ContDiffAt ℝ 1 G 0 :=
    (A.contDiff.contDiffAt.comp (0 : Z) hc1).sub (h𝒩'.comp (0 : Z) hc1)
  have heq : A.comp Z.subtypeL - (fderiv ℝ 𝒩 W).comp Z.subtypeL = (Φ : Z →L[ℝ] Y) := by
    ext z
    change A z - fderiv ℝ 𝒩 W z = Φ z
    rw [hΦ z]
  have hs : HasStrictFDerivAt G (Φ : Z →L[ℝ] Y) 0 := by
    rw [← heq]
    exact hGc.hasStrictFDerivAt' hGd one_ne_zero
  have hG0 : G 0 = A W - 𝒩 W := by simp only [hG, h0]
  refine ⟨⟨(hs.toOpenPartialHomeomorph G).source,
    (hs.toOpenPartialHomeomorph G).open_source.mem_nhds hs.mem_toOpenPartialHomeomorph_source,
    ?_⟩, fun V hV => ?_⟩
  · have h := (hs.toOpenPartialHomeomorph G).injOn
    rwa [HasStrictFDerivAt.toOpenPartialHomeomorph_coe] at h
  · have h : G '' V ∈ map G (𝓝 0) := image_mem_map hV
    rw [hs.map_nhds_eq_of_equiv, hG0] at h
    exact h

end IFT

/-! ### The cutoff profile -/

/-- The cutoff profile `χ(τ) = ψ(τ - 1)`, with `ψ` the smooth transition: `χ = 0` on `(-∞, 1]` and
`χ = 1` on `[2, ∞)` (`lem:cutoff`). -/
def cutoffProfile (τ : ℝ) : ℝ := Real.smoothTransition (τ - 1)

theorem contDiff_cutoffProfile : ContDiff ℝ ∞ cutoffProfile := by
  unfold cutoffProfile
  exact (Real.smoothTransition.contDiff (n := ⊤)).comp (contDiff_id.sub contDiff_const)

theorem cutoffProfile_eq_zero {τ : ℝ} (h : τ ≤ 1) : cutoffProfile τ = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem cutoffProfile_eq_one {τ : ℝ} (h : 2 ≤ τ) : cutoffProfile τ = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

variable {g : SmoothRiemannianMetric I M}

/-! ### The time derivative on parabolic spaces -/

namespace LinearOp

variable {s p : ℕ} {T : ℝ}

/-- The zero operator. -/
def zeroOp : LinearOp g s p T where
  coeff _ _ := 0
  smooth _ := jointlySmoothOn_const g (Icc 0 T) 0

theorem zeroOp_apply (t : ℝ) (u : SmoothCcTensor g 0 s) :
    (zeroOp : LinearOp g s p T).apply t u = 0 := by
  simp only [apply, zeroOp, operatorFieldApplication_zero_left, Finset.sum_const_zero]

end LinearOp

namespace ParabolicSpace

variable {s p : ℕ} {T : ℝ}

/-- Two continuous linear maps on `𝒫^m` that agree on smooth families are equal. -/
theorem clm_ext_ofSmooth {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {m : ℕ}
    {A B : ParabolicSpace g s p m T →L[ℝ] F}
    (h : ∀ u (hu : JointlySmoothOn g 0 s (Icc 0 T) u), A (ofSmooth u hu) = B (ofSmooth u hu)) :
    A = B := by
  ext x
  exact UniformSpace.Completion.induction_on x (isClosed_eq A.continuous B.continuous)
    fun a => h a.family a.2

/-- **The time derivative `∂ₜ : 𝒫^m → 𝒫^{m-1}`**, the continuous extension of `u ↦ ∂ₜu` from
smooth families (`∂ₜ - L` for the zero operator `L`). -/
def timeDerivExt (hT : 0 < T) {m : ℕ} (hm : 1 ≤ m) :
    ParabolicSpace g s p m T →L[ℝ] ParabolicSpace g s p (m - 1) T :=
  (LinearOp.zeroOp : LinearOp g s p T).heatExt hT hm

theorem timeDerivExt_ofSmooth (hT : 0 < T) {m : ℕ} (hm : 1 ≤ m) {u : ℝ → SmoothCcTensor g 0 s}
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u) :
    timeDerivExt (p := p) hT hm (ofSmooth u hu) =
      ofSmooth (timeDeriv T u) (jointlySmoothOn_timeDeriv hT hu) := by
  rw [timeDerivExt, LinearOp.heatExt_ofSmooth]
  exact ofSmooth_congr hT _ _ fun t _ => by
    simp only [LinearOp.heatOp, LinearOp.zeroOp_apply, sub_zero]

/-- `∂ₜ - A = ∂ₜ - L` on `𝒫^m` when `A` acts as `L` on smooth families. -/
theorem timeDerivExt_sub_eq_heatExt (hT : 0 < T) {m : ℕ} (hm : 1 ≤ m) (L : LinearOp g s p T)
    (A : ParabolicSpace g s p m T →L[ℝ] ParabolicSpace g s p (m - 1) T)
    (hA : ∀ h (hh : JointlySmoothOn g 0 s (Icc 0 T) h), ∃ hL,
      A (ofSmooth h hh) = ofSmooth (fun t => L.apply t (h t)) hL) :
    timeDerivExt hT hm - A = L.heatExt hT hm := by
  refine clm_ext_ofSmooth fun h hh => ?_
  obtain ⟨hL, hAe⟩ := hA h hh
  rw [sub_apply, hAe, timeDerivExt_ofSmooth, L.heatExt_ofSmooth,
    ← ofSmooth_sub]
  rfl

/-- **The map of the existence proof**, `G(v) = ∂ₜ(W + v) - 𝒩(W + v)` on `𝒫^m_0`. -/
def existenceMap (hT : 0 < T) {m : ℕ} (hm : 1 ≤ m)
    (𝒩 : ParabolicSpace g s p m T → ParabolicSpace g s p (m - 1) T)
    (W : ParabolicSpace g s p m T) (v : zeroAtStart g s p m T) : ParabolicSpace g s p (m - 1) T :=
  timeDerivExt hT hm (W + (v : ParabolicSpace g s p m T)) - 𝒩 (W + (v : ParabolicSpace g s p m T))

end ParabolicSpace

namespace LinearOp

variable {s p : ℕ} {T : ℝ}

open ParabolicSpace in
/-- The isomorphism of `thm:linear` (i) is `∂ₜ - L` (`heatExt`) on all of `𝒫^m_0`: both are
continuous and agree on the dense smooth families vanishing at `t = 0`. -/
theorem isomorphism_eq_heatExt (hT : 0 < T) {m : ℕ} (hm : 1 ≤ m) (L : LinearOp g s p T)
    (Φ : zeroAtStart g s p m T ≃L[ℝ] ParabolicSpace g s p (m - 1) T)
    (hΦ : ∀ (u w : ℝ → SmoothCcTensor g 0 s) (hu : JointlySmoothOn g 0 s (Icc 0 T) u)
        (hw : JointlySmoothOn g 0 s (Icc 0 T) w) (h0 : u 0 = 0), L.Solves u w →
        (Φ ⟨ofSmooth u hu, ofSmooth_mem_zeroAtStart u hu h0⟩ :
          ParabolicSpace g s p (m - 1) T) = ofSmooth w hw)
    (z : zeroAtStart g s p m T) :
    Φ z = L.heatExt hT hm z := by
  have hclosed : IsClosed {z : zeroAtStart g s p m T | Φ z = L.heatExt hT hm z} :=
    isClosed_eq Φ.continuous ((L.heatExt hT hm).continuous.comp continuous_subtype_val)
  suffices hz : z ∈ closure {z : zeroAtStart g s p m T | Φ z = L.heatExt hT hm z} by
    rw [hclosed.closure_eq] at hz
    exact hz
  rw [closure_subtype]
  have hz' : (z : ParabolicSpace g s p m T) ∈ closure ((ParabolicPre.zeroAtStart.map
      (UniformSpace.Completion.toComplL (𝕜 := ℝ) (E := ParabolicPre g s p m T)).toLinearMap :
        Submodule ℝ (ParabolicSpace g s p m T)) : Set (ParabolicSpace g s p m T)) := by
    rw [← Submodule.topologicalClosure_coe]
    exact z.2
  refine closure_mono ?_ hz'
  rintro _ ⟨u, hu0, rfl⟩
  refine ⟨⟨ofSmooth u.family u.2, ofSmooth_mem_zeroAtStart u.family u.2 hu0⟩, ?_, rfl⟩
  change Φ ⟨ofSmooth u.family u.2, _⟩ = L.heatExt hT hm (ofSmooth u.family u.2)
  exact (hΦ u.family (L.heatOp u.family) u.2 (L.jointlySmoothOn_heatOp hT u.2) hu0
    (L.solves_heatOp hT u.2)).trans (L.heatExt_ofSmooth hT hm u.2).symm

end LinearOp

/-! ### Existence -/

namespace EquationData

variable {s p : ℕ}

open ParabolicSpace

/-- **Existence in parabolic spaces** (`prop:existence`, covariant bundles). Let `u₀` be parabolic
and `m ≥ ⌊n/2p⌋ + 4`. There are `T₁ ∈ (0, T₀]`, `lam > 0` and a smooth family `w` on `[0, T₁]`
(the truncated formal solution) with `w(0) = u₀`, whose jets are parabolic with Legendre constant
`lam`, such that `f = ∂ₜw - F[w]` vanishes to order `m` at `t = 0`, and the following hold for the
nonlinear operator `𝒩 : 𝒫^m → 𝒫^{m-1}` of `cor:N` around `w` (with its linearization `L_w`, which is
parabolic):

* `G(v) = ∂ₜ(w + v) - 𝒩(w + v)` (`existenceMap`) is injective on a neighbourhood `U` of `0` in
  `𝒫^m_0` (local uniqueness);
* for every neighbourhood `V` of `0` in `𝒫^m_0` and all small `ε > 0`, some `v ∈ V` solves
  `G(v) = f_ε`, where `f_ε = χ(t/ε) f` (`cutoffFamily cutoffProfile ε f`) vanishes for `t ≤ ε`.

So `u = w + v` solves `∂ₜu = F[u]` on `[0, ε]` in `𝒫^{m-1}`. -/
theorem exists_parabolicSpace_solution (D : EquationData I M 0 s p) (hp : 1 ≤ p)
    (u₀ : SmoothCcTensor g 0 s)
    (h₀ : ∀ x : M, D.IsParabolicAt g 0 x (covJet g 0 s (2 * p) u₀ x))
    {m : ℕ} (hm : Module.finrank ℝ E / (2 * p) + 4 ≤ m) :
    ∃ T₁ : ℝ, ∃ hT₁ : 0 < T₁, T₁ ≤ D.T₀ ∧ ∃ lam > 0, ∃ (w : ℝ → SmoothCcTensor g 0 s)
      (hw : JointlySmoothOn g 0 s (Icc 0 T₁) w), w 0 = u₀ ∧
      (∀ t ∈ Icc (0 : ℝ) T₁, ∀ x : M, covJet g 0 s (2 * p) (w t) x ∈ D.dom t x ∧
        LegendreAt g 0 s p x (D.principal t x (covJet g 0 s (2 * p) (w t) x)) lam) ∧
      (∀ l < m, timeDerivIter T₁ (fun t => timeDeriv T₁ w t - D.nonlinFamily w t) l 0 = 0) ∧
      ∃ hf : JointlySmoothOn g 0 s (Icc 0 T₁) (fun t => timeDeriv T₁ w t - D.nonlinFamily w t),
      ∃ hm1 : 1 ≤ m, ∃ δ > 0,
      ∃ 𝒩 : ParabolicSpace g s p m T₁ → ParabolicSpace g s p (m - 1) T₁,
        ContDiffAt ℝ ∞ 𝒩 (ofSmooth w hw) ∧
        (∀ u (hu : JointlySmoothOn g 0 s (Icc 0 T₁) u),
          dist (ofSmooth (p := p) (m := m) u hu) (ofSmooth w hw) < δ →
          (∀ t ∈ Icc (0 : ℝ) T₁, ∀ x : M, covJet g 0 s (2 * p) (u t) x ∈ D.dom t x) ∧
          ∃ hF, 𝒩 (ofSmooth u hu) = ofSmooth (D.nonlinFamily u) hF) ∧
        (∃ L : LinearOp g s p T₁, L.IsParabolic lam ∧
          (∀ k t, t ∈ Icc (0 : ℝ) T₁ → ∀ x,
            opFieldHom ((L.coeff k t).toSection x) =
              D.partialDeriv k t x (covJet g 0 s (2 * p) (w t) x)) ∧
          ∀ h (hh : JointlySmoothOn g 0 s (Icc 0 T₁) h), ∃ hL,
            fderiv ℝ 𝒩 (ofSmooth w hw) (ofSmooth h hh) =
              ofSmooth (fun t => L.apply t (h t)) hL) ∧
        (∃ U ∈ 𝓝 (0 : zeroAtStart g s p m T₁),
          InjOn (existenceMap hT₁ hm1 𝒩 (ofSmooth w hw)) U) ∧
        ∀ V ∈ 𝓝 (0 : zeroAtStart g s p m T₁), ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ v ∈ V,
          existenceMap hT₁ hm1 𝒩 (ofSmooth w hw) v =
            ofSmooth (cutoffFamily cutoffProfile ε
              (fun t => timeDeriv T₁ w t - D.nonlinFamily w t))
              (jointlySmoothOn_cutoffFamily contDiff_cutoffProfile ε hf) := by
  have hm1 : 1 ≤ m := le_trans (by norm_num) (le_trans (Nat.le_add_left 4 _) hm)
  have h₀dom : ∀ x, covJet g 0 s (2 * p) u₀ x ∈ D.dom 0 x := fun x => (h₀ x).1
  -- the formal solution and its parabolicity
  obtain ⟨w, hwdef⟩ : ∃ w, w = D.formalPoly g u₀ m := ⟨_, rfl⟩
  have hw0 : w 0 = u₀ := by rw [hwdef, D.formalPoly_zero u₀ m]
  have hwT : JointlySmoothOn g 0 s (Icc 0 D.T₀) w := by
    rw [hwdef]
    exact D.jointlySmoothOn_formalPoly u₀ m _
  obtain ⟨T₁, hT₁, hT₁D, lam, hlam, hleg⟩ := D.exists_legendre_interval g D.T₀_pos le_rfl hwT
    (fun x => by rw [hw0]; exact h₀ x)
  have hw : JointlySmoothOn g 0 s (Icc 0 T₁) w := by
    rw [hwdef]
    exact D.jointlySmoothOn_formalPoly u₀ m _
  have hdom : ∀ t ∈ Icc (0 : ℝ) T₁, ∀ x, covJet g 0 s (2 * p) (w t) x ∈ D.dom t x :=
    fun t ht x => (hleg t ht x).1
  -- the nonlinear operator and the linearization
  obtain ⟨δ, hδ, 𝒩, h𝒩, hagree, L, hLc, hLd⟩ := D.exists_nonlinOp hp hT₁ hT₁D hm hw hdom
  have hLpar : L.IsParabolic lam := by
    refine ⟨hlam, fun t ht x => ?_⟩
    have h := (hleg t ht x).2
    unfold LinearOp.principal
    rw [hLc ⟨2 * p, Nat.lt_succ_self _⟩ t ht x]
    exact h
  obtain ⟨Φ, hΦ⟩ := L.isomorphism hp hT₁ hLpar m hm1
  -- the defect `f = ∂ₜw - F[w]`
  have hFw := (D.nonlinFamily_spec hT₁D hw hdom).2
  have hf : JointlySmoothOn g 0 s (Icc 0 T₁) (fun t => timeDeriv T₁ w t - D.nonlinFamily w t) :=
    jointlySmoothOn_sub (jointlySmoothOn_timeDeriv hT₁ hw) hFw
  have hfvan : ∀ l < m,
      timeDerivIter T₁ (fun t => timeDeriv T₁ w t - D.nonlinFamily w t) l 0 = 0 := by
    intro l hl
    refine EquationData.formalCoeff_spec (D := D) (u₀ := u₀) h₀dom hT₁ hT₁D hw hdom
      (fun ℓ hℓ => ?_) hl
    rw [hwdef]
    exact D.timeDerivIter_formalPoly u₀ hT₁ hℓ
  -- `G(0) = f` and `DG(0) = ∂ₜ - L_w`
  have hNW : 𝒩 (ofSmooth w hw) = ofSmooth (D.nonlinFamily w) hFw := by
    obtain ⟨-, hF, hEq⟩ := hagree w hw (by rw [dist_self]; exact hδ)
    exact hEq
  have hG0 : timeDerivExt hT₁ hm1 (ofSmooth (p := p) w hw) - 𝒩 (ofSmooth w hw) =
      ofSmooth (fun t => timeDeriv T₁ w t - D.nonlinFamily w t) hf := by
    rw [hNW, timeDerivExt_ofSmooth, ← ofSmooth_sub]
  have hdec : timeDerivExt hT₁ hm1 - fderiv ℝ 𝒩 (ofSmooth w hw) = L.heatExt hT₁ hm1 :=
    timeDerivExt_sub_eq_heatExt hT₁ hm1 L _ hLd
  have hΦW : ∀ z : zeroAtStart g s p m T₁,
      Φ z = timeDerivExt hT₁ hm1 z - fderiv ℝ 𝒩 (ofSmooth w hw) z := fun z => by
    rw [← sub_apply, hdec]
    exact L.isomorphism_eq_heatExt hT₁ hm1 Φ hΦ z
  -- the inverse function theorem
  have : IsClosed ((zeroAtStart g s p m T₁ : Submodule ℝ (ParabolicSpace g s p m T₁)) :
      Set (ParabolicSpace g s p m T₁)) := Submodule.isClosed_topologicalClosure _
  have : CompleteSpace (zeroAtStart g s p m T₁) := IsClosed.completeSpace_coe
  obtain ⟨hinj, himg⟩ := exists_injOn_and_image_mem_nhds (zeroAtStart g s p m T₁)
    (timeDerivExt hT₁ hm1) 𝒩 (ofSmooth w hw) (h𝒩.of_le (by norm_num)) Φ hΦW
  refine ⟨T₁, hT₁, hT₁D, lam, hlam, w, hw, hw0, hleg, hfvan, hf, hm1, δ, hδ, 𝒩, h𝒩, hagree,
    ⟨L, hLpar, hLc, hLd⟩, hinj, fun V hV => ?_⟩
  have hmem := himg V hV
  rw [hG0] at hmem
  have ht := ParabolicSpace.tendsto_cutoff (p := p) hT₁ contDiff_cutoffProfile
    (fun τ hτ => cutoffProfile_eq_one hτ) hf hfvan (Nat.sub_le m 1)
  filter_upwards [ht.eventually_mem hmem] with ε hε
  obtain ⟨v, hv, hve⟩ := hε
  exact ⟨v, hv, hve⟩

end EquationData

end ShortTime
