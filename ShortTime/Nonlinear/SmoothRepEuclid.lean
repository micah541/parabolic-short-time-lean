import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Spatially smooth families and the time bootstrap (Euclidean core of `prop:regularity`)

For a function `φ(t, y)` on `S × U` (`S ⊆ ℝ` a time interval, `U ⊆ E` open), `SpC k S U n V φ`
says that `φ` and its first `n` spatial derivatives `∂_y φ, ∂_y ∂_y φ, …` (nested `fderiv` in `y`)
exist and are `C^k` jointly in `(t, y)`.

* The class is closed under composition with smooth maps `Ψ(t, y, φ(t, y))` and under pairing
  (`SpC.comp`, `SpC.pair`, `SpC.add`), under freezing the time (`SpC.slice`), and contains the
  time-independent smooth functions (`SpC.timeIndep`).
* `SpC_clm`: `(t, y) ↦ ℓ_t(W(y))`, with `W` smooth into a normed space `X` and `ℓ_t : X →L V`
  uniformly bounded and strongly continuous in `t`, is in the class for `k = 0` and every `n`.
  This is how the continuous representative of `Π_σ v` enters (`ℓ_t` an evaluation functional).
* `hasFDerivWithinAt_of_partials`, `contDiffOn_succ_of_partials`: a function with a time partial
  derivative (within `S`) and a continuous spatial derivative is differentiable, and `C^{k+1}` if
  both partials are `C^k`.
* `SpC_primT`: the primitive `∫₀ᵗ G(τ, y) dτ` gains one time derivative.
* **`contDiffOn_of_evolution`** (the bootstrap): if `φ` is spatially smooth with spatial derivatives
  continuous in `(t, y)` (`∀ n, SpC 0 S U n V φ`), `∂ₜ φ = G` on `[0, T] × U`, and `G` is in the
  class of order `k` whenever `φ` is (`G = F(t, y, jets of φ)`), then `φ` is `C^∞` on `[0, T] × U`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set Filter Topology Metric Asymptotics
open scoped ContDiff Convex

namespace ShortTime

namespace SpatialReg

universe u w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `SpC k S U n V φ`: `φ` and its first `n` nested spatial derivatives are `C^k` jointly on
`S ×ˢ U` (and the spatial derivatives exist on `U`). -/
def SpC (k : ℕ) (S : Set ℝ) (U : Set E) :
    ℕ → ∀ (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V], (ℝ → E → V) → Prop
  | 0 => fun _ _ _ φ => ContDiffOn ℝ k (fun q : ℝ × E => φ q.1 q.2) (S ×ˢ U)
  | n + 1 => fun V _ _ φ => ContDiffOn ℝ k (fun q : ℝ × E => φ q.1 q.2) (S ×ˢ U) ∧
      (∀ t ∈ S, ∀ y ∈ U, DifferentiableAt ℝ (φ t) y) ∧
      SpC k S U n (E →L[ℝ] V) (fun t y => fderiv ℝ (φ t) y)

variable {k : ℕ} {S : Set ℝ} {U : Set E}

theorem natCast_le_infty (k : ℕ) : (k : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top

theorem SpC.contDiffOn {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] {φ : ℝ → E → V}
    {n : ℕ} (h : SpC k S U n V φ) : ContDiffOn ℝ k (fun q : ℝ × E => φ q.1 q.2) (S ×ˢ U) := by
  cases n with
  | zero => exact h
  | succ n => exact h.1

theorem SpC.mono_n (n : ℕ) : ∀ {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {φ : ℝ → E → V}, SpC k S U (n + 1) V φ → SpC k S U n V φ := by
  induction n with
  | zero => intro V _ _ φ h; exact h.1
  | succ n ih => intro V _ _ φ h; exact ⟨h.1, h.2.1, ih h.2.2⟩

theorem SpC.of_add {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] {φ : ℝ → E → V}
    {m : ℕ} : ∀ d : ℕ, SpC k S U (m + d) V φ → SpC k S U m V φ
  | 0, h => h
  | d + 1, h => SpC.of_add d (SpC.mono_n _ h)

theorem SpC.of_le {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] {φ : ℝ → E → V}
    {m n : ℕ} (hmn : m ≤ n) (h : SpC k S U n V φ) : SpC k S U m V φ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  exact SpC.of_add d h

theorem SpC.mono_k {k' : ℕ} (hk : k' ≤ k) (n : ℕ) : ∀ {V : Type u} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {φ : ℝ → E → V}, SpC k S U n V φ → SpC k' S U n V φ := by
  induction n with
  | zero => intro V _ _ φ h; exact ContDiffOn.of_le h (by exact_mod_cast hk)
  | succ n ih =>
    intro V _ _ φ h
    exact ⟨ContDiffOn.of_le h.1 (by exact_mod_cast hk), h.2.1, ih h.2.2⟩

theorem SpC.congr (hU : IsOpen U) (n : ℕ) : ∀ {V : Type u} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {φ ψ : ℝ → E → V}, (∀ t ∈ S, ∀ y ∈ U, φ t y = ψ t y) →
    SpC k S U n V φ → SpC k S U n V ψ := by
  induction n with
  | zero =>
    intro V _ _ φ ψ he h
    exact ContDiffOn.congr (show ContDiffOn ℝ k (fun q : ℝ × E => φ q.1 q.2) (S ×ˢ U) from h)
      fun q hq => (he q.1 hq.1 q.2 hq.2).symm
  | succ n ih =>
    intro V _ _ φ ψ he h
    have hev : ∀ t ∈ S, ∀ y ∈ U, φ t =ᶠ[𝓝 y] ψ t := fun t ht y hy =>
      Filter.eventually_of_mem (hU.mem_nhds hy) fun z hz => he t ht z hz
    refine ⟨h.1.congr fun q hq => (he q.1 hq.1 q.2 hq.2).symm, fun t ht y hy =>
      (h.2.1 t ht y hy).congr_of_eventuallyEq (hev t ht y hy).symm, ?_⟩
    exact ih (fun t ht y hy => (hev t ht y hy).fderiv_eq) h.2.2

/-! ### Composition with smooth maps and pairing -/

theorem contDiffOn_comp_aux {V W : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {φ : ℝ → E → V} {O : Set (E × V)}
    {Ψ : ℝ × E × V → W} (hΨ : ContDiffOn ℝ ∞ Ψ (S ×ˢ O))
    (hO : ∀ t ∈ S, ∀ y ∈ U, (y, φ t y) ∈ O)
    (hφ : ContDiffOn ℝ k (fun q : ℝ × E => φ q.1 q.2) (S ×ˢ U)) :
    ContDiffOn ℝ k (fun q : ℝ × E => Ψ (q.1, q.2, φ q.1 q.2)) (S ×ˢ U) :=
  (hΨ.of_le (natCast_le_infty k)).comp (contDiffOn_fst.prodMk (contDiffOn_snd.prodMk hφ))
    fun q hq => ⟨hq.1, hO q.1 hq.1 q.2 hq.2⟩

/-- The chain rule for `y ↦ Ψ(t, y, φ(t, y))`, with the derivative written as a smooth function of
`(t, y, φ, ∂_y φ)`. -/
theorem hasFDerivAt_comp_aux {V W : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {φ : ℝ → E → V} {O : Set (E × V)}
    {Ψ : ℝ × E × V → W} (hOo : IsOpen O) (hΨ : ContDiffOn ℝ ∞ Ψ (S ×ˢ O)) {t : ℝ} (ht : t ∈ S)
    {y : E} (hyO : (y, φ t y) ∈ O) (hφd : DifferentiableAt ℝ (φ t) y) :
    HasFDerivAt (fun y => Ψ (t, y, φ t y))
      ((fderivWithin ℝ Ψ (S ×ˢ O) (t, y, φ t y)).comp
          ((ContinuousLinearMap.inr ℝ ℝ (E × V)).comp (ContinuousLinearMap.inl ℝ E V)) +
        ((fderivWithin ℝ Ψ (S ×ˢ O) (t, y, φ t y)).comp
          ((ContinuousLinearMap.inr ℝ ℝ (E × V)).comp (ContinuousLinearMap.inr ℝ E V))).comp
          (fderiv ℝ (φ t) y)) y := by
  have hι : HasFDerivAt (fun y' : E => ((t, y', φ t y') : ℝ × E × V))
      ((0 : E →L[ℝ] ℝ).prod ((ContinuousLinearMap.id ℝ E).prod (fderiv ℝ (φ t) y))) y :=
    (hasFDerivAt_const t y).prodMk ((hasFDerivAt_id y).prodMk hφd.hasFDerivAt)
  have hΨd : HasFDerivWithinAt Ψ (fderivWithin ℝ Ψ (S ×ˢ O) (t, y, φ t y)) (S ×ˢ O)
      (t, y, φ t y) :=
    ((hΨ.differentiableOn (by simp)) _ ⟨ht, hyO⟩).hasFDerivWithinAt
  have hnhds : (fun y' : E => ((t, y', φ t y') : ℝ × E × V)) ⁻¹' (S ×ˢ O) ∈ 𝓝 y := by
    have hc : ContinuousAt (fun y' => (y', φ t y')) y := continuousAt_id.prodMk hφd.continuousAt
    filter_upwards [hc.preimage_mem_nhds (hOo.mem_nhds hyO)] with y' hy' using ⟨ht, hy'⟩
  have h := (hΨd.comp y hι.hasFDerivWithinAt (mapsTo_preimage _ _)).hasFDerivAt hnhds
  refine h.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inr_apply, ContinuousLinearMap.inl_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.zero_apply, ContinuousLinearMap.id_apply, ← map_add, Prod.mk_add_mk,
    add_zero, zero_add]

theorem SpC.comp_pair (hS : UniqueDiffOn ℝ S) (hU : IsOpen U) (n : ℕ) :
    (∀ {V W : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
      [NormedSpace ℝ W] {φ : ℝ → E → V} {O : Set (E × V)} {Ψ : ℝ × E × V → W},
      IsOpen O → ContDiffOn ℝ ∞ Ψ (S ×ˢ O) → (∀ t ∈ S, ∀ y ∈ U, (y, φ t y) ∈ O) →
      SpC k S U n V φ → SpC k S U n W (fun t y => Ψ (t, y, φ t y))) ∧
    (∀ {V₁ V₂ : Type u} [NormedAddCommGroup V₁] [NormedSpace ℝ V₁] [NormedAddCommGroup V₂]
      [NormedSpace ℝ V₂] {φ₁ : ℝ → E → V₁} {φ₂ : ℝ → E → V₂},
      SpC k S U n V₁ φ₁ → SpC k S U n V₂ φ₂ →
      SpC k S U n (V₁ × V₂) (fun t y => (φ₁ t y, φ₂ t y))) := by
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro V W _ _ _ _ φ O Ψ _ hΨ hO h
      exact contDiffOn_comp_aux hΨ hO h
    intro V₁ V₂ _ _ _ _ φ₁ φ₂ h₁ h₂
    exact ContDiffOn.prodMk (show ContDiffOn ℝ k (fun q : ℝ × E => φ₁ q.1 q.2) (S ×ˢ U) from h₁)
      (show ContDiffOn ℝ k (fun q : ℝ × E => φ₂ q.1 q.2) (S ×ˢ U) from h₂)
  | succ n ih =>
    refine ⟨?_, ?_⟩
    · -- composition
      intro V W _ _ _ _ φ O Ψ hOo hΨ hO h
      have hdiff : ∀ t ∈ S, ∀ y ∈ U, DifferentiableAt ℝ (φ t) y := h.2.1
      set A₀ : E →L[ℝ] ℝ × E × V :=
        (ContinuousLinearMap.inr ℝ ℝ (E × V)).comp (ContinuousLinearMap.inl ℝ E V) with hA₀
      set B₀ : V →L[ℝ] ℝ × E × V :=
        (ContinuousLinearMap.inr ℝ ℝ (E × V)).comp (ContinuousLinearMap.inr ℝ E V) with hB₀
      obtain ⟨D, hD⟩ : ∃ D : ℝ × E × V → (ℝ × E × V →L[ℝ] W),
          D = fderivWithin ℝ Ψ (S ×ˢ O) := ⟨_, rfl⟩
      have hDs : ContDiffOn ℝ ∞ D (S ×ˢ O) := by
        rw [hD]; exact hΨ.fderivWithin (hS.prod hOo.uniqueDiffOn) (by simp)
      let O' : Set (E × (V × (E →L[ℝ] V))) := (fun p => (p.1, p.2.1)) ⁻¹' O
      have hO'o : IsOpen O' :=
        hOo.preimage (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
      let Ψ' : ℝ × E × (V × (E →L[ℝ] V)) → (E →L[ℝ] W) := fun q =>
        (D (q.1, q.2.1, q.2.2.1)).comp A₀ + ((D (q.1, q.2.1, q.2.2.1)).comp B₀).comp q.2.2.2
      have hπ : ContDiffOn ℝ ∞ (fun q : ℝ × E × (V × (E →L[ℝ] V)) => D (q.1, q.2.1, q.2.2.1))
          (S ×ˢ O') :=
        hDs.comp (contDiff_fst.prodMk ((contDiff_fst.comp contDiff_snd).prodMk
          (contDiff_fst.comp (contDiff_snd.comp contDiff_snd)))).contDiffOn
          fun q hq => ⟨hq.1, hq.2⟩
      have hΨ' : ContDiffOn ℝ ∞ Ψ' (S ×ˢ O') :=
        (hπ.clm_comp contDiffOn_const).add ((hπ.clm_comp contDiffOn_const).clm_comp
          (contDiff_snd.comp (contDiff_snd.comp contDiff_snd)).contDiffOn)
      have key : ∀ t ∈ S, ∀ y ∈ U, HasFDerivAt (fun y => Ψ (t, y, φ t y))
          (Ψ' (t, y, (φ t y, fderiv ℝ (φ t) y))) y := by
        intro t ht y hy
        have h := hasFDerivAt_comp_aux hOo hΨ ht (hO t ht y hy) (hdiff t ht y hy)
        rw [← hD] at h
        exact h
      refine ⟨contDiffOn_comp_aux hΨ hO h.1, fun t ht y hy => (key t ht y hy).differentiableAt,
        ?_⟩
      have hpair : SpC k S U n (V × (E →L[ℝ] V)) (fun t y => (φ t y, fderiv ℝ (φ t) y)) :=
        ih.2 (SpC.mono_n n h) h.2.2
      have hcomp := ih.1 (φ := fun t y => (φ t y, fderiv ℝ (φ t) y)) (O := O') (Ψ := Ψ') hO'o hΨ'
        (fun t ht y hy => show (y, φ t y) ∈ O from hO t ht y hy) hpair
      exact SpC.congr hU n (fun t ht y hy => (key t ht y hy).fderiv.symm) hcomp
    · -- pairing
      intro V₁ V₂ _ _ _ _ φ₁ φ₂ h₁ h₂
      refine ⟨ContDiffOn.prodMk h₁.1 h₂.1, fun t ht y hy =>
        (h₁.2.1 t ht y hy).prodMk (h₂.2.1 t ht y hy), ?_⟩
      have hp := ih.2 h₁.2.2 h₂.2.2
      have hsm : ContDiffOn ℝ ∞ (fun q : ℝ × E × ((E →L[ℝ] V₁) × (E →L[ℝ] V₂)) =>
          (ContinuousLinearMap.inl ℝ V₁ V₂).comp q.2.2.1 +
            (ContinuousLinearMap.inr ℝ V₁ V₂).comp q.2.2.2)
          (S ×ˢ (univ : Set (E × ((E →L[ℝ] V₁) × (E →L[ℝ] V₂))))) :=
        ((contDiffOn_const.clm_comp (contDiff_fst.comp (contDiff_snd.comp contDiff_snd)).contDiffOn)).add
          (contDiffOn_const.clm_comp (contDiff_snd.comp (contDiff_snd.comp contDiff_snd)).contDiffOn)
      have hc := ih.1 isOpen_univ hsm (fun _ _ _ _ => trivial) hp
      refine SpC.congr hU n (fun t ht y hy => ?_) hc
      rw [((h₁.2.1 t ht y hy).hasFDerivAt.prodMk (h₂.2.1 t ht y hy).hasFDerivAt).fderiv]
      refine ContinuousLinearMap.ext fun v => ?_
      simp

theorem SpC.comp (hS : UniqueDiffOn ℝ S) (hU : IsOpen U) {n : ℕ} {V W : Type u}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {φ : ℝ → E → V} {O : Set (E × V)} {Ψ : ℝ × E × V → W} (hOo : IsOpen O)
    (hΨ : ContDiffOn ℝ ∞ Ψ (S ×ˢ O)) (hO : ∀ t ∈ S, ∀ y ∈ U, (y, φ t y) ∈ O)
    (h : SpC k S U n V φ) : SpC k S U n W (fun t y => Ψ (t, y, φ t y)) :=
  (SpC.comp_pair hS hU n).1 hOo hΨ hO h

theorem SpC.pair (hS : UniqueDiffOn ℝ S) (hU : IsOpen U) {n : ℕ} {V₁ V₂ : Type u}
    [NormedAddCommGroup V₁] [NormedSpace ℝ V₁] [NormedAddCommGroup V₂] [NormedSpace ℝ V₂]
    {φ₁ : ℝ → E → V₁} {φ₂ : ℝ → E → V₂} (h₁ : SpC k S U n V₁ φ₁) (h₂ : SpC k S U n V₂ φ₂) :
    SpC k S U n (V₁ × V₂) (fun t y => (φ₁ t y, φ₂ t y)) :=
  (SpC.comp_pair hS hU n).2 h₁ h₂

theorem SpC.add (hS : UniqueDiffOn ℝ S) (hU : IsOpen U) {n : ℕ} {V : Type u}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {φ₁ φ₂ : ℝ → E → V} (h₁ : SpC k S U n V φ₁)
    (h₂ : SpC k S U n V φ₂) : SpC k S U n V (fun t y => φ₁ t y + φ₂ t y) :=
  SpC.comp hS hU (O := univ) (Ψ := fun q : ℝ × E × (V × V) => q.2.2.1 + q.2.2.2) isOpen_univ
    ((contDiff_fst.comp (contDiff_snd.comp contDiff_snd)).add
      (contDiff_snd.comp (contDiff_snd.comp contDiff_snd))).contDiffOn
    (fun _ _ _ _ => trivial) (SpC.pair hS hU h₁ h₂)

/-! ### Freezing the time; time-independent functions -/

theorem SpC.slice {t₀ : ℝ} (ht₀ : t₀ ∈ S) (n : ℕ) : ∀ {V : Type u} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {φ : ℝ → E → V}, SpC k S U n V φ → SpC k S U n V (fun _ y => φ t₀ y) := by
  induction n with
  | zero =>
    intro V _ _ φ h
    have h' := ContDiffOn.comp (g := fun q : ℝ × E => φ q.1 q.2)
      (f := fun q : ℝ × E => ((t₀, q.2) : ℝ × E)) (s := S ×ˢ U) (t := S ×ˢ U) h
      (contDiffOn_const.prodMk contDiffOn_snd) fun q hq => ⟨ht₀, hq.2⟩
    exact h'
  | succ n ih =>
    intro V _ _ φ h
    have h' := ContDiffOn.comp (g := fun q : ℝ × E => φ q.1 q.2)
      (f := fun q : ℝ × E => ((t₀, q.2) : ℝ × E)) (s := S ×ˢ U) (t := S ×ˢ U) h.1
      (contDiffOn_const.prodMk contDiffOn_snd) fun q hq => ⟨ht₀, hq.2⟩
    exact ⟨h', fun _ _ y hy => h.2.1 t₀ ht₀ y hy, ih h.2.2⟩

theorem contDiffOn_timeIndep_succ (hS0 : (0 : ℝ) ∈ S) (hU : IsOpen U) {k : ℕ} {V : Type u}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {ψ : E → V}
    (hd : ∀ y ∈ U, DifferentiableAt ℝ ψ y)
    (hk : ContDiffOn ℝ k (fun q : ℝ × E => fderiv ℝ ψ q.2) (S ×ˢ U)) :
    ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (fun q : ℝ × E => ψ q.2) (S ×ˢ U) := by
  have hψ : ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞) ψ U := by
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨fun y hy => (hd y hy).differentiableWithinAt, fun h => ?_, ?_⟩
    · exact absurd h (by simp)
    · exact (hk.comp (contDiffOn_const.prodMk contDiffOn_id) fun y hy => ⟨hS0, hy⟩ :)
  exact hψ.comp contDiffOn_snd fun q hq => hq.2

theorem SpC.timeIndep (hS0 : (0 : ℝ) ∈ S) (hU : IsOpen U) (k : ℕ) : ∀ (n : ℕ) {V : Type u}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {ψ : E → V},
    SpC 0 S U (n + k) V (fun _ y => ψ y) → SpC k S U n V (fun _ y => ψ y) := by
  induction k with
  | zero => intro n V _ _ ψ h; exact h
  | succ k ihk =>
    have hC : ∀ {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] {ψ : E → V},
        SpC 0 S U (0 + (k + 1)) V (fun _ y => ψ y) →
        ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (fun q : ℝ × E => ψ q.2) (S ×ˢ U) := by
      intro V _ _ ψ h
      have h2 : SpC k S U 0 (E →L[ℝ] V) (fun _ y => fderiv ℝ ψ y) := ihk 0 h.2.2
      exact contDiffOn_timeIndep_succ hS0 hU (fun y hy => h.2.1 0 hS0 y hy) h2
    intro n
    induction n with
    | zero => intro V _ _ ψ h; exact hC h
    | succ n ihn =>
      intro V _ _ ψ h
      have h0 : SpC 0 S U (0 + (k + 1)) V (fun _ y => ψ y) := SpC.of_le (by omega) h
      have h3 : SpC 0 S U (n + (k + 1)) (E →L[ℝ] V) (fun _ y => fderiv ℝ ψ y) := by
        have h4 : SpC 0 S U (n + 1 + k) (E →L[ℝ] V) (fun _ y => fderiv ℝ ψ y) := h.2.2
        rwa [show n + 1 + k = n + (k + 1) by omega] at h4
      exact ⟨hC h0, fun _ _ y hy => h.2.1 0 hS0 y hy, ihn h3⟩

/-! ### Joint differentiability from partial derivatives -/

theorem tendsto_fst_nhdsWithin_prod (q : ℝ × E) :
    Tendsto Prod.fst (𝓝[S ×ˢ U] q) (𝓝[S] q.1) :=
  tendsto_nhdsWithin_iff.2 ⟨(continuous_fst.tendsto q).mono_left nhdsWithin_le_nhds,
    eventually_mem_nhdsWithin.mono fun _ h => h.1⟩

theorem tendsto_snd_nhdsWithin_prod (q : ℝ × E) :
    Tendsto Prod.snd (𝓝[S ×ˢ U] q) (𝓝[U] q.2) :=
  tendsto_nhdsWithin_iff.2 ⟨(continuous_snd.tendsto q).mono_left nhdsWithin_le_nhds,
    eventually_mem_nhdsWithin.mono fun _ h => h.2⟩

/-- **Partial derivatives give the derivative**: a time partial derivative `a` at `(t₀, y₀)` (within
`S`) and spatial derivatives `B` on `S × U`, continuous at `(t₀, y₀)`, give the joint derivative
within `S × U`. -/
theorem isLittleO_spatial_aux {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hU : IsOpen U) {φ : ℝ → E → V} {B : ℝ → E → E →L[ℝ] V} {t₀ : ℝ} {y₀ : E} (hy₀ : y₀ ∈ U)
    (hB : ∀ t ∈ S, ∀ y ∈ U, HasFDerivAt (φ t) (B t y) y)
    (hBc : ContinuousWithinAt (fun q : ℝ × E => B q.1 q.2) (S ×ˢ U) (t₀, y₀)) :
    (fun χ : ℝ × E => φ χ.1 χ.2 - φ χ.1 y₀ - B t₀ y₀ (χ.2 - y₀)) =o[𝓝[S ×ˢ U] (t₀, y₀)]
      (fun χ => χ.2 - y₀) := by
  rw [isLittleO_iff]
  intro ε hε
  obtain ⟨δ₁, hδ₁, hB'⟩ := Metric.continuousWithinAt_iff.1 hBc ε hε
  obtain ⟨δ₂, hδ₂, hδ₂U⟩ := Metric.isOpen_iff.1 hU y₀ hy₀
  have hδ : 0 < min δ₁ δ₂ := lt_min hδ₁ hδ₂
  have hball : ball y₀ (min δ₁ δ₂) ⊆ U := (ball_subset_ball (min_le_right _ _)).trans hδ₂U
  filter_upwards [self_mem_nhdsWithin, inter_mem_nhdsWithin (S ×ˢ U)
    (ball_mem_nhds ((t₀, y₀) : ℝ × E) hδ)] with χ hχ hχb
  have hχb' : dist χ (t₀, y₀) < min δ₁ δ₂ := hχb.2
  rw [Prod.dist_eq] at hχb'
  have hχ1 : dist χ.1 t₀ < min δ₁ δ₂ := (max_lt_iff.1 hχb').1
  have hχ2 : χ.2 ∈ ball y₀ (min δ₁ δ₂) := (max_lt_iff.1 hχb').2
  refine Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le' (f := φ χ.1) (f' := B χ.1)
    (s := ball y₀ (min δ₁ δ₂)) (fun z hz => (hB χ.1 hχ.1 z (hball hz)).hasFDerivWithinAt)
    (fun z hz => ?_) (convex_ball y₀ _) (mem_ball_self hδ) hχ2
  have hd : dist ((χ.1, z) : ℝ × E) (t₀, y₀) < δ₁ := by
    rw [Prod.dist_eq]
    exact max_lt (hχ1.trans_le (min_le_left _ _)) ((mem_ball.1 hz).trans_le (min_le_left _ _))
  rw [← dist_eq_norm]
  exact (hB' (x := ((χ.1, z) : ℝ × E)) ⟨hχ.1, hball hz⟩ hd).le

/-- **Partial derivatives give the derivative**: a time partial derivative `a` at `(t₀, y₀)` (within
`S`) and spatial derivatives `B` on `S × U`, continuous at `(t₀, y₀)`, give the joint derivative
within `S × U`. -/
theorem hasFDerivWithinAt_of_partials {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hU : IsOpen U) {φ : ℝ → E → V} {a : V} {B : ℝ → E → E →L[ℝ] V} {t₀ : ℝ} {y₀ : E}
    (hy₀ : y₀ ∈ U) (hA : HasDerivWithinAt (fun t => φ t y₀) a S t₀)
    (hB : ∀ t ∈ S, ∀ y ∈ U, HasFDerivAt (φ t) (B t y) y)
    (hBc : ContinuousWithinAt (fun q : ℝ × E => B q.1 q.2) (S ×ˢ U) (t₀, y₀)) :
    HasFDerivWithinAt (fun q : ℝ × E => φ q.1 q.2)
      ((ContinuousLinearMap.fst ℝ ℝ E).smulRight a +
        (B t₀ y₀).comp (ContinuousLinearMap.snd ℝ ℝ E)) (S ×ˢ U) (t₀, y₀) := by
  rw [hasFDerivWithinAt_iff_isLittleO]
  have hfst : Tendsto (fun χ : ℝ × E => χ.1) (𝓝[S ×ˢ U] ((t₀, y₀) : ℝ × E)) (𝓝[S] t₀) :=
    tendsto_fst_nhdsWithin_prod (t₀, y₀)
  have h1 := isLittleO_spatial_aux hU hy₀ hB hBc
  have h2 := (hasDerivWithinAt_iff_isLittleO.1 hA).comp_tendsto hfst
  have h1' := h1.trans_isBigO (isBigO_of_le (𝓝[S ×ˢ U] ((t₀, y₀) : ℝ × E)) fun χ => by
    simpa using norm_snd_le (χ - ((t₀, y₀) : ℝ × E)))
  have h2' := h2.trans_isBigO (isBigO_of_le (𝓝[S ×ˢ U] ((t₀, y₀) : ℝ × E)) fun χ => by
    simpa using norm_fst_le (χ - ((t₀, y₀) : ℝ × E)))
  refine (h1'.add h2').congr_left fun χ => ?_
  simp only [Function.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Prod.fst_sub, Prod.snd_sub]
  abel

/-- **`C^{k+1}` from partial derivatives**: if `∂ₜ φ = A` (within `S`) and `∂_y φ = B`, with `A, B`
of class `C^k` on `S × U`, then `φ` is `C^{k+1}` on `S × U`. -/
theorem contDiffOn_succ_of_partials {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hS : UniqueDiffOn ℝ S) (hU : IsOpen U) {k : ℕ} {φ A : ℝ → E → V}
    {B : ℝ → E → E →L[ℝ] V}
    (hA : ∀ t ∈ S, ∀ y ∈ U, HasDerivWithinAt (fun τ => φ τ y) (A t y) S t)
    (hB : ∀ t ∈ S, ∀ y ∈ U, HasFDerivAt (φ t) (B t y) y)
    (hAc : ContDiffOn ℝ k (fun q : ℝ × E => A q.1 q.2) (S ×ˢ U))
    (hBc : ContDiffOn ℝ k (fun q : ℝ × E => B q.1 q.2) (S ×ˢ U)) :
    ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (fun q : ℝ × E => φ q.1 q.2) (S ×ˢ U) := by
  have hSU : UniqueDiffOn ℝ (S ×ˢ U) := hS.prod hU.uniqueDiffOn
  have hD : ∀ q ∈ S ×ˢ U, HasFDerivWithinAt (fun q : ℝ × E => φ q.1 q.2)
      ((ContinuousLinearMap.fst ℝ ℝ E).smulRight (A q.1 q.2) +
        (B q.1 q.2).comp (ContinuousLinearMap.snd ℝ ℝ E)) (S ×ˢ U) q := fun q hq =>
    hasFDerivWithinAt_of_partials hU hq.2 (hA q.1 hq.1 q.2 hq.2) hB
      (hBc.continuousOn.continuousWithinAt hq)
  rw [Nat.cast_succ, contDiffOn_succ_iff_fderivWithin hSU]
  refine ⟨fun q hq => (hD q hq).differentiableWithinAt, fun h => absurd h (by simp), ?_⟩
  have hDc : ContDiffOn ℝ k (fun q : ℝ × E =>
      (ContinuousLinearMap.fst ℝ ℝ E).smulRight (A q.1 q.2) +
        (B q.1 q.2).comp (ContinuousLinearMap.snd ℝ ℝ E)) (S ×ˢ U) :=
    (contDiffOn_const.smulRight hAc).add (hBc.clm_comp contDiffOn_const)
  exact hDc.congr fun q hq => (hD q hq).fderivWithin (hSU q hq)

/-! ### The primitive in time -/

/-- The time `τ` clamped to `[0, T]`. -/
def clampT (T τ : ℝ) : ℝ := max 0 (min T τ)

theorem continuous_clampT (T : ℝ) : Continuous (clampT T) :=
  continuous_const.max (continuous_const.min continuous_id)

theorem clampT_mem {T : ℝ} (hT : 0 ≤ T) (τ : ℝ) : clampT T τ ∈ Icc 0 T :=
  ⟨le_max_left _ _, max_le hT (min_le_left _ _)⟩

theorem clampT_of_mem {T τ : ℝ} (hτ : τ ∈ Icc 0 T) : clampT T τ = τ := by
  unfold clampT
  rw [min_eq_right hτ.2, max_eq_right hτ.1]

/-- The primitive `∫₀ᵗ G(τ, y) dτ` (with the integrand clamped to `[0, T]` in time). -/
def primT {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (T : ℝ) (G : ℝ → E → V)
    (t : ℝ) (y : E) : V :=
  ∫ τ in (0 : ℝ)..t, G (clampT T τ) y

section Prim

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {T : ℝ}

theorem continuous_clamp_slice (hT : 0 ≤ T) {G : ℝ → E → V}
    (hG : ContinuousOn (fun q : ℝ × E => G q.1 q.2) (Icc 0 T ×ˢ U)) {y : E} (hy : y ∈ U) :
    Continuous fun τ => G (clampT T τ) y :=
  hG.comp_continuous ((continuous_clampT T).prodMk continuous_const)
    fun τ => ⟨clampT_mem hT τ, hy⟩

theorem continuousOn_primT (hT : 0 ≤ T) {G : ℝ → E → V}
    (hG : ContinuousOn (fun q : ℝ × E => G q.1 q.2) (Icc 0 T ×ˢ U)) :
    ContinuousOn (fun q : ℝ × E => primT T G q.1 q.2) (S ×ˢ U) := by
  have hf : Continuous (Function.uncurry fun (x : ℝ × U) (τ : ℝ) => G (clampT T τ) (x.2 : E)) :=
    hG.comp_continuous (((continuous_clampT T).comp continuous_snd).prodMk
      (continuous_subtype_val.comp (continuous_snd.comp continuous_fst)))
      fun p => ⟨clampT_mem hT _, p.1.2.2⟩
  have h := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (a₀ := 0)
    (μ := MeasureTheory.volume) hf (s := fun x : ℝ × U => x.1) continuous_fst
  refine ContinuousOn.mono ?_ (prod_mono (subset_univ S) subset_rfl)
  rw [continuousOn_iff_continuous_domRestrict]
  have hm : Continuous (fun q : ((univ : Set ℝ) ×ˢ U : Set (ℝ × E)) =>
      ((q.1.1, ⟨q.1.2, q.2.2⟩) : ℝ × U)) :=
    (continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
  exact h.comp hm

theorem hasDerivAt_primT [CompleteSpace V] (hT : 0 ≤ T) {G : ℝ → E → V}
    (hG : ContinuousOn (fun q : ℝ × E => G q.1 q.2) (Icc 0 T ×ˢ U)) {y : E} (hy : y ∈ U)
    (t : ℝ) : HasDerivAt (fun t => primT T G t y) (G (clampT T t) y) t := by
  have hc := continuous_clamp_slice hT hG hy
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    (hc.stronglyMeasurableAtFilter MeasureTheory.volume _) hc.continuousAt

theorem hasFDerivAt_primT [CompleteSpace V] [ProperSpace E] (hT : 0 ≤ T) (hU : IsOpen U)
    {G : ℝ → E → V} {G' : ℝ → E → E →L[ℝ] V}
    (hG : ContinuousOn (fun q : ℝ × E => G q.1 q.2) (Icc 0 T ×ˢ U))
    (hG' : ContinuousOn (fun q : ℝ × E => G' q.1 q.2) (Icc 0 T ×ˢ U))
    (hd : ∀ t ∈ Icc 0 T, ∀ y ∈ U, HasFDerivAt (G t) (G' t y) y) (t : ℝ) {y : E} (hy : y ∈ U) :
    HasFDerivAt (primT T G t) (primT T G' t y) y := by
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU y hy
  have hcb : closedBall y (ε / 2) ⊆ U := (closedBall_subset_ball (by linarith)).trans hεU
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod (isCompact_closedBall y (ε / 2))).exists_bound_of_continuousOn
    (hG'.mono (prod_mono subset_rfl hcb))
  refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ)
    (μ := MeasureTheory.volume) (bound := fun _ => C) (H := E) (E := V)
    (F := fun y' τ => G (clampT T τ) y') (F' := fun y' τ => G' (clampT T τ) y')
    (closedBall_mem_nhds y (half_pos hε)) ?_ ?_ ?_ ?_ ?_ ?_
  · filter_upwards [hU.mem_nhds hy] with y' hy'
    exact (continuous_clamp_slice hT hG hy').aestronglyMeasurable
  · exact (continuous_clamp_slice hT hG hy).intervalIntegrable _ _
  · exact (continuous_clamp_slice hT hG' hy).aestronglyMeasurable
  · exact MeasureTheory.ae_of_all _ fun τ _ y' hy' =>
      hC (clampT T τ, y') ⟨clampT_mem hT τ, hy'⟩
  · exact intervalIntegrable_const
  · exact MeasureTheory.ae_of_all _ fun τ _ y' hy' => hd _ (clampT_mem hT τ) y' (hcb hy')

/-- **The fundamental theorem of calculus** in the form `φ(t) = φ(0) + ∫₀ᵗ ∂ₜφ`. -/
theorem eq_add_primT [CompleteSpace V] (hT : 0 ≤ T) {φ G : ℝ → E → V} {y : E}
    (hφ : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt (fun τ => φ τ y) (G t y) (Icc 0 T) t)
    (hG : ContinuousOn (fun τ => G τ y) (Icc 0 T)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    φ t y = φ 0 y + primT T G t y := by
  have hsub : Icc (0 : ℝ) t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
  have h1 := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht.1
    (fun x hx => (hφ x (hsub hx)).continuousWithinAt.mono hsub)
    (fun x hx => ((hφ x ⟨hx.1.le, hx.2.le.trans ht.2⟩).hasDerivAt
      (Icc_mem_nhds hx.1 (hx.2.trans_le ht.2))).hasDerivWithinAt)
    ((hG.mono hsub).intervalIntegrable_of_Icc ht.1)
  have h2 : primT T G t y = ∫ τ in (0 : ℝ)..t, G τ y := by
    refine intervalIntegral.integral_congr fun τ hτ => ?_
    rw [uIcc_of_le ht.1] at hτ
    simp only [clampT_of_mem (hsub hτ)]
  rw [h2, h1]
  abel

end Prim

section PrimSpC

variable [ProperSpace E] {T : ℝ}

theorem contDiffOn_primT_aux (hT : 0 < T) (hU : IsOpen U) {k : ℕ} {V : Type u}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] {G : ℝ → E → V}
    (h1 : SpC k (Icc 0 T) U 1 V G)
    (hB : ContDiffOn ℝ k (fun q : ℝ × E => primT T (fun t y => fderiv ℝ (G t) y) q.1 q.2)
      (Icc 0 T ×ˢ U)) :
    ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (fun q : ℝ × E => primT T G q.1 q.2)
      (Icc 0 T ×ˢ U) := by
  have hGc := h1.1.continuousOn
  have hG'c : ContinuousOn (fun q : ℝ × E => fderiv ℝ (G q.1) q.2) (Icc 0 T ×ˢ U) :=
    (SpC.contDiffOn h1.2.2).continuousOn
  refine contDiffOn_succ_of_partials (uniqueDiffOn_Icc hT) hU (A := G) (B := fun t y =>
    primT T (fun t y => fderiv ℝ (G t) y) t y) (fun t ht y hy => ?_) (fun t _ y hy => ?_) h1.1 hB
  · have h := (hasDerivAt_primT hT.le hGc hy t).hasDerivWithinAt (s := Icc 0 T)
    rwa [clampT_of_mem ht] at h
  · exact hasFDerivAt_primT hT.le hU hGc hG'c (fun t ht y hy => (h1.2.1 t ht y hy).hasFDerivAt)
      t hy

theorem contDiffOn_primT (hT : 0 < T) (hU : IsOpen U) (k : ℕ) : ∀ {V : Type u}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] {G : ℝ → E → V},
    (∀ n, SpC k (Icc 0 T) U n V G) →
    ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (fun q : ℝ × E => primT T G q.1 q.2)
      (Icc 0 T ×ˢ U) := by
  induction k with
  | zero =>
    intro V _ _ _ G hG
    refine contDiffOn_primT_aux hT hU (hG 1) ?_
    rw [Nat.cast_zero, contDiffOn_zero]
    exact continuousOn_primT hT.le (SpC.contDiffOn (hG 1).2.2).continuousOn
  | succ k ih =>
    intro V _ _ _ G hG
    exact contDiffOn_primT_aux hT hU (hG 1)
      (ih fun n => SpC.mono_k (Nat.le_succ k) n (hG (n + 1)).2.2)

/-- **The primitive gains one time derivative.** -/
theorem SpC_primT (hT : 0 < T) (hU : IsOpen U) (k n : ℕ) : ∀ {V : Type u}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] {G : ℝ → E → V},
    (∀ n', SpC k (Icc 0 T) U n' V G) → SpC (k + 1) (Icc 0 T) U n V (primT T G) := by
  induction n with
  | zero => intro V _ _ _ G hG; exact contDiffOn_primT hT hU k hG
  | succ n ih =>
    intro V _ _ _ G hG
    have hGc := (SpC.contDiffOn (hG 0)).continuousOn
    have hG'c : ContinuousOn (fun q : ℝ × E => fderiv ℝ (G q.1) q.2) (Icc 0 T ×ˢ U) :=
      (SpC.contDiffOn (hG 1).2.2).continuousOn
    have hd : ∀ t ∈ Icc (0 : ℝ) T, ∀ y ∈ U, HasFDerivAt (primT T G t)
        (primT T (fun t y => fderiv ℝ (G t) y) t y) y := fun t _ y hy =>
      hasFDerivAt_primT hT.le hU hGc hG'c (fun t ht y hy => ((hG 1).2.1 t ht y hy).hasFDerivAt)
        t hy
    refine ⟨contDiffOn_primT hT hU k hG, fun t ht y hy => (hd t ht y hy).differentiableAt, ?_⟩
    exact SpC.congr hU n (fun t ht y hy => (hd t ht y hy).fderiv.symm)
      (ih fun n' => (hG (n' + 1)).2.2)

/-- **The time bootstrap.** Let `φ` be spatially smooth on `[0, T] × U`, with all spatial derivatives
continuous in `(t, y)`, and let `∂ₜ φ = G` there. If `G` is in the class of order `k` whenever `φ`
is (as for `G = F(t, y, jets of φ)` with `F` smooth), then `φ` is `C^∞` on `[0, T] × U`. -/
theorem contDiffOn_of_evolution (hT : 0 < T) (hU : IsOpen U) {V : Type u}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] {φ G : ℝ → E → V}
    (h0 : ∀ n, SpC 0 (Icc 0 T) U n V φ)
    (hφ : ∀ t ∈ Icc (0 : ℝ) T, ∀ y ∈ U, HasDerivWithinAt (fun τ => φ τ y) (G t y) (Icc 0 T) t)
    (hG : ∀ k, (∀ n, SpC k (Icc 0 T) U n V φ) → ∀ n, SpC k (Icc 0 T) U n V G) :
    ContDiffOn ℝ ∞ (fun q : ℝ × E => φ q.1 q.2) (Icc 0 T ×ˢ U) := by
  have hS : UniqueDiffOn ℝ (Icc (0 : ℝ) T) := uniqueDiffOn_Icc hT
  have h0S : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
  have key : ∀ k n, SpC k (Icc 0 T) U n V φ := by
    intro k
    induction k with
    | zero => exact h0
    | succ k ih =>
      intro n
      have hGk := hG k ih
      have hI := SpC_primT hT hU k n hGk
      have h₀ : SpC (k + 1) (Icc 0 T) U n V (fun _ y => φ 0 y) :=
        SpC.timeIndep h0S hU (k + 1) n (ψ := fun y => φ 0 y)
          (SpC.slice h0S (n + (k + 1)) (h0 (n + (k + 1))))
      refine SpC.congr hU n (fun t ht y hy => ?_) (SpC.add hS hU h₀ hI)
      exact (eq_add_primT hT.le (fun t ht => hφ t ht y hy)
        ((SpC.contDiffOn (hGk 0)).continuousOn.comp (continuousOn_id.prodMk continuousOn_const)
          fun τ hτ => ⟨hτ, hy⟩) ht).symm
  exact contDiffOn_infty.2 fun k => SpC.contDiffOn (key k 0)

end PrimSpC

/-! ### Evaluation functionals applied to a smooth map -/

section ClmApply

variable [FiniteDimensional ℝ E]

theorem continuousOn_clm_apply_comp {X V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] {ℓ : ℝ → X →L[ℝ] V} {C : ℝ}
    (hℓ : ∀ t ∈ S, ‖ℓ t‖ ≤ C) (hℓc : ∀ x, ContinuousOn (fun t => ℓ t x) S) {W : E → X}
    (hW : ContinuousOn W U) : ContinuousOn (fun q : ℝ × E => ℓ q.1 (W q.2)) (S ×ˢ U) := by
  intro q hq
  have hw : Tendsto (fun q' : ℝ × E => W q'.2 - W q.2) (𝓝[S ×ˢ U] q) (𝓝 0) := by
    have h := ((hW q.2 hq.2).tendsto.comp (tendsto_snd_nhdsWithin_prod (S := S) q)).sub
      (tendsto_const_nhds (x := W q.2))
    simpa using h
  have h1 : Tendsto (fun q' : ℝ × E => ℓ q'.1 (W q'.2) - ℓ q'.1 (W q.2)) (𝓝[S ×ˢ U] q)
      (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (by simpa using hw.norm.const_mul C)
    filter_upwards [self_mem_nhdsWithin] with q' hq'
    rw [← map_sub]
    exact ((ℓ q'.1).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hℓ _ hq'.1) (norm_nonneg _))
  have h2 : Tendsto (fun q' : ℝ × E => ℓ q'.1 (W q.2)) (𝓝[S ×ˢ U] q) (𝓝 (ℓ q.1 (W q.2))) :=
    (hℓc (W q.2) q.1 hq.1).tendsto.comp (tendsto_fst_nhdsWithin_prod q)
  have h3 := h1.add h2
  simp only [sub_add_cancel, zero_add] at h3
  exact h3

theorem SpC_clm_zero {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] {ℓ : ℝ → X →L[ℝ] V} {C : ℝ}
    (hℓ : ∀ t ∈ S, ‖ℓ t‖ ≤ C) (hℓc : ∀ x, ContinuousOn (fun t => ℓ t x) S) {W : E → X}
    (hW : ContinuousOn W U) : ContDiffOn ℝ ((0 : ℕ) : WithTop ℕ∞)
      (fun q : ℝ × E => ℓ q.1 (W q.2)) (S ×ˢ U) := by
  rw [Nat.cast_zero, contDiffOn_zero]
  exact continuousOn_clm_apply_comp hℓ hℓc hW

theorem SpC_clm_step {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] (hU : IsOpen U) {ℓ : ℝ → X →L[ℝ] V}
    {C : ℝ} (hℓ : ∀ t ∈ S, ‖ℓ t‖ ≤ C) (hℓc : ∀ x, ContinuousOn (fun t => ℓ t x) S) {W : E → X}
    (hW : ContDiffOn ℝ ∞ W U) (n : ℕ)
    (h' : SpC 0 S U n (E →L[ℝ] V)
      (fun t y => ContinuousLinearMap.compL ℝ E X V (ℓ t) (fderiv ℝ W y))) :
    SpC 0 S U (n + 1) V (fun t y => ℓ t (W y)) := by
  have hWd : ∀ y ∈ U, DifferentiableAt ℝ W y := fun y hy =>
    (hW.differentiableOn (by simp) y hy).differentiableAt (hU.mem_nhds hy)
  have hd : ∀ t, ∀ y ∈ U, HasFDerivAt (fun y => ℓ t (W y))
      (ContinuousLinearMap.compL ℝ E X V (ℓ t) (fderiv ℝ W y)) y := fun t y hy => by
    rw [ContinuousLinearMap.compL_apply]
    exact (ℓ t).hasFDerivAt.comp y (hWd y hy).hasFDerivAt
  exact ⟨SpC_clm_zero hℓ hℓc hW.continuousOn, fun t _ y hy => (hd t y hy).differentiableAt,
    SpC.congr hU n (fun t _ y hy => (hd t y hy).fderiv.symm) h'⟩

theorem compL_bound_aux {X V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] {ℓ : ℝ → X →L[ℝ] V} {C : ℝ}
    (hℓ : ∀ t ∈ S, ‖ℓ t‖ ≤ C) :
    ∀ t ∈ S, ‖ContinuousLinearMap.compL ℝ E X V (ℓ t)‖ ≤ max C 0 := fun t ht =>
  ContinuousLinearMap.opNorm_le_bound _ (le_max_right _ _) fun L => by
    rw [ContinuousLinearMap.compL_apply]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right ((hℓ t ht).trans (le_max_left _ _)) (norm_nonneg _))

theorem compL_cont_aux {X V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] {ℓ : ℝ → X →L[ℝ] V}
    (hℓc : ∀ x, ContinuousOn (fun t => ℓ t x) S) (L : E →L[ℝ] X) :
    ContinuousOn (fun t => ContinuousLinearMap.compL ℝ E X V (ℓ t) L) S := by
  rw [continuousOn_clm_apply]
  intro e
  simpa using hℓc (L e)

theorem SpC_clm_aux (hU : IsOpen U) (n : ℕ) : ∀ {X : Type (max u w)} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {ℓ : ℝ → X →L[ℝ] V} {C : ℝ}, (∀ t ∈ S, ‖ℓ t‖ ≤ C) → (∀ x, ContinuousOn (fun t => ℓ t x) S) →
    ∀ {W : E → X}, ContDiffOn ℝ ∞ W U → SpC 0 S U n V (fun t y => ℓ t (W y)) := by
  induction n with
  | zero => intro X _ _ V _ _ ℓ C hℓ hℓc W hW; exact SpC_clm_zero hℓ hℓc hW.continuousOn
  | succ n ih =>
    intro X _ _ V _ _ ℓ C hℓ hℓc W hW
    exact SpC_clm_step hU hℓ hℓc hW n
      (ih (compL_bound_aux hℓ) (compL_cont_aux hℓc) (hW.fderiv_of_isOpen hU (by simp)))

/-- **Evaluation functionals applied to a smooth map**: if `W : U → X` is `C^∞` and `ℓ_t : X →L V`
is bounded uniformly in `t ∈ S` and strongly continuous, then `(t, y) ↦ ℓ_t(W y)` has all spatial
derivatives, continuous in `(t, y)`. -/
theorem SpC_clm (hU : IsOpen U) {X : Type w} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] {ℓ : ℝ → X →L[ℝ] V} {C : ℝ}
    (hℓ : ∀ t ∈ S, ‖ℓ t‖ ≤ C) (hℓc : ∀ x, ContinuousOn (fun t => ℓ t x) S) {W : E → X}
    (hW : ContDiffOn ℝ ∞ W U) (n : ℕ) : SpC 0 S U n V (fun t y => ℓ t (W y)) := by
  cases n with
  | zero => exact SpC_clm_zero hℓ hℓc hW.continuousOn
  | succ n =>
    exact SpC_clm_step hU hℓ hℓc hW n
      (SpC_clm_aux.{u, w} hU n (X := E →L[ℝ] X) (compL_bound_aux hℓ) (compL_cont_aux hℓc)
        (hW.fderiv_of_isOpen hU (by simp)))

end ClmApply

end SpatialReg

end ShortTime
