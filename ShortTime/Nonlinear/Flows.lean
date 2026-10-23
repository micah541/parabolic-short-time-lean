import ShortTime.Setting.Jet
import DifferentialGeometry.Geometry.Connection.ParallelTransport.VectorBundle
import DifferentialGeometry.Analysis.ODE.Flow.Complete

/-!
# Horizontal pullback along the flow of a vector field

Paper: Lemma `lem:flows` (a), first part.

Let `X` be a smooth vector field on the closed manifold `M`, with flow `φ_σ` (`flow`), and let
`P_σ(x) : T⁰_s|_x ≃ T⁰_s|_{φ_σ x}` be parallel transport for the Levi-Civita connection along the
flow line `τ ↦ φ_τ(x)` (`pt`). The horizontal pullback of a tensor field `u` is
`(Π_σ u)(x) = P_σ(x)⁻¹ u(φ_σ x)` (`hpull`).

* `contMDiffOn_hpullFib`: `(x, σ, t) ↦ (Π_σ (u t))(x)` is jointly smooth for a jointly smooth
  family `u`; hence `Π_σ` maps smooth fields to smooth fields (`hpull`), jointly smooth families
  to jointly smooth families (`jointlySmoothOn_hpull`), and `σ ↦ Π_σ u` is a jointly smooth
  family (`jointlySmoothOn_hpull_param`).
* `hpull_zero`, `hpull_add`, `hpull_smul`: `Π_0 = id`, linearity.
* `hasDerivAt_hpull_zero`: `d/dσ|_{σ=0} (Π_σ u)(x) = ∇_X u (x)`.

Parallel transport comes from the library (`exists_parallel_transport_on_interval`), along the
family of curves `(σ, p) ↦ φ_σ(p)`. It starts in the fibre over `φ_0(p)`, which is only
propositionally `p`; `fibCast` identifies the two fibres.
-/

noncomputable section

open Bundle Manifold Set Filter
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Analysis.ODE
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Geometry.Connection
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

/-! ### The flow -/

section Flow

variable (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)

/-- A smooth vector field on a compact manifold is complete. -/
theorem flow_complete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ (fun y => X y) :=
  exists_globalIntegralCurve_of_compactSupport (fun y => X y) X.contMDiff
    (isClosed_tsupport _).isCompact

/-- The flow `φ_σ(x)` of `X`. -/
def flow (σ : ℝ) (x : M) : M := curveAt (fun y => X y) (flow_complete X) x σ

theorem flow_zero (x : M) : flow X 0 x = x := curveAt_zero _ _ x

theorem flow_add (σ τ : ℝ) (x : M) : flow X (σ + τ) x = flow X τ (flow X σ x) :=
  curveAt_add _ (X.contMDiff.of_le (by norm_num)) _ x σ τ

theorem contMDiff_flow :
    ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => flow X q.1 q.2) :=
  contMDiff_curveAt _ X.contMDiff _

theorem isMIntegralCurve_flow (x : M) :
    IsMIntegralCurve (fun σ => flow X σ x) (fun y => X y) :=
  curveAt_integralCurve _ _ x

theorem contMDiff_flow_curve (x : M) : ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun σ => flow X σ x) :=
  (contMDiff_flow X).comp (contMDiff_id.prodMk contMDiff_const)

/-- The velocity of a flow line is the vector field. -/
theorem mfderiv_flow_curve (x : M) (σ : ℝ) :
    mfderivWithin 𝓘(ℝ, ℝ) I (fun τ => flow X τ x) univ σ
      ((NormedSpace.fromTangentSpace σ).symm 1) = X (flow X σ x) := by
  rw [mfderivWithin_univ, (isMIntegralCurve_flow X x σ).mfderiv]
  change (1 : ℝ) • X (flow X σ x) = X (flow X σ x)
  exact one_smul ℝ _

end Flow

/-! ### Parallel transport along the flow lines -/

section Transport

variable (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
variable (g : SmoothRiemannianMetric I M) (s : ℕ)

/-- The Levi-Civita connection on `T⁰_s M`. -/
abbrev covT : CovariantDerivative I (TensorRSModel 0 s ℝ E)
    (fun x : M => TensorRSSpace 0 s I x) :=
  TensorRSNabla.tensorRSCovariantDerivative I M 0 s (LeviCivita (I := I) g)

theorem exists_pt :
    ∃ T : ∀ σ : ℝ, ∀ p : M,
        TensorRSSpace 0 s I (flow X 0 p) ≃L[ℝ] TensorRSSpace 0 s I (flow X σ p),
      (∀ p : M, ∀ v : TensorRSSpace 0 s I (flow X 0 p), T 0 p v = v) ∧
      (∀ (e : Trivialization (TensorRSModel 0 s ℝ E)
          (TotalSpace.proj : TotalSpace (TensorRSModel 0 s ℝ E)
            (fun x : M => TensorRSSpace 0 s I x) → M)),
        ∀ [MemTrivializationAtlas e],
        ContMDiffOn ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, TensorRSModel 0 s ℝ E))
          (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
          (fun q : (ℝ × M) × TensorRSModel 0 s ℝ E =>
            (⟨flow X q.1.1 q.1.2, T q.1.1 q.1.2 (e.symmL ℝ (flow X 0 q.1.2) q.2)⟩ :
              TotalSpace (TensorRSModel 0 s ℝ E) (fun x : M => TensorRSSpace 0 s I x)))
          {q | q.1.1 ∈ (univ : Set ℝ) ∧ flow X 0 q.1.2 ∈ e.baseSet}) ∧
      (∀ (e : Trivialization (TensorRSModel 0 s ℝ E)
          (TotalSpace.proj : TotalSpace (TensorRSModel 0 s ℝ E)
            (fun x : M => TensorRSSpace 0 s I x) → M)),
        ∀ [MemTrivializationAtlas e],
        ContMDiffOn ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, TensorRSModel 0 s ℝ E))
          (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
          (fun q : (ℝ × M) × TensorRSModel 0 s ℝ E =>
            (⟨flow X 0 q.1.2,
              (T q.1.1 q.1.2).symm (e.symmL ℝ (flow X q.1.1 q.1.2) q.2)⟩ :
              TotalSpace (TensorRSModel 0 s ℝ E) (fun x : M => TensorRSSpace 0 s I x)))
          {q | q.1.1 ∈ (univ : Set ℝ) ∧ flow X q.1.1 q.1.2 ∈ e.baseSet}) ∧
      ∀ p : M, ∀ v : TensorRSSpace 0 s I (flow X 0 p), ∀ σ ∈ (univ : Set ℝ),
        (covT g s).derivAlongWithin (fun τ => flow X τ p) (fun τ => T τ p v) univ σ = 0 :=
  (covT g s).exists_parallel_transport_on_interval inferInstance ordConnected_univ (mem_univ 0)
    (γ := fun σ p => flow X σ p) (contMDiff_flow X).contMDiffOn

/-- Parallel transport along `τ ↦ φ_τ(p)`, `τ ∈ [0, σ]`, from the fibre over `φ_0(p)`. -/
def ptRaw (σ : ℝ) (p : M) :
    TensorRSSpace 0 s I (flow X 0 p) ≃L[ℝ] TensorRSSpace 0 s I (flow X σ p) :=
  Classical.choose (exists_pt X g s) σ p

theorem ptRaw_zero (p : M) (v : TensorRSSpace 0 s I (flow X 0 p)) : ptRaw X g s 0 p v = v :=
  (Classical.choose_spec (exists_pt X g s)).1 p v

theorem ptRaw_forward (e : Trivialization (TensorRSModel 0 s ℝ E)
      (TotalSpace.proj : TotalSpace (TensorRSModel 0 s ℝ E)
        (fun x : M => TensorRSSpace 0 s I x) → M)) [MemTrivializationAtlas e] :
    ContMDiffOn ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, TensorRSModel 0 s ℝ E))
      (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun q : (ℝ × M) × TensorRSModel 0 s ℝ E =>
        (⟨flow X q.1.1 q.1.2, ptRaw X g s q.1.1 q.1.2 (e.symmL ℝ (flow X 0 q.1.2) q.2)⟩ :
          TotalSpace (TensorRSModel 0 s ℝ E) (fun x : M => TensorRSSpace 0 s I x)))
      {q | q.1.1 ∈ (univ : Set ℝ) ∧ flow X 0 q.1.2 ∈ e.baseSet} :=
  (Classical.choose_spec (exists_pt X g s)).2.1 e

theorem ptRaw_inverse (e : Trivialization (TensorRSModel 0 s ℝ E)
      (TotalSpace.proj : TotalSpace (TensorRSModel 0 s ℝ E)
        (fun x : M => TensorRSSpace 0 s I x) → M)) [MemTrivializationAtlas e] :
    ContMDiffOn ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, TensorRSModel 0 s ℝ E))
      (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun q : (ℝ × M) × TensorRSModel 0 s ℝ E =>
        (⟨flow X 0 q.1.2,
          (ptRaw X g s q.1.1 q.1.2).symm (e.symmL ℝ (flow X q.1.1 q.1.2) q.2)⟩ :
          TotalSpace (TensorRSModel 0 s ℝ E) (fun x : M => TensorRSSpace 0 s I x)))
      {q | q.1.1 ∈ (univ : Set ℝ) ∧ flow X q.1.1 q.1.2 ∈ e.baseSet} :=
  (Classical.choose_spec (exists_pt X g s)).2.2.1 e

theorem ptRaw_parallel (p : M) (v : TensorRSSpace 0 s I (flow X 0 p)) (σ : ℝ) :
    (covT g s).derivAlongWithin (fun τ => flow X τ p) (fun τ => ptRaw X g s τ p v) univ σ = 0 :=
  (Classical.choose_spec (exists_pt X g s)).2.2.2 p v σ (mem_univ σ)

end Transport

/-! ### Identifying fibres over equal points -/

section Cast

variable {s : ℕ}

/-- The identification of the fibres over two equal points. -/
def fibCast {x y : M} (h : x = y) : TensorRSSpace 0 s I x ≃L[ℝ] TensorRSSpace 0 s I y := by
  subst h
  exact ContinuousLinearEquiv.refl ℝ _

theorem mk_fibCast_symm {x y : M} (h : x = y) (v : TensorRSSpace 0 s I y) :
    (⟨x, (fibCast h).symm v⟩ :
      TotalSpace (TensorRSModel 0 s ℝ E) (fun z : M => TensorRSSpace 0 s I z)) = ⟨y, v⟩ := by
  subst h
  rfl

theorem fibCast_symm_apply_section {x y : M} (h : x = y) (u : ∀ z : M, TensorRSSpace 0 s I z) :
    (fibCast h).symm (u y) = u x := by
  subst h
  rfl

/-- `e.symmL` inverts the coordinates of `e` over its base set. -/
theorem symmL_coord (e : Trivialization (TensorRSModel 0 s ℝ E)
      (TotalSpace.proj : TotalSpace (TensorRSModel 0 s ℝ E)
        (fun x : M => TensorRSSpace 0 s I x) → M)) [MemTrivializationAtlas e]
    {y : M} (hy : y ∈ e.baseSet) (v : TensorRSSpace 0 s I y) :
    e.symmL ℝ y (e ⟨y, v⟩).2 = v := by
  rw [Trivialization.symmL_apply _ hy, e.symm_apply_apply_mk hy]

end Cast

/-! ### The horizontal pullback -/

section Pullback

variable (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
variable (g : SmoothRiemannianMetric I M) (s : ℕ)

/-- Parallel transport `P_σ(x) : T⁰_s|_x ≃ T⁰_s|_{φ_σ x}` along the flow line of `x`. -/
def pt (σ : ℝ) (x : M) : TensorRSSpace 0 s I x ≃L[ℝ] TensorRSSpace 0 s I (flow X σ x) :=
  (fibCast (flow_zero X x).symm).trans (ptRaw X g s σ x)

/-- The horizontal pullback, pointwise: `(Π_σ u)(x) = P_σ(x)⁻¹ u(φ_σ x)`. -/
def hpullFib (σ : ℝ) (u : SmoothCcTensor g 0 s) (x : M) : TensorRSSpace 0 s I x :=
  (pt X g s σ x).symm (u.toSection (flow X σ x))

theorem mk_hpullFib (σ : ℝ) (u : SmoothCcTensor g 0 s) (x : M) :
    (⟨x, hpullFib X g s σ u x⟩ :
      TotalSpace (TensorRSModel 0 s ℝ E) (fun z : M => TensorRSSpace 0 s I z)) =
      ⟨flow X 0 x, (ptRaw X g s σ x).symm (u.toSection (flow X σ x))⟩ := by
  unfold hpullFib pt
  rw [ContinuousLinearEquiv.symm_trans_apply]
  exact mk_fibCast_symm _ _

theorem mk_hpullFib_eq (e : Trivialization (TensorRSModel 0 s ℝ E)
      (TotalSpace.proj : TotalSpace (TensorRSModel 0 s ℝ E)
        (fun x : M => TensorRSSpace 0 s I x) → M)) [MemTrivializationAtlas e]
    {σ : ℝ} {x : M} (hx : flow X σ x ∈ e.baseSet) (u : SmoothCcTensor g 0 s) :
    (⟨x, hpullFib X g s σ u x⟩ :
      TotalSpace (TensorRSModel 0 s ℝ E) (fun z : M => TensorRSSpace 0 s I z)) =
      ⟨flow X 0 x, (ptRaw X g s σ x).symm
        (e.symmL ℝ (flow X σ x) (e ⟨flow X σ x, u.toSection (flow X σ x)⟩).2)⟩ := by
  rw [symmL_coord e hx]
  exact mk_hpullFib X g s σ u x

/-- **Joint smoothness of the horizontal pullback**: for a jointly smooth family `u`,
`(x, σ, t) ↦ (Π_σ (u t))(x)` is smooth. -/
theorem contMDiffOn_hpullFib {S : Set ℝ} {u : ℝ → SmoothCcTensor g 0 s}
    (hu : JointlySmoothOn g 0 s S u) :
    ContMDiffOn (I.prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))) (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun q : M × ℝ × ℝ => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun x : M => TensorRSSpace 0 s I x) q.1 (hpullFib X g s q.2.1 (u q.2.2) q.1))
      (univ ×ˢ (univ ×ˢ S)) := by
  rintro ⟨x₀, σ₀, t₀⟩ hq₀
  obtain ⟨e, he⟩ : ∃ e, e = trivializationAt (TensorRSModel 0 s ℝ E)
      (fun x : M => TensorRSSpace 0 s I x) (flow X σ₀ x₀) := ⟨_, rfl⟩
  have : MemTrivializationAtlas e := by rw [he]; infer_instance
  have hy₀ : flow X σ₀ x₀ ∈ e.baseSet := by rw [he]; exact mem_baseSet_trivializationAt _ _ _
  have hG : ContMDiff (I.prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))) I ∞
      (fun q : M × ℝ × ℝ => flow X q.2.1 q.1) :=
    (contMDiff_flow X).comp ((contMDiff_fst.comp contMDiff_snd).prodMk contMDiff_fst)
  -- the family `u` along the flow
  have hU : ContMDiffOn (I.prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))) (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun q : M × ℝ × ℝ => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun x : M => TensorRSSpace 0 s I x) (flow X q.2.1 q.1)
          ((u q.2.2).toSection (flow X q.2.1 q.1)))
      (univ ×ˢ (univ ×ˢ S)) :=
    hu.comp (hG.prodMk (contMDiff_snd.comp contMDiff_snd)).contMDiffOn
      (fun q hq => ⟨mem_univ _, hq.2.2⟩)
  have hc : ContMDiffWithinAt (I.prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))) 𝓘(ℝ, TensorRSModel 0 s ℝ E) ∞
      (fun q : M × ℝ × ℝ => (e ⟨flow X q.2.1 q.1, (u q.2.2).toSection (flow X q.2.1 q.1)⟩).2)
      (univ ×ˢ (univ ×ˢ S)) (x₀, σ₀, t₀) :=
    ((e.contMDiffWithinAt_iff (e.mem_source.mpr hy₀)).mp (hU _ hq₀)).2
  have hin : ContMDiffWithinAt (I.prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)))
      ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun q : M × ℝ × ℝ => ((q.2.1, q.1),
        (e ⟨flow X q.2.1 q.1, (u q.2.2).toSection (flow X q.2.1 q.1)⟩).2))
      (univ ×ˢ (univ ×ˢ S)) (x₀, σ₀, t₀) :=
    have hpair : ContMDiff (I.prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))) (𝓘(ℝ, ℝ).prod I) ∞
        (fun q : M × ℝ × ℝ => (q.2.1, q.1)) :=
      (contMDiff_fst.comp contMDiff_snd).prodMk contMDiff_fst
    (hpair (x₀, σ₀, t₀)).contMDiffWithinAt.prodMk hc
  have hopen : IsOpen {q : (ℝ × M) × TensorRSModel 0 s ℝ E |
      q.1.1 ∈ (univ : Set ℝ) ∧ flow X q.1.1 q.1.2 ∈ e.baseSet} := by
    simp only [mem_univ, true_and]
    exact ((contMDiff_flow X).continuous.comp continuous_fst).isOpen_preimage _ e.open_baseSet
  have hinvAt := (ptRaw_inverse X g s e).contMDiffAt
    (hopen.mem_nhds (x := ((σ₀, x₀),
      (e ⟨flow X σ₀ x₀, (u t₀).toSection (flow X σ₀ x₀)⟩).2)) ⟨mem_univ _, hy₀⟩)
  have hcomp := hinvAt.comp_contMDiffWithinAt (x₀, σ₀, t₀) hin
  have hev : ∀ᶠ q in 𝓝 ((x₀, σ₀, t₀) : M × ℝ × ℝ), flow X q.2.1 q.1 ∈ e.baseSet :=
    hG.continuous.continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds hy₀)
  refine hcomp.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [eventually_nhdsWithin_of_eventually_nhds hev] with q hq
    exact mk_hpullFib_eq X g s e hq (u q.2.2)
  · exact mk_hpullFib_eq X g s e hy₀ (u t₀)

theorem jointlySmoothOn_const (u : SmoothCcTensor g 0 s) (S : Set ℝ) :
    JointlySmoothOn g 0 s S (fun _ => u) :=
  (u.toSection.contMDiff.comp contMDiff_fst).contMDiffOn

/-- `Π_σ u` is a smooth tensor field. -/
theorem contMDiff_hpullFib (σ : ℝ) (u : SmoothCcTensor g 0 s) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) x (hpullFib X g s σ u x)) :=
  (contMDiffOn_hpullFib X g s (jointlySmoothOn_const g s u univ)).comp_contMDiff
    (contMDiff_id.prodMk (contMDiff_const (c := ((σ, 0) : ℝ × ℝ))))
    (fun _ => ⟨mem_univ _, mem_univ _, mem_univ _⟩)

/-- **The horizontal pullback** `Π_σ u` of a smooth tensor field along the flow of `X`. -/
def hpull (σ : ℝ) (u : SmoothCcTensor g 0 s) : SmoothCcTensor g 0 s where
  toSection :=
    { toFun := hpullFib X g s σ u
      contMDiff_toFun := contMDiff_hpullFib X g s σ u }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

theorem hpull_toSection (σ : ℝ) (u : SmoothCcTensor g 0 s) (x : M) :
    (hpull X g s σ u).toSection x = hpullFib X g s σ u x := rfl

/-- The horizontal pullback of a jointly smooth family is jointly smooth. -/
theorem jointlySmoothOn_hpull (σ : ℝ) {S : Set ℝ} {u : ℝ → SmoothCcTensor g 0 s}
    (hu : JointlySmoothOn g 0 s S u) :
    JointlySmoothOn g 0 s S (fun t => hpull X g s σ (u t)) :=
  (contMDiffOn_hpullFib X g s hu).comp
    (contMDiff_fst.prodMk ((contMDiff_const (c := σ)).prodMk contMDiff_snd)).contMDiffOn
    (fun _ hq => ⟨mem_univ _, mem_univ _, hq.2⟩)

/-- `σ ↦ Π_σ u` is a jointly smooth family. -/
theorem jointlySmoothOn_hpull_param (u : SmoothCcTensor g 0 s) :
    JointlySmoothOn g 0 s univ (fun σ => hpull X g s σ u) :=
  (contMDiffOn_hpullFib X g s (jointlySmoothOn_const g s u univ)).comp
    (contMDiff_fst.prodMk (contMDiff_snd.prodMk (contMDiff_const (c := (0 : ℝ))))).contMDiffOn
    (fun _ _ => ⟨mem_univ _, mem_univ _, mem_univ _⟩)

/-! ### `Π_0 = id` and linearity -/

theorem pt_zero_symm_apply (x : M) (u : ∀ z : M, TensorRSSpace 0 s I z) :
    (pt X g s 0 x).symm (u (flow X 0 x)) = u x := by
  unfold pt
  rw [ContinuousLinearEquiv.symm_trans_apply]
  have h : (ptRaw X g s 0 x).symm (u (flow X 0 x)) = u (flow X 0 x) := by
    rw [ContinuousLinearEquiv.symm_apply_eq, ptRaw_zero]
  rw [h]
  exact fibCast_symm_apply_section _ u

theorem hpull_zero (u : SmoothCcTensor g 0 s) : hpull X g s 0 u = u := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  exact pt_zero_symm_apply X g s x (fun z => u.toSection z)

theorem hpull_add (σ : ℝ) (u v : SmoothCcTensor g 0 s) :
    hpull X g s σ (u + v) = hpull X g s σ u + hpull X g s σ v := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  simp only [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
    hpull_toSection, hpullFib, map_add]

theorem hpull_smul (σ : ℝ) (c : ℝ) (u : SmoothCcTensor g 0 s) :
    hpull X g s σ (c • u) = c • hpull X g s σ u := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  simp only [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
    hpull_toSection, hpullFib, map_smul]

/-- `Π_σ` as a linear map. -/
def hpullL (σ : ℝ) : SmoothCcTensor g 0 s →ₗ[ℝ] SmoothCcTensor g 0 s where
  toFun := hpull X g s σ
  map_add' := hpull_add X g s σ
  map_smul' := hpull_smul X g s σ

end Pullback

end HFlow

end ShortTime
