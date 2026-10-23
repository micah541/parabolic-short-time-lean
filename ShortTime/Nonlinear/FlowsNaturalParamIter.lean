import ShortTime.Nonlinear.FlowsNaturalParam

/-!
# Naturality of the equation under composite horizontal flows

Paper: Lemma `lem:flows` (d), iterated over a frame.

For vector fields `B 0, …, B (n-1)` and `σ ∈ ℝⁿ`, the composite horizontal pullback is

  `Π_σ = Π^{B 0}_{σ 0} ∘ Π^{B 1}_{σ 1} ∘ ⋯ ∘ Π^{B (n-1)}_{σ (n-1)}`     (`iterPull`),

defined by recursion: `Π_σ = Π^{B 0}_{σ 0} ∘ Π^{B ∘ succ}_{σ ∘ succ}`. It is jointly smooth
(`jointlySmoothOn_iterPull`, `contMDiffOn_iterPull`, `contMDiff_iterPull_const`), and
`Π_0 = id` (`iterPull_zero`).

Iterating `natParam` gives a smooth fibre map `Φ^B` with parameter `σ ∈ ℝⁿ` (`iterFM`), with
`Φ^B(0) = F` (`iterFM_F_zero`, `iterFM_dom_zero`) and, for `|σ i| < δ_i`,

  `Π_σ (F[u](t)) = Φ^B[σ, j(Π_σ u)](t)`                           (`iterPull_nonlinFamily`).
-/

noncomputable section

open Bundle Manifold Set Filter
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Analysis.ODE
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Analysis.Sobolev
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

/-! ### Joint smoothness of the horizontal pullback, with a parameter manifold -/

section JointParam

variable (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
variable (g : SmoothRiemannianMetric I M) (s : ℕ)
variable {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] {HN : Type*}
  [TopologicalSpace HN] {J : ModelWithCorners ℝ EN HN} {Nn : Type*} [TopologicalSpace Nn]
  [ChartedSpace HN Nn]

/-- **Joint smoothness of the horizontal pullback** for a family `u` indexed by a manifold:
`(x, σ, w) ↦ (Π_σ (u w))(x)` is smooth when `(x, w) ↦ u w x` is. -/
theorem contMDiffOn_hpullFib_param {S : Set Nn} {u : Nn → SmoothCcTensor g 0 s}
    (hu : ContMDiffOn (I.prod J) (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun q : M × Nn => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun x : M => TensorRSSpace 0 s I x) q.1 ((u q.2).toSection q.1))
      ((univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod (𝓘(ℝ, ℝ).prod J)) (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun q : M × ℝ × Nn => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun x : M => TensorRSSpace 0 s I x) q.1 (hpullFib X g s q.2.1 (u q.2.2) q.1))
      (univ ×ˢ (univ ×ˢ S)) := by
  rintro ⟨x₀, σ₀, t₀⟩ hq₀
  obtain ⟨e, he⟩ : ∃ e, e = trivializationAt (TensorRSModel 0 s ℝ E)
      (fun x : M => TensorRSSpace 0 s I x) (flow X σ₀ x₀) := ⟨_, rfl⟩
  have : MemTrivializationAtlas e := by rw [he]; infer_instance
  have hy₀ : flow X σ₀ x₀ ∈ e.baseSet := by rw [he]; exact mem_baseSet_trivializationAt _ _ _
  have hG : ContMDiff (I.prod (𝓘(ℝ, ℝ).prod J)) I ∞
      (fun q : M × ℝ × Nn => flow X q.2.1 q.1) :=
    (contMDiff_flow X).comp ((contMDiff_fst.comp contMDiff_snd).prodMk contMDiff_fst)
  have hU : ContMDiffOn (I.prod (𝓘(ℝ, ℝ).prod J)) (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun q : M × ℝ × Nn => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun x : M => TensorRSSpace 0 s I x) (flow X q.2.1 q.1)
          ((u q.2.2).toSection (flow X q.2.1 q.1)))
      (univ ×ˢ (univ ×ˢ S)) :=
    hu.comp (hG.prodMk (contMDiff_snd.comp contMDiff_snd)).contMDiffOn
      (fun q hq => ⟨mem_univ _, hq.2.2⟩)
  have hc : ContMDiffWithinAt (I.prod (𝓘(ℝ, ℝ).prod J)) 𝓘(ℝ, TensorRSModel 0 s ℝ E) ∞
      (fun q : M × ℝ × Nn => (e ⟨flow X q.2.1 q.1, (u q.2.2).toSection (flow X q.2.1 q.1)⟩).2)
      (univ ×ˢ (univ ×ˢ S)) (x₀, σ₀, t₀) :=
    ((e.contMDiffWithinAt_iff (e.mem_source.mpr hy₀)).mp (hU _ hq₀)).2
  have hin : ContMDiffWithinAt (I.prod (𝓘(ℝ, ℝ).prod J))
      ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun q : M × ℝ × Nn => ((q.2.1, q.1),
        (e ⟨flow X q.2.1 q.1, (u q.2.2).toSection (flow X q.2.1 q.1)⟩).2))
      (univ ×ˢ (univ ×ˢ S)) (x₀, σ₀, t₀) :=
    have hpair : ContMDiff (I.prod (𝓘(ℝ, ℝ).prod J)) (𝓘(ℝ, ℝ).prod I) ∞
        (fun q : M × ℝ × Nn => (q.2.1, q.1)) :=
      (contMDiff_fst.comp contMDiff_snd).prodMk contMDiff_fst
    (hpair (x₀, σ₀, t₀)).contMDiffWithinAt.prodMk hc
  have hopen : IsOpen {q' : (ℝ × M) × TensorRSModel 0 s ℝ E |
      q'.1.1 ∈ (univ : Set ℝ) ∧ flow X q'.1.1 q'.1.2 ∈ e.baseSet} := by
    simp only [mem_univ, true_and]
    exact ((contMDiff_flow X).continuous.comp continuous_fst).isOpen_preimage _ e.open_baseSet
  have hinvAt := (ptRaw_inverse X g s e).contMDiffAt
    (hopen.mem_nhds (x := ((σ₀, x₀),
      (e ⟨flow X σ₀ x₀, (u t₀).toSection (flow X σ₀ x₀)⟩).2)) ⟨mem_univ _, hy₀⟩)
  have hcomp := hinvAt.comp_contMDiffWithinAt (x₀, σ₀, t₀) hin
  have hev : ∀ᶠ q in 𝓝 ((x₀, σ₀, t₀) : M × ℝ × Nn), flow X q.2.1 q.1 ∈ e.baseSet :=
    hG.continuous.continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds hy₀)
  refine hcomp.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [eventually_nhdsWithin_of_eventually_nhds hev] with q hq
    exact mk_hpullFib_eq X g s e hq (u q.2.2)
  · exact mk_hpullFib_eq X g s e hy₀ (u t₀)

end JointParam

/-! ### The composite pullback -/

section Iter

/-- **The composite horizontal pullback**
`Π_σ = Π^{B 0}_{σ 0} ∘ Π^{B 1}_{σ 1} ∘ ⋯ ∘ Π^{B (n-1)}_{σ (n-1)}`. -/
def iterPull : {n : ℕ} → (B : Fin n → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) →
    (g : SmoothRiemannianMetric I M) → (s : ℕ) → (σ : Fin n → ℝ) →
    SmoothCcTensor g 0 s → SmoothCcTensor g 0 s
  | 0, _, _, _, _, u => u
  | _ + 1, B, g, s, σ, u =>
    hpull (B 0) g s (σ 0) (iterPull (fun i => B i.succ) g s (fun i => σ i.succ) u)

variable (g : SmoothRiemannianMetric I M) (s : ℕ)

theorem iterPull_zero_len (B : Fin 0 → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (σ : Fin 0 → ℝ) (u : SmoothCcTensor g 0 s) : iterPull B g s σ u = u := rfl

theorem iterPull_succ {n : ℕ} (B : Fin (n + 1) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (σ : Fin (n + 1) → ℝ) (u : SmoothCcTensor g 0 s) :
    iterPull B g s σ u =
      hpull (B 0) g s (σ 0) (iterPull (fun i => B i.succ) g s (fun i => σ i.succ) u) := rfl

/-- **`Π_0 = id`**. -/
theorem iterPull_zero {n : ℕ} (B : Fin n → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (u : SmoothCcTensor g 0 s) : iterPull B g s 0 u = u := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterPull_succ]
    exact (congrArg (hpull (B 0) g s 0) (ih (fun i => B i.succ))).trans (hpull_zero _ g s u)

/-- The composite pullback of a jointly smooth family is jointly smooth. -/
theorem jointlySmoothOn_iterPull {n : ℕ}
    (B : Fin n → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (σ : Fin n → ℝ) {S : Set ℝ}
    {u : ℝ → SmoothCcTensor g 0 s} (hu : JointlySmoothOn g 0 s S u) :
    JointlySmoothOn g 0 s S (fun t => iterPull B g s σ (u t)) := by
  induction n with
  | zero => exact hu
  | succ n ih =>
    exact jointlySmoothOn_hpull (B 0) g s (σ 0) (ih (fun i => B i.succ) (fun i => σ i.succ))

variable {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] {HN : Type*}
  [TopologicalSpace HN] {J : ModelWithCorners ℝ EN HN} {Nn : Type*} [TopologicalSpace Nn]
  [ChartedSpace HN Nn]

/-- **Joint smoothness of the composite pullback** in `(x, σ, w)`, for a family `u` indexed by a
manifold. -/
theorem contMDiffOn_iterPull {n : ℕ}
    (B : Fin n → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) {S : Set Nn}
    {u : Nn → SmoothCcTensor g 0 s}
    (hu : ContMDiffOn (I.prod J) (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun q : M × Nn => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun x : M => TensorRSSpace 0 s I x) q.1 ((u q.2).toSection q.1))
      ((univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod (𝓘(ℝ, Fin n → ℝ).prod J)) (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun q : M × (Fin n → ℝ) × Nn => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun x : M => TensorRSSpace 0 s I x) q.1
        ((iterPull B g s q.2.1 (u q.2.2)).toSection q.1))
      (univ ×ˢ (univ ×ˢ S)) := by
  induction n with
  | zero =>
    refine (hu.comp (contMDiff_fst.prodMk (contMDiff_snd.comp contMDiff_snd)).contMDiffOn
      (fun q hq => ⟨mem_univ _, hq.2.2⟩)).congr fun q _ => rfl
  | succ n ih =>
    have hA := contMDiffOn_hpullFib_param (B 0) g s (J := 𝓘(ℝ, Fin n → ℝ).prod J)
      (S := (univ : Set (Fin n → ℝ)) ×ˢ S)
      (u := fun r : (Fin n → ℝ) × Nn => iterPull (fun i => B i.succ) g s r.1 (u r.2))
      (ih (fun i => B i.succ))
    have h0 : ContMDiff 𝓘(ℝ, Fin (n + 1) → ℝ) 𝓘(ℝ, ℝ) ∞ (fun σ : Fin (n + 1) → ℝ => σ 0) :=
      (contDiff_apply (𝕜 := ℝ) (E := ℝ) (0 : Fin (n + 1))).contMDiff
    have htail : ContMDiff 𝓘(ℝ, Fin (n + 1) → ℝ) 𝓘(ℝ, Fin n → ℝ) ∞
        (fun σ : Fin (n + 1) → ℝ => fun i : Fin n => σ i.succ) :=
      (contDiff_pi.2 fun i : Fin n =>
        contDiff_apply (𝕜 := ℝ) (E := ℝ) (Fin.succ i)).contMDiff
    have hψ : ContMDiff (I.prod (𝓘(ℝ, Fin (n + 1) → ℝ).prod J))
        (I.prod (𝓘(ℝ, ℝ).prod ((𝓘(ℝ, Fin n → ℝ)).prod J))) ∞
        (fun q : M × (Fin (n + 1) → ℝ) × Nn =>
          (q.1, q.2.1 0, (fun i : Fin n => q.2.1 i.succ), q.2.2)) :=
      contMDiff_fst.prodMk ((h0.comp (contMDiff_fst.comp contMDiff_snd)).prodMk
        ((htail.comp (contMDiff_fst.comp contMDiff_snd)).prodMk
          (contMDiff_snd.comp contMDiff_snd)))
    exact (hA.comp hψ.contMDiffOn
      (fun q hq => ⟨mem_univ _, mem_univ _, mem_univ _, hq.2.2⟩)).congr fun q _ => rfl

/-- `(x, σ) ↦ (Π_σ u)(x)` is smooth. -/
theorem contMDiff_iterPull_const {n : ℕ}
    (B : Fin n → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (u : SmoothCcTensor g 0 s) :
    ContMDiff (I.prod 𝓘(ℝ, Fin n → ℝ)) (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun q : M × (Fin n → ℝ) => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun x : M => TensorRSSpace 0 s I x) q.1 ((iterPull B g s q.2 u).toSection q.1)) := by
  have h := contMDiffOn_iterPull g s B (J := 𝓘(ℝ, ℝ)) (S := univ)
    (u := fun _ : ℝ => u) (jointlySmoothOn_const g s u univ)
  have hψ : ContMDiff (I.prod 𝓘(ℝ, Fin n → ℝ)) (I.prod (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, ℝ))) ∞
      (fun q : M × (Fin n → ℝ) => (q.1, q.2, (0 : ℝ))) :=
    contMDiff_fst.prodMk (contMDiff_snd.prodMk contMDiff_const)
  rw [← contMDiffOn_univ]
  exact (h.comp hψ.contMDiffOn
    (fun _ _ => ⟨mem_univ _, mem_univ _, mem_univ _⟩)).congr fun q _ => rfl

end Iter

/-! ### The iterated transported nonlinearity -/

section IterFM

variable (g : SmoothRiemannianMetric I M) {s p : ℕ}

/-- `σ ↦ (σ ∘ succ, σ 0)`. -/
def consL (n : ℕ) : (Fin (n + 1) → ℝ) →L[ℝ] (Fin n → ℝ) × ℝ :=
  (ContinuousLinearMap.pi fun i : Fin n =>
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) i.succ).prod
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) 0)

theorem consL_apply (n : ℕ) (σ : Fin (n + 1) → ℝ) :
    consL n σ = ((fun i : Fin n => σ i.succ), σ 0) := rfl

/-- **The iterated transported nonlinearity** `Φ^B`, a smooth fibre map with parameter
`σ ∈ ℝⁿ`: `Φ^∅ = F`, `Φ^B(σ) = (Φ^{B ∘ succ})_{B 0}(σ ∘ succ, σ 0)`. -/
def iterFM : {n : ℕ} → (B : Fin n → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) →
    (g : SmoothRiemannianMetric I M) → EquationData I M 0 s p →
    FibreMap I M (Fin n → ℝ) (EquationData.jetRanks s p) s
  | 0, _, _, D => D.toFibreMap.reparam 0
  | n + 1, B, g, D => (natParam (B 0) g (iterFM (fun i => B i.succ) g D)).reparam (consL n)

variable (D : EquationData I M 0 s p)

theorem iterFM_succ {n : ℕ} (B : Fin (n + 1) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    iterFM B g D = (natParam (B 0) g (iterFM (fun i => B i.succ) g D)).reparam (consL n) := rfl

theorem iterFM_T₀ {n : ℕ} (B : Fin n → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    (iterFM B g D).T₀ = D.T₀ := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih (fun i => B i.succ)

theorem iterFM_F_succ {n : ℕ} (B : Fin (n + 1) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (σ : Fin (n + 1) → ℝ) :
    (iterFM B g D).F σ =
      (natParam (B 0) g (iterFM (fun i => B i.succ) g D)).F ((fun i => σ i.succ), σ 0) := rfl

theorem iterFM_dom_succ {n : ℕ} (B : Fin (n + 1) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (σ : Fin (n + 1) → ℝ) :
    (iterFM B g D).dom σ =
      (natParam (B 0) g (iterFM (fun i => B i.succ) g D)).dom ((fun i => σ i.succ), σ 0) := rfl

/-- **`Φ^B(0) = F`**. -/
theorem iterFM_F_zero {n : ℕ} (B : Fin n → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (t : ℝ) (x : M) (ζ : CovJetFiber I 0 s (2 * p) x) :
    (iterFM B g D).F 0 t x ζ = D.F t x ζ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterFM_F_succ]
    exact (natParam_F_zero (B 0) g _ _ t x ζ).trans (ih (fun i => B i.succ))

/-- **`dom Φ^B(0) = dom F`**. -/
theorem iterFM_dom_zero {n : ℕ} (B : Fin n → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (t : ℝ) (x : M) : (iterFM B g D).dom 0 t x = D.dom t x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterFM_dom_succ]
    exact (natParam_dom_zero (B 0) g _ _ t x).trans (ih (fun i => B i.succ))

/-- The radii: `|σ i| < δ_i` for all `i`. -/
def IterSmall {n : ℕ} (B : Fin n → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (s N : ℕ)
    (σ : Fin n → ℝ) : Prop :=
  ∀ i, |σ i| < natδ (B i) g s N (I := I)

/-- The jets of `Π_σ u` lie in the domain of `Φ^B(σ)` when those of `u` lie in `𝒟`. -/
theorem covJet_iterPull_mem_dom {n : ℕ}
    (B : Fin n → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) {σ : Fin n → ℝ}
    (hσ : IterSmall g B s (2 * p) σ) {t : ℝ} {u : SmoothCcTensor g 0 s}
    (hu : ∀ x, covJet g 0 s (2 * p) u x ∈ D.dom t x) (x : M) :
    covJet g 0 s (2 * p) (iterPull B g s σ u) x ∈ (iterFM B g D).dom σ t x := by
  induction n generalizing x with
  | zero => exact hu x
  | succ n ih =>
    rw [iterFM_dom_succ, iterPull_succ]
    exact covJet_hpull_mem_natParam_dom (B 0) g _ (hσ 0)
      (fun y => ih (B := fun i => B i.succ) (σ := fun i => σ i.succ) (hσ := fun i => hσ i.succ)
        (x := y)) x

/-- **Naturality under the composite flow**: `Π_σ (F[u](t)) = Φ^B[σ, j(Π_σ u)](t)` for a jointly
smooth family `u` with jets in `𝒟`, and `|σ i| < δ_i`. -/
theorem iterPull_nonlinFamily {n : ℕ}
    (B : Fin n → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) {T : ℝ} (hT : T ≤ D.T₀)
    {u : ℝ → SmoothCcTensor g 0 s} (hu : JointlySmoothOn g 0 s (Icc 0 T) u)
    (hdom : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, covJet g 0 s (2 * p) (u t) x ∈ D.dom t x)
    {σ : Fin n → ℝ} (hσ : IterSmall g B s (2 * p) σ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    iterPull B g s σ (D.nonlinFamily u t) =
      (iterFM B g D).apply σ
        (EquationData.jetFamily (p := p) (fun τ => iterPull B g s σ (u τ))) t := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterPull_succ,
      ih (B := fun i => B i.succ) (σ := fun i => σ i.succ) (hσ := fun i => hσ i.succ),
      iterFM_succ, FibreMap.reparam_apply, consL_apply]
    refine hpull_fibreApply (B 0) g (iterFM (fun i => B i.succ) g D) ?_
      (jointlySmoothOn_iterPull g s (fun i => B i.succ) (fun i => σ i.succ) hu)
      (fun τ hτ x => covJet_iterPull_mem_dom g D (fun i => B i.succ) (fun i => hσ i.succ)
        (hdom τ hτ) x) (hσ 0) ht
    rw [iterFM_T₀]
    exact hT

end IterFM

end HFlow

end ShortTime
