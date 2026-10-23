import ShortTime.Nonlinear.FibreMap
import Mathlib.Analysis.Analytic.CPolynomial

/-!
# Calculus of fibre maps: reindexing and iterated fibre derivatives

For a smooth fibre map `F(λ, t, x, ζ)` on `⊕_{c ∈ ι} T⁰_{b c}` (`FibreMap`):

* `FibreMap.comap Φ pr` precomposes with a reindexing `pr : ι' → ι` of the inputs, so that one fibre
  map can be evaluated with repeated inputs.
* `FibreMap.fibreDeriv Φ k` is the iterated fibre derivative
  `G_k(λ, t, x; ζ, η₁, …, η_k) = D^k_ζ F(λ, t, x, ζ)[η₁, …, η_k]`, a fibre map on the inputs
  `ι ⊕ (Fin k × ι)` (`blkRanks b b k`), defined for `ζ ∈ dom` and arbitrary `η`, and multilinear in
  the blocks `η_l` (`fibreDeriv_smul`).

**Coordinates.** The derivative is taken in the norm-model coordinates of the fibres (`fibL`,
`prodL`), which need no trivialization (`modelRep`). Read in the trivializations at `x₀`, the
fibre map becomes `rep x₀`, which differs from `modelRep` by linear changes of coordinates on both
sides (`rep_eq_comp`). Hence the derivative of `F` read at `x₀` is the coordinate derivative of
`rep x₀` (`rep_fibreDeriv`), whose smoothness follows from the smoothness of partial derivatives on
sets which are open in the fibre direction (`contMDiffOn_fderiv_fibre`,
`contMDiffOn_iteratedFDeriv_fibre`).
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set Filter Topology
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Analysis.Sobolev
open scoped Manifold ContDiff

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

variable {ι : Type*} [Fintype ι]

/-! ### Smoothness of partial derivatives in the fibre direction -/

section Partial

variable {Λ : Type*} [NormedAddCommGroup Λ] [NormedSpace ℝ Λ]
variable {Z Y : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y]

/-- **Partial derivatives in the fibre variable are smooth** on a set which is open in the fibre
direction: `{q ∈ U | P(λ, t, x)}` with `U` open. -/
theorem contMDiffOn_fderiv_fibre {f : Λ × ℝ × M × Z → Y} {U : Set (Λ × ℝ × M × Z)}
    (hU : IsOpen U) {P : Λ → ℝ → M → Prop}
    (hf : ContMDiffOn (𝓘(ℝ, Λ).prod (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, Z)))) 𝓘(ℝ, Y) ∞ f
      {q | q ∈ U ∧ P q.1 q.2.1 q.2.2.1}) :
    ContMDiffOn (𝓘(ℝ, Λ).prod (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, Z)))) 𝓘(ℝ, Z →L[ℝ] Y) ∞
      (fun q => fderiv ℝ (fun z => f (q.1, q.2.1, q.2.2.1, z)) q.2.2.2)
      {q | q ∈ U ∧ P q.1 q.2.1 q.2.2.1} := by
  intro q₀ hq₀
  set S := {q : Λ × ℝ × M × Z | q ∈ U ∧ P q.1 q.2.1 q.2.2.1} with hS
  let Θ : (Λ × ℝ × M × Z) × Z → Λ × ℝ × M × Z := fun p => (p.1.1, p.1.2.1, p.1.2.2.1, p.2)
  have hΘc : Continuous Θ :=
    (continuous_fst.comp continuous_fst).prodMk
      ((continuous_fst.comp (continuous_snd.comp continuous_fst)).prodMk
        ((continuous_fst.comp (continuous_snd.comp (continuous_snd.comp continuous_fst))).prodMk
          continuous_snd))
  obtain ⟨A, B, hA, hqA, hB, hzB, hAB⟩ :=
    mem_nhds_prod_iff'.mp ((hU.preimage hΘc).mem_nhds (show Θ (q₀, q₀.2.2.2) ∈ U from hq₀.1))
  have hgc : Continuous (fun q : Λ × ℝ × M × Z => q.2.2.2) :=
    continuous_snd.comp (continuous_snd.comp continuous_snd)
  set t := S ∩ A ∩ (fun q : Λ × ℝ × M × Z => q.2.2.2) ⁻¹' B with ht_def
  have ht : t ∈ 𝓝[S] q₀ :=
    inter_mem (inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds (hA.mem_nhds hqA)))
      (mem_nhdsWithin_of_mem_nhds (hgc.continuousAt.preimage_mem_nhds (hB.mem_nhds hzB)))
  have hq₀t : q₀ ∈ t := ⟨⟨hq₀, hqA⟩, hzB⟩
  have hΘs : ContMDiff ((𝓘(ℝ, Λ).prod (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, Z)))).prod 𝓘(ℝ, Z))
      (𝓘(ℝ, Λ).prod (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, Z)))) ∞ Θ :=
    (contMDiff_fst.comp contMDiff_fst).prodMk
      ((contMDiff_fst.comp (contMDiff_snd.comp contMDiff_fst)).prodMk
        ((contMDiff_fst.comp (contMDiff_snd.comp (contMDiff_snd.comp contMDiff_fst))).prodMk
          contMDiff_snd))
  have hmaps : MapsTo Θ (t ×ˢ B) S := by
    rintro ⟨n, z⟩ ⟨hn, hz⟩
    exact ⟨hAB (mk_mem_prod hn.1.2 hz), hn.1.1.2⟩
  have hf' : ContMDiffWithinAt ((𝓘(ℝ, Λ).prod (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, Z)))).prod 𝓘(ℝ, Z))
      𝓘(ℝ, Y) ∞ (Function.uncurry fun (n : Λ × ℝ × M × Z) (z : Z) => f (n.1, n.2.1, n.2.2.1, z))
      (t ×ˢ B) (q₀, q₀.2.2.2) :=
    (hf _ (hmaps ⟨hq₀t, hzB⟩)).comp (q₀, q₀.2.2.2)
      hΘs.contMDiffAt.contMDiffWithinAt hmaps
  have hg : ContMDiffWithinAt (𝓘(ℝ, Λ).prod (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, Z)))) 𝓘(ℝ, Z) ∞
      (fun q : Λ × ℝ × M × Z => q.2.2.2) t q₀ :=
    (contMDiff_snd.comp (contMDiff_snd.comp contMDiff_snd)).contMDiffAt.contMDiffWithinAt
  have key := ContMDiffWithinAt.mfderivWithin (t := t) (u := B) hf' hg hq₀t (fun n hn => hn.2)
    (by simp) hB.uniqueMDiffOn
  refine (key.congr (fun n hn => ?_) ?_).mono_of_mem_nhdsWithin ht
  · simp +unfoldPartialApp only [inTangentCoordinates]
    rw [mfderivWithin_eq_fderivWithin, fderivWithin_of_isOpen hB hn.2]
    erw [inCoordinates_tangent_bundle_core_model_space]
  · simp +unfoldPartialApp only [inTangentCoordinates]
    rw [mfderivWithin_eq_fderivWithin, fderivWithin_of_isOpen hB hq₀t.2]
    erw [inCoordinates_tangent_bundle_core_model_space]

set_option synthInstance.maxHeartbeats 200000 in
/-- **Iterated partial derivatives in the fibre variable are smooth** on a set which is open in the
fibre direction. -/
theorem contMDiffOn_iteratedFDeriv_fibre {f : Λ × ℝ × M × Z → Y} {U : Set (Λ × ℝ × M × Z)}
    (hU : IsOpen U) {P : Λ → ℝ → M → Prop}
    (hf : ContMDiffOn (𝓘(ℝ, Λ).prod (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, Z)))) 𝓘(ℝ, Y) ∞ f
      {q | q ∈ U ∧ P q.1 q.2.1 q.2.2.1}) (k : ℕ) :
    ContMDiffOn (𝓘(ℝ, Λ).prod (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, Z))))
      𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin k => Z) Y) ∞
      (fun q => iteratedFDeriv ℝ k (fun z => f (q.1, q.2.1, q.2.2.1, z)) q.2.2.2)
      {q | q ∈ U ∧ P q.1 q.2.1 q.2.2.1} := by
  induction k with
  | zero =>
    have h := ((continuousMultilinearCurryFin0 ℝ Z Y).symm.contDiff (n := ∞)).contMDiff.comp_contMDiffOn hf
    refine h.congr fun q _ => ?_
    rw [iteratedFDeriv_zero_eq_comp]
    rfl
  | succ k ih =>
    have h1 := contMDiffOn_fderiv_fibre hU ih
    have h2 := ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => Z) Y).symm.contDiff
      (n := ∞)).contMDiff.comp_contMDiffOn h1
    refine h2.congr fun q _ => ?_
    rw [iteratedFDeriv_succ_eq_comp_left]
    rfl

/-- Evaluation of continuous multilinear maps is smooth. -/
theorem contDiff_multilinear_eval {k : ℕ} :
    ContDiff ℝ ∞ (fun p : ContinuousMultilinearMap ℝ (fun _ : Fin k => Z) Y × (Fin k → Z) =>
      p.1 p.2) :=
  ((ContinuousLinearMap.id ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin k => Z) Y)).analyticOnNhd_uncurry_of_multilinear
    (s := univ)).contDiff

end Partial

/-- Iterated derivatives commute with continuous linear equivalences on the right. -/
theorem iteratedFDeriv_comp_cle_right {Z Z' Y : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup Z'] [NormedSpace ℝ Z'] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (B : Z' ≃L[ℝ] Z) (f : Z → Y) (z : Z') (k : ℕ) :
    iteratedFDeriv ℝ k (f ∘ B) z =
      (iteratedFDeriv ℝ k f (B z)).compContinuousLinearMap fun _ => (B : Z' →L[ℝ] Z) := by
  have h := B.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ (mem_univ (B z)) k
  rwa [preimage_univ, iteratedFDerivWithin_univ, iteratedFDerivWithin_univ] at h

/-! ### Fibres in model coordinates -/

variable (I) in
/-- The fibre `T⁰_n|_x` is linearly isomorphic to the model space (no trivialization needed). -/
def fibL (n : ℕ) (x : M) : TensorRSSpace 0 n I x ≃ₗ[ℝ] TensorRSModel 0 n ℝ E :=
  (tensorRSSpaceContinuousLinearEquiv (𝕜 := ℝ) (I := I) 0 n x).toLinearEquiv

variable (I) in
/-- The fibre of `⊕_c T⁰_{b c}` at `x` in model coordinates. -/
def prodL (b : ι → ℕ) (x : M) : ProdFiber I b x ≃ₗ[ℝ] ProdModel E b :=
  LinearEquiv.piCongrRight fun c => fibL I (b c) x

/-- The coordinates in the trivializations at `x₀`, as a linear equivalence over `prodBase`. -/
def prodEquiv {b : ι → ℕ} {b' : ℕ} {x₀ y : M} (hy : y ∈ prodBase (I := I) b b' x₀) :
    ProdFiber I b y ≃ₗ[ℝ] ProdModel E b where
  toFun := prodTriv b x₀ y
  invFun := prodOfModel b x₀ y
  map_add' ζ η := by
    funext c
    simp only [prodTriv, Pi.add_apply, map_add]
  map_smul' a ζ := by
    funext c
    simp only [prodTriv, Pi.smul_apply, map_smul, RingHom.id_apply]
  left_inv ζ := FibreMap.prodOfModel_prodTriv hy ζ
  right_inv z := by
    funext c
    exact (trivAt I M 0 (b c) x₀).continuousLinearMapAt_symmL (mem_iInter.mp hy.2 c) (z c)

theorem prodEquiv_symm_apply {b : ι → ℕ} {b' : ℕ} {x₀ y : M} (hy : y ∈ prodBase (I := I) b b' x₀)
    (z : ProdModel E b) : (prodEquiv hy).symm z = prodOfModel b x₀ y z := rfl

/-! ### Blocks of inputs -/

section Blocks

variable {κ ι₀ : Type*} [Fintype κ] [Fintype ι₀]

/-- The ranks of a tuple `ζ` indexed by `κ` followed by `k` blocks `η_l` indexed by `ι₀`. -/
abbrev blkRanks (a : κ → ℕ) (b₀ : ι₀ → ℕ) (k : ℕ) : κ ⊕ (Fin k × ι₀) → ℕ :=
  Sum.elim a fun q => b₀ q.2

variable {a : κ → ℕ} {b₀ : ι₀ → ℕ} {k : ℕ}

/-- The leading tuple of a point of `⊕ T⁰` with blocks. -/
def fbase {x : M} (V : ProdFiber I (blkRanks a b₀ k) x) : ProdFiber I a x := fun c => V (.inl c)

/-- The `l`-th block of a point of `⊕ T⁰` with blocks. -/
def fblk {x : M} (V : ProdFiber I (blkRanks a b₀ k) x) (l : Fin k) : ProdFiber I b₀ x :=
  fun c => V (.inr (l, c))

/-- The leading tuple, in model coordinates. -/
def mbase (z : ProdModel E (blkRanks a b₀ k)) : ProdModel E a := fun c => z (.inl c)

/-- The `l`-th block, in model coordinates. -/
def mblk (z : ProdModel E (blkRanks a b₀ k)) (l : Fin k) : ProdModel E b₀ :=
  fun c => z (.inr (l, c))

/-- Scale the blocks of a point of `⊕ T⁰` with blocks. -/
def scaleBlk {x : M} (s : Fin k → ℝ) (V : ProdFiber I (blkRanks a b₀ k) x) :
    ProdFiber I (blkRanks a b₀ k) x
  | .inl c => V (.inl c)
  | .inr q => s q.1 • V (.inr q)

@[simp] theorem fbase_scaleBlk {x : M} (s : Fin k → ℝ) (V : ProdFiber I (blkRanks a b₀ k) x) :
    fbase (scaleBlk s V) = fbase V := rfl

@[simp] theorem fblk_scaleBlk {x : M} (s : Fin k → ℝ) (V : ProdFiber I (blkRanks a b₀ k) x)
    (l : Fin k) : fblk (scaleBlk s V) l = s l • fblk V l := rfl

theorem fbase_prodOfModel (x₀ y : M) (z : ProdModel E (blkRanks a b₀ k)) :
    fbase (prodOfModel (I := I) (blkRanks a b₀ k) x₀ y z) = prodOfModel a x₀ y (mbase z) := rfl

theorem fblk_prodOfModel (x₀ y : M) (z : ProdModel E (blkRanks a b₀ k)) (l : Fin k) :
    fblk (prodOfModel (I := I) (blkRanks a b₀ k) x₀ y z) l = prodOfModel b₀ x₀ y (mblk z l) := rfl

theorem contDiff_mbase : ContDiff ℝ ∞ (mbase (E := E) (a := a) (b₀ := b₀) (k := k)) :=
  contDiff_pi.mpr fun c => (ContinuousLinearMap.proj (R := ℝ)
    (φ := fun q => TensorRSModel 0 (blkRanks a b₀ k q) ℝ E) (Sum.inl c)).contDiff

theorem contDiff_mblk :
    ContDiff ℝ ∞ (fun z : ProdModel E (blkRanks a b₀ k) => fun l => mblk z l) :=
  contDiff_pi.mpr fun l => contDiff_pi.mpr fun c => (ContinuousLinearMap.proj (R := ℝ)
    (φ := fun q => TensorRSModel 0 (blkRanks a b₀ k q) ℝ E) (Sum.inr (l, c))).contDiff

end Blocks

theorem prodBase_blkRanks (b : ι → ℕ) (b' k : ℕ) (x₀ : M) :
    prodBase (I := I) (blkRanks b b k) b' x₀ = prodBase (I := I) b b' x₀ := by
  ext y
  simp only [prodBase, mem_inter_iff, mem_iInter]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁, fun c => h₂ (.inl c)⟩
  · rintro ⟨h₁, h₂⟩
    refine ⟨h₁, fun q => ?_⟩
    rcases q with c | ⟨l, c⟩
    · exact h₂ c
    · exact h₂ c

namespace FibreMap

variable {Λ : Type*} [NormedAddCommGroup Λ] [NormedSpace ℝ Λ] {b : ι → ℕ} {b' : ℕ}

/-! ### Local representatives -/

/-- `F` read in the trivializations at `x₀`. -/
def rep (Φ : FibreMap I M Λ b b') (x₀ : M) (q : Λ × ℝ × M × ProdModel E b) :
    TensorRSModel 0 b' ℝ E :=
  (trivAt I M 0 b' x₀).continuousLinearMapAt ℝ q.2.2.1
    (Φ.F q.1 q.2.1 q.2.2.1 (prodOfModel b x₀ q.2.2.1 q.2.2.2))

/-- The domain read in the trivializations at `x₀`. -/
def domSet (Φ : FibreMap I M Λ b b') (x₀ : M) : Set (Λ × ℝ × M × ProdModel E b) :=
  {q ∈ prodSlab (I := I) Λ b b' Φ.T₀ x₀ | prodOfModel b x₀ q.2.2.1 q.2.2.2 ∈ Φ.dom q.1 q.2.1 q.2.2.1}

theorem smooth_rep (Φ : FibreMap I M Λ b b') (x₀ : M) :
    ContMDiffOn (𝓘(ℝ, Λ).prod (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, ProdModel E b))))
      𝓘(ℝ, TensorRSModel 0 b' ℝ E) ∞ (Φ.rep x₀) (Φ.domSet x₀) :=
  Φ.smooth x₀

/-- The domain read at `x₀` is `{q ∈ U | t ∈ [0,T₀], y ∈ prodBase}` with `U` open. -/
theorem exists_domSet_eq (Φ : FibreMap I M Λ b b') (x₀ : M) :
    ∃ U : Set (Λ × ℝ × M × ProdModel E b), IsOpen U ∧
      Φ.domSet x₀ = {q | q ∈ U ∧ (q.2.1 ∈ Icc 0 Φ.T₀ ∧ q.2.2.1 ∈ prodBase (I := I) b b' x₀)} := by
  obtain ⟨U, hU, hdom⟩ := Φ.dom_relOpen x₀
  refine ⟨U, hU, ?_⟩
  rw [domSet, hdom]
  rfl

/-- `F` at `x` in the model coordinates of the fibres. -/
def modelRep (Φ : FibreMap I M Λ b b') (lam : Λ) (t : ℝ) (x : M) (z : ProdModel E b) :
    TensorRSModel 0 b' ℝ E :=
  fibL I b' x (Φ.F lam t x ((prodL I b x).symm z))

/-- The change from model coordinates to the trivialization at `x₀` on the target, linearly. -/
def chgAₗ {x₀ y : M} (hy : y ∈ prodBase (I := I) b b' x₀) :
    TensorRSModel 0 b' ℝ E ≃ₗ[ℝ] TensorRSModel 0 b' ℝ E where
  toFun w := (trivAt I M 0 b' x₀).continuousLinearMapAt ℝ y ((fibL I b' y).symm w)
  invFun v := fibL I b' y ((trivAt I M 0 b' x₀).symmL ℝ y v)
  map_add' v w := by simp only [map_add]
  map_smul' a v := by simp only [map_smul, RingHom.id_apply]
  left_inv w := by
    simp only [Trivialization.symmL_continuousLinearMapAt _ hy.1, LinearEquiv.apply_symm_apply]
  right_inv v := by
    simp only [LinearEquiv.symm_apply_apply, Trivialization.continuousLinearMapAt_symmL _ hy.1]

/-- The change from model coordinates to the trivialization at `x₀` on the target. -/
def chgA {x₀ y : M} (hy : y ∈ prodBase (I := I) b b' x₀) :
    TensorRSModel 0 b' ℝ E ≃L[ℝ] TensorRSModel 0 b' ℝ E :=
  (chgAₗ hy).toContinuousLinearEquiv

/-- The change from the trivializations at `x₀` to model coordinates on the source. -/
def chgB {x₀ y : M} (hy : y ∈ prodBase (I := I) b b' x₀) : ProdModel E b ≃L[ℝ] ProdModel E b :=
  ((prodEquiv hy).symm.trans (prodL I b y)).toContinuousLinearEquiv

theorem chgA_apply {x₀ y : M} (hy : y ∈ prodBase (I := I) b b' x₀) (w : TensorRSModel 0 b' ℝ E) :
    chgA hy w = (trivAt I M 0 b' x₀).continuousLinearMapAt ℝ y ((fibL I b' y).symm w) := rfl

theorem chgB_apply {x₀ y : M} (hy : y ∈ prodBase (I := I) b b' x₀) (z : ProdModel E b) :
    chgB hy z = prodL I b y (prodOfModel b x₀ y z) := rfl

/-- **Change of coordinates**: the representative at `x₀` is the model representative composed
with linear equivalences. -/
theorem rep_eq_comp (Φ : FibreMap I M Λ b b') {x₀ y : M} (hy : y ∈ prodBase (I := I) b b' x₀)
    (lam : Λ) (t : ℝ) :
    (fun z => Φ.rep x₀ (lam, t, y, z)) = chgA hy ∘ Φ.modelRep lam t y ∘ chgB hy := by
  funext z
  simp only [Function.comp_apply, chgA_apply, chgB_apply, modelRep, rep,
    LinearEquiv.symm_apply_apply]

/-- The iterated derivative of the representative at `x₀`, in model coordinates. -/
theorem iteratedFDeriv_rep (Φ : FibreMap I M Λ b b') {x₀ y : M}
    (hy : y ∈ prodBase (I := I) b b' x₀) (lam : Λ) (t : ℝ) (k : ℕ) (z : ProdModel E b)
    (v : Fin k → ProdModel E b) :
    iteratedFDeriv ℝ k (fun z => Φ.rep x₀ (lam, t, y, z)) z v =
      chgA hy (iteratedFDeriv ℝ k (Φ.modelRep lam t y) (chgB hy z) fun l => chgB hy (v l)) := by
  rw [rep_eq_comp Φ hy, ContinuousLinearEquiv.iteratedFDeriv_comp_left,
    iteratedFDeriv_comp_cle_right]
  rfl

/-! ### Reindexing -/

section Comap

variable {ι' : Type*} [Fintype ι']

/-- **Reindexing**: `Φ.comap pr` takes `ζ` to `F(λ, t, x, (ζ_{pr c'})_{c'})`. -/
def comap (pr : ι' → ι) (Φ : FibreMap I M Λ (b ∘ pr) b') : FibreMap I M Λ b b' where
  T₀ := Φ.T₀
  dom lam t x := {ζ | (fun c' => ζ (pr c')) ∈ Φ.dom lam t x}
  F lam t x ζ := Φ.F lam t x fun c' => ζ (pr c')
  dom_relOpen x₀ := by
    obtain ⟨U, hU, hdom⟩ := Φ.dom_relOpen x₀
    refine ⟨{q | (q.1, q.2.1, q.2.2.1, fun c' => q.2.2.2 (pr c')) ∈ U}, ?_, ?_⟩
    · refine hU.preimage (continuous_fst.prodMk (continuous_snd.fst.prodMk
        (continuous_snd.snd.fst.prodMk ?_)))
      exact continuous_pi fun c' => (continuous_apply (pr c')).comp continuous_snd.snd.snd
    · ext q
      have hb : q.2.2.1 ∈ prodBase (I := I) b b' x₀ → q.2.2.1 ∈ prodBase (I := I) (b ∘ pr) b' x₀ :=
        fun h => ⟨h.1, mem_iInter.mpr fun c' => mem_iInter.mp h.2 (pr c')⟩
      have h := congrArg (fun S => ((q.1, q.2.1, q.2.2.1, fun c' => q.2.2.2 (pr c')) :
        Λ × ℝ × M × ProdModel E (b ∘ pr)) ∈ S) hdom
      simp only [prodSlab, mem_inter_iff, mem_ofPred_eq, eq_iff_iff] at h
      simp only [prodSlab, mem_inter_iff, mem_ofPred_eq]
      constructor
      · rintro ⟨⟨ht, hy⟩, hd⟩
        exact ⟨(h.mp ⟨⟨ht, hb hy⟩, hd⟩).1, ht, hy⟩
      · rintro ⟨hU', ht, hy⟩
        exact ⟨⟨ht, hy⟩, (h.mpr ⟨hU', ht, hb hy⟩).2⟩
  smooth x₀ := by
    have hσ : ContMDiff (𝓘(ℝ, Λ).prod (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, ProdModel E b))))
        (𝓘(ℝ, Λ).prod (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, ProdModel E (b ∘ pr))))) ∞
        (fun q : Λ × ℝ × M × ProdModel E b =>
          ((q.1, q.2.1, q.2.2.1, fun c' => q.2.2.2 (pr c')) : Λ × ℝ × M × ProdModel E (b ∘ pr))) := by
      refine contMDiff_fst.prodMk (contMDiff_fst.comp contMDiff_snd |>.prodMk
        ((contMDiff_fst.comp (contMDiff_snd.comp contMDiff_snd)).prodMk ?_))
      have hl : ContDiff ℝ ∞ (fun z : ProdModel E b => (fun c' => z (pr c') : ProdModel E (b ∘ pr))) :=
        contDiff_pi.mpr fun c' => (ContinuousLinearMap.proj (R := ℝ)
          (φ := fun c => TensorRSModel 0 (b c) ℝ E) (pr c')).contDiff
      exact hl.contMDiff.comp (contMDiff_snd.comp (contMDiff_snd.comp contMDiff_snd))
    refine (Φ.smooth x₀).comp hσ.contMDiffOn ?_
    rintro q ⟨⟨ht, hy⟩, hd⟩
    exact ⟨⟨ht, hy.1, mem_iInter.mpr fun c' => mem_iInter.mp hy.2 (pr c')⟩, hd⟩

@[simp] theorem comap_F (pr : ι' → ι) (Φ : FibreMap I M Λ (b ∘ pr) b') (lam : Λ) (t : ℝ) (x : M)
    (ζ : ProdFiber I b x) : (Φ.comap pr).F lam t x ζ = Φ.F lam t x fun c' => ζ (pr c') := rfl

@[simp] theorem comap_dom (pr : ι' → ι) (Φ : FibreMap I M Λ (b ∘ pr) b') (lam : Λ) (t : ℝ) (x : M) :
    (Φ.comap pr).dom lam t x = {ζ | (fun c' => ζ (pr c')) ∈ Φ.dom lam t x} := rfl

end Comap

/-! ### Iterated fibre derivatives -/

/-- `D^k_ζ F(λ, t, x, ζ)[η₁, …, η_k]`, computed in the model coordinates of the fibres. -/
def derivF (Φ : FibreMap I M Λ b b') (k : ℕ) (lam : Λ) (t : ℝ) (x : M)
    (V : ProdFiber I (blkRanks b b k) x) : TensorRSSpace 0 b' I x :=
  (fibL I b' x).symm (iteratedFDeriv ℝ k (Φ.modelRep lam t x) (prodL I b x (fbase V))
    fun l => prodL I b x (fblk V l))

/-- **The fibre derivative read at `x₀` is the coordinate derivative of the representative.** -/
theorem rep_derivF (Φ : FibreMap I M Λ b b') (k : ℕ) {x₀ y : M}
    (hy : y ∈ prodBase (I := I) b b' x₀) (lam : Λ) (t : ℝ) (z : ProdModel E (blkRanks b b k)) :
    (trivAt I M 0 b' x₀).continuousLinearMapAt ℝ y
        (Φ.derivF k lam t y (prodOfModel (blkRanks b b k) x₀ y z)) =
      iteratedFDeriv ℝ k (fun z' => Φ.rep x₀ (lam, t, y, z')) (mbase z) (mblk z) := by
  rw [iteratedFDeriv_rep Φ hy, chgA_apply]
  simp only [chgB_apply]
  rfl

theorem derivF_scaleBlk (Φ : FibreMap I M Λ b b') (k : ℕ) (lam : Λ) (t : ℝ) (x : M)
    (s : Fin k → ℝ) (V : ProdFiber I (blkRanks b b k) x) :
    Φ.derivF k lam t x (scaleBlk s V) = (∏ l, s l) • Φ.derivF k lam t x V := by
  simp only [derivF, fbase_scaleBlk, fblk_scaleBlk, map_smul]
  rw [ContinuousMultilinearMap.map_smul_univ, map_smul]

/-- **The iterated fibre derivative** `G_k(λ, t, x; ζ, η) = D^k_ζ F(λ, t, x, ζ)[η₁, …, η_k]` as a
fibre map on `ι ⊕ (Fin k × ι)`, on the domain `ζ ∈ dom`. -/
def fibreDeriv (Φ : FibreMap I M Λ b b') (k : ℕ) : FibreMap I M Λ (blkRanks b b k) b' where
  T₀ := Φ.T₀
  dom lam t x := {V | fbase V ∈ Φ.dom lam t x}
  F := Φ.derivF k
  dom_relOpen x₀ := by
    obtain ⟨U, hU, hdom⟩ := Φ.dom_relOpen x₀
    refine ⟨{q | (q.1, q.2.1, q.2.2.1, mbase q.2.2.2) ∈ U}, ?_, ?_⟩
    · exact hU.preimage (continuous_fst.prodMk (continuous_snd.fst.prodMk
        (continuous_snd.snd.fst.prodMk ((contDiff_mbase (E := E) (a := b) (b₀ := b) (k := k)).continuous.comp
          continuous_snd.snd.snd))))
    · ext q
      have h := congrArg (fun S => ((q.1, q.2.1, q.2.2.1, mbase q.2.2.2) :
        Λ × ℝ × M × ProdModel E b) ∈ S) hdom
      simp only [prodSlab, mem_inter_iff, mem_ofPred_eq, eq_iff_iff] at h
      simp only [prodSlab, mem_inter_iff, mem_ofPred_eq, prodBase_blkRanks, fbase_prodOfModel]
      constructor
      · rintro ⟨hs, hd⟩
        exact ⟨(h.mp ⟨hs, hd⟩).1, hs⟩
      · rintro ⟨hU', hs⟩
        exact ⟨hs, (h.mpr ⟨hU', hs⟩).2⟩
  smooth x₀ := by
    obtain ⟨U, hU, hS⟩ := Φ.exists_domSet_eq x₀
    have hsm := Φ.smooth_rep x₀
    rw [hS] at hsm
    have hD := contMDiffOn_iteratedFDeriv_fibre (f := Φ.rep x₀)
      (P := fun _ t y => t ∈ Icc 0 Φ.T₀ ∧ y ∈ prodBase (I := I) b b' x₀) hU hsm k
    rw [← hS] at hD
    have hσ : ContMDiff (𝓘(ℝ, Λ).prod (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, ProdModel E (blkRanks b b k)))))
        (𝓘(ℝ, Λ).prod (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, ProdModel E b)))) ∞
        (fun q : Λ × ℝ × M × ProdModel E (blkRanks b b k) =>
          ((q.1, q.2.1, q.2.2.1, mbase q.2.2.2) : Λ × ℝ × M × ProdModel E b)) :=
      contMDiff_fst.prodMk (contMDiff_fst.comp contMDiff_snd |>.prodMk
        ((contMDiff_fst.comp (contMDiff_snd.comp contMDiff_snd)).prodMk
          ((contDiff_mbase (E := E) (a := b) (b₀ := b) (k := k)).contMDiff.comp (contMDiff_snd.comp (contMDiff_snd.comp contMDiff_snd)))))
    have hmaps : MapsTo (fun q : Λ × ℝ × M × ProdModel E (blkRanks b b k) =>
          ((q.1, q.2.1, q.2.2.1, mbase q.2.2.2) : Λ × ℝ × M × ProdModel E b))
        {q ∈ prodSlab (I := I) Λ (blkRanks b b k) b' Φ.T₀ x₀ |
          prodOfModel (blkRanks b b k) x₀ q.2.2.1 q.2.2.2 ∈
            {V | fbase V ∈ Φ.dom q.1 q.2.1 q.2.2.1}}
        (Φ.domSet x₀) := by
      rintro q ⟨⟨ht, hy⟩, hd⟩
      rw [prodBase_blkRanks] at hy
      exact ⟨⟨ht, hy⟩, hd⟩
    have h1 := hD.comp hσ.contMDiffOn hmaps
    have h2 : ContMDiff (𝓘(ℝ, Λ).prod (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, ProdModel E (blkRanks b b k)))))
        𝓘(ℝ, Fin k → ProdModel E b) ∞
        (fun q : Λ × ℝ × M × ProdModel E (blkRanks b b k) => fun l => mblk q.2.2.2 l) :=
      (contDiff_mblk (E := E) (a := b) (b₀ := b) (k := k)).contMDiff.comp
        (contMDiff_snd.comp (contMDiff_snd.comp contMDiff_snd))
    have h3 := contDiff_multilinear_eval.contMDiff.comp_contMDiffOn
      (h1.prodMk_space h2.contMDiffOn)
    refine h3.congr fun q hq => ?_
    have hy : q.2.2.1 ∈ prodBase (I := I) b b' x₀ := by
      have := hq.1.2
      rwa [prodBase_blkRanks] at this
    exact rep_derivF Φ k hy q.1 q.2.1 q.2.2.2

@[simp] theorem fibreDeriv_F (Φ : FibreMap I M Λ b b') (k : ℕ) :
    (Φ.fibreDeriv k).F = Φ.derivF k := rfl

@[simp] theorem fibreDeriv_dom (Φ : FibreMap I M Λ b b') (k : ℕ) (lam : Λ) (t : ℝ) (x : M) :
    (Φ.fibreDeriv k).dom lam t x = {V | fbase V ∈ Φ.dom lam t x} := rfl

/-- The fibre derivative is multilinear in the blocks. -/
theorem fibreDeriv_smul (Φ : FibreMap I M Λ b b') (k : ℕ) (lam : Λ) (t : ℝ) (x : M)
    (s : Fin k → ℝ) (V : ProdFiber I (blkRanks b b k) x) :
    (Φ.fibreDeriv k).F lam t x (scaleBlk s V) = (∏ l, s l) • (Φ.fibreDeriv k).F lam t x V :=
  Φ.derivF_scaleBlk k lam t x s V

end FibreMap

end ShortTime
