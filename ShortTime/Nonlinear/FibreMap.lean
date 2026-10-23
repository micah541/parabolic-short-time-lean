import ShortTime.Nonlinear.LocalRep
import ShortTime.Linear.Parabolic
import ShortTime.Nonlinear.JetSq

/-!
# Smooth fibre maps on products of covariant tensor bundles

The composition estimates (`prop:nemytskii`, `cor:N`) concern maps of the form
`V ↦ Φ[λ, V]`, `Φ[λ, V](t)(x) = F(λ, t, x, V(t, x))`, where `V = (V_c)_{c ∈ ι}` is a tuple of
families of covariant tensor fields of ranks `b c`, and `F` is smooth on a relatively open domain.

* The nonlinearity of an equation is the case `ι = Fin (2p+1)`, `b k = s + k`, `V_k = ∇^k u`.
* Multilinear remainders `G(ζ; η₁, …, η_k)` are the case of several tuples.
* The parameter `λ ∈ Λ` carries the flow parameter of Angenent's trick.

Smoothness of `F` is read in the trivializations at each base point, as for `EquationData`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set Filter Topology
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Elliptic
open scoped Manifold ContDiff

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

variable {ι : Type*} [Fintype ι]

variable (I) in
/-- The fibre at `x` of `⊕_{c ∈ ι} T⁰_{b c} M`. -/
abbrev ProdFiber (b : ι → ℕ) (x : M) : Type _ :=
  ∀ c : ι, TensorRSSpace 0 (b c) I x

variable (E) in
/-- The model fibre of `⊕_{c ∈ ι} T⁰_{b c} M`. -/
abbrev ProdModel (b : ι → ℕ) : Type _ :=
  ∀ c : ι, TensorRSModel 0 (b c) ℝ E

/-- The points over which all the bundles `T⁰_{b c}` and `T⁰_{b'}` are trivialized at `x₀`. -/
def prodBase (b : ι → ℕ) (b' : ℕ) (x₀ : M) : Set M :=
  (trivAt I M 0 b' x₀).baseSet ∩ ⋂ c : ι, (trivAt I M 0 (b c) x₀).baseSet

/-- The point of `⊕_c T⁰_{b c}` over `y` with coordinates `z` in the trivializations at `x₀`. -/
def prodOfModel (b : ι → ℕ) (x₀ y : M) (z : ProdModel E b) : ProdFiber I b y :=
  fun c => (trivAt I M 0 (b c) x₀).symmL ℝ y (z c)

/-- The coordinates of a point of `⊕_c T⁰_{b c}` in the trivializations at `x₀`. -/
def prodTriv (b : ι → ℕ) (x₀ y : M) (ζ : ProdFiber I b y) : ProdModel E b :=
  fun c => (trivAt I M 0 (b c) x₀).continuousLinearMapAt ℝ y (ζ c)

/-- The slab `Λ × [0,T₀] × prodBase × model` in the local coordinates at `x₀`. -/
def prodSlab (Λ : Type*) (b : ι → ℕ) (b' : ℕ) (T₀ : ℝ) (x₀ : M) :
    Set (Λ × ℝ × M × ProdModel E b) :=
  {q | q.2.1 ∈ Icc 0 T₀ ∧ q.2.2.1 ∈ prodBase (I := I) b b' x₀}

variable (I M) in
/-- **A smooth fibre map** `F(λ, t, x, ζ) ∈ T⁰_{b'}` for `λ ∈ Λ`, `t ∈ [0,T₀]` and `ζ ∈ ⊕_c T⁰_{b c}`
in a relatively open domain, smooth jointly in `(λ, t, x, ζ)`. -/
structure FibreMap (Λ : Type*) [NormedAddCommGroup Λ] [NormedSpace ℝ Λ] (b : ι → ℕ) (b' : ℕ) where
  /-- The final time. -/
  T₀ : ℝ
  /-- The domain, fibrewise. -/
  dom : Λ → ℝ → (x : M) → Set (ProdFiber I b x)
  /-- The map. -/
  F : Λ → ℝ → (x : M) → ProdFiber I b x → TensorRSSpace 0 b' I x
  /-- The domain is relatively open in the slab. -/
  dom_relOpen : ∀ x₀ : M, ∃ U : Set (Λ × ℝ × M × ProdModel E b), IsOpen U ∧
    {q ∈ prodSlab (I := I) Λ b b' T₀ x₀ | prodOfModel b x₀ q.2.2.1 q.2.2.2 ∈ dom q.1 q.2.1 q.2.2.1} =
      U ∩ prodSlab (I := I) Λ b b' T₀ x₀
  /-- The map is smooth on its domain, read in the trivializations at each `x₀`. -/
  smooth : ∀ x₀ : M,
    ContMDiffOn (𝓘(ℝ, Λ).prod (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, ProdModel E b))))
      𝓘(ℝ, TensorRSModel 0 b' ℝ E) ∞
      (fun q : Λ × ℝ × M × ProdModel E b => (trivAt I M 0 b' x₀).continuousLinearMapAt ℝ q.2.2.1
        (F q.1 q.2.1 q.2.2.1 (prodOfModel b x₀ q.2.2.1 q.2.2.2)))
      {q ∈ prodSlab (I := I) Λ b b' T₀ x₀ | prodOfModel b x₀ q.2.2.1 q.2.2.2 ∈ dom q.1 q.2.1 q.2.2.1}

namespace FibreMap

variable {Λ : Type*} [NormedAddCommGroup Λ] [NormedSpace ℝ Λ] {b : ι → ℕ} {b' : ℕ}
variable {g : SmoothRiemannianMetric I M}

/-- The values of a tuple of tensor fields at `x`. -/
def valAt (V : ∀ c : ι, SmoothCcTensor g 0 (b c)) (x : M) : ProdFiber I b x :=
  fun c => (V c).toSection x

open Classical in
/-- `Φ[λ, V](t)`: the tensor field `x ↦ F(λ, t, x, V(t, x))` when it is smooth, and `0`
otherwise. -/
def apply (Φ : FibreMap I M Λ b b') (lam : Λ) (V : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c)) (t : ℝ) :
    SmoothCcTensor g 0 b' :=
  if h : ∃ S : SmoothCcTensor g 0 b', ∀ x : M,
      S.toSection x = Φ.F lam t x (valAt (fun c => V c t) x) then h.choose else 0

theorem apply_toSection (Φ : FibreMap I M Λ b b') (lam : Λ)
    (V : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c)) (t : ℝ)
    (h : ∃ S : SmoothCcTensor g 0 b', ∀ x : M,
      S.toSection x = Φ.F lam t x (valAt (fun c => V c t) x)) (x : M) :
    (Φ.apply lam V t).toSection x = Φ.F lam t x (valAt (fun c => V c t) x) := by
  rw [apply, dif_pos h]
  exact h.choose_spec x

theorem prodBase_isOpen (b : ι → ℕ) (b' : ℕ) (x₀ : M) : IsOpen (prodBase (I := I) b b' x₀) :=
  (trivAt I M 0 b' x₀).open_baseSet.inter
    (isOpen_iInter_of_finite fun c => (trivAt I M 0 (b c) x₀).open_baseSet)

theorem mem_prodBase_self (b : ι → ℕ) (b' : ℕ) (x₀ : M) : x₀ ∈ prodBase (I := I) b b' x₀ :=
  ⟨mem_baseSet_trivializationAt _ _ x₀, mem_iInter.2 fun c => mem_baseSet_trivializationAt _ _ x₀⟩

theorem prodOfModel_prodTriv {x₀ y : M} (hy : y ∈ prodBase (I := I) b b' x₀)
    (ζ : ProdFiber I b y) : prodOfModel b x₀ y (prodTriv b x₀ y ζ) = ζ := by
  funext c
  exact Trivialization.symmL_continuousLinearMapAt _ (mem_iInter.mp hy.2 c) (ζ c)

/-- The values of a jointly smooth tuple, read in the trivializations at `x₀`, are smooth. -/
theorem contMDiffOn_prodTriv_valAt {S : Set ℝ} {V : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c)}
    (hV : ∀ c, JointlySmoothOn g 0 (b c) S (V c)) (b' : ℕ) (x₀ : M) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ProdModel E b) ∞
      (fun q : M × ℝ => prodTriv b x₀ q.1 (valAt (fun c => V c q.2) q.1))
      (prodBase (I := I) b b' x₀ ×ˢ S) := by
  rw [contMDiffOn_pi_space]
  intro c
  have hk : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel 0 (b c) ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel 0 (b c) ℝ E)
        (E := fun x : M => TensorRSSpace 0 (b c) I x) q.1 ((V c q.2).toSection q.1))
      (prodBase (I := I) b b' x₀ ×ˢ S) :=
    (hV c).mono (prod_mono (subset_univ _) le_rfl)
  rw [(trivAt I M 0 (b c) x₀).contMDiffOn_iff
    (fun q hq => (trivAt I M 0 (b c) x₀).mem_source.mpr (mem_iInter.mp hq.1.2 c))] at hk
  refine hk.2.congr fun q hq => ?_
  simp only [prodTriv, valAt]
  rw [Trivialization.continuousLinearMapAt_apply,
    Trivialization.coe_linearMapAt_of_mem _ (mem_iInter.mp hq.1.2 c)]

/-- `(x, t) ↦ F(λ, t, x, V(t, x))` is a jointly smooth section on `M × [0,T]`. -/
theorem contMDiffOn_F_valAt (Φ : FibreMap I M Λ b b') (lam : Λ) {T : ℝ} (hT : T ≤ Φ.T₀)
    {V : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c)}
    (hV : ∀ c, JointlySmoothOn g 0 (b c) (Icc 0 T) (V c))
    (hdom : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, valAt (fun c => V c t) x ∈ Φ.dom lam t x) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel 0 b' ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel 0 b' ℝ E)
        (E := fun x : M => TensorRSSpace 0 b' I x) q.1
        (Φ.F lam q.2 q.1 (valAt (fun c => V c q.2) q.1)))
      ((Set.univ : Set M) ×ˢ Icc 0 T) := by
  intro q₀ hq₀
  set x₀ := q₀.1
  have hloc : prodBase (I := I) b b' x₀ ×ˢ Icc 0 T ∈ 𝓝[(univ : Set M) ×ˢ Icc 0 T] q₀ :=
    mem_nhdsWithin.2 ⟨prodBase (I := I) b b' x₀ ×ˢ univ,
      (prodBase_isOpen b b' x₀).prod isOpen_univ, ⟨mem_prodBase_self b b' x₀, mem_univ _⟩,
      fun q hq => ⟨hq.1.1, hq.2.2⟩⟩
  suffices hon : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel 0 b' ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel 0 b' ℝ E)
        (E := fun x : M => TensorRSSpace 0 b' I x) q.1
        (Φ.F lam q.2 q.1 (valAt (fun c => V c q.2) q.1)))
      (prodBase (I := I) b b' x₀ ×ˢ Icc 0 T) from
    (hon q₀ ⟨mem_prodBase_self b b' x₀, hq₀.2⟩).mono_of_mem_nhdsWithin hloc
  rw [(trivAt I M 0 b' x₀).contMDiffOn_iff
    (fun q hq => (trivAt I M 0 b' x₀).mem_source.mpr hq.1.1)]
  refine ⟨contMDiffOn_fst, ?_⟩
  have hψ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (𝓘(ℝ, Λ).prod (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, ProdModel E b)))) ∞
      (fun q : M × ℝ => (lam, q.2, q.1, prodTriv b x₀ q.1 (valAt (fun c => V c q.2) q.1)))
      (prodBase (I := I) b b' x₀ ×ˢ Icc 0 T) :=
    contMDiffOn_const.prodMk (contMDiffOn_snd.prodMk
      (contMDiffOn_fst.prodMk (contMDiffOn_prodTriv_valAt hV b' x₀)))
  have hmaps : MapsTo
      (fun q : M × ℝ => (lam, q.2, q.1, prodTriv b x₀ q.1 (valAt (fun c => V c q.2) q.1)))
      (prodBase (I := I) b b' x₀ ×ˢ Icc 0 T)
      {q ∈ prodSlab (I := I) Λ b b' Φ.T₀ x₀ |
        prodOfModel b x₀ q.2.2.1 q.2.2.2 ∈ Φ.dom q.1 q.2.1 q.2.2.1} := by
    intro q hq
    refine ⟨⟨⟨hq.2.1, hq.2.2.trans hT⟩, hq.1⟩, ?_⟩
    change prodOfModel b x₀ q.1 (prodTriv b x₀ q.1 (valAt (fun c => V c q.2) q.1)) ∈
      Φ.dom lam q.2 q.1
    rw [prodOfModel_prodTriv hq.1]
    exact hdom q.2 hq.2 q.1
  refine ((Φ.smooth x₀).comp hψ hmaps).congr fun q hq => ?_
  change _ = (trivAt I M 0 b' x₀).continuousLinearMapAt ℝ q.1
    (Φ.F lam q.2 q.1 (prodOfModel b x₀ q.1 (prodTriv b x₀ q.1 (valAt (fun c => V c q.2) q.1))))
  rw [prodOfModel_prodTriv hq.1, Trivialization.continuousLinearMapAt_apply,
    Trivialization.coe_linearMapAt_of_mem _ hq.1.1]

/-- **`Φ[λ, V]` is a jointly smooth family** when `V` is, and its values stay in the domain. -/
theorem jointlySmoothOn_fibreApply (Φ : FibreMap I M Λ b b') (lam : Λ) {T : ℝ} (hT : T ≤ Φ.T₀)
    {V : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c)}
    (hV : ∀ c, JointlySmoothOn g 0 (b c) (Icc 0 T) (V c))
    (hdom : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, valAt (fun c => V c t) x ∈ Φ.dom lam t x) :
    (∀ t ∈ Icc (0 : ℝ) T, ∃ S : SmoothCcTensor g 0 b', ∀ x : M,
      S.toSection x = Φ.F lam t x (valAt (fun c => V c t) x)) ∧
    JointlySmoothOn g 0 b' (Icc 0 T) (Φ.apply lam V) := by
  have hj := Φ.contMDiffOn_F_valAt lam hT hV hdom
  have hex : ∀ t ∈ Icc (0 : ℝ) T, ∃ S : SmoothCcTensor g 0 b', ∀ x : M,
      S.toSection x = Φ.F lam t x (valAt (fun c => V c t) x) := by
    intro t ht
    have hs : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 b' ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (TensorRSModel 0 b' ℝ E)
          (E := fun x : M => TensorRSSpace 0 b' I x) x
          (Φ.F lam t x (valAt (fun c => V c t) x))) := by
      intro x
      have hg : ContMDiffWithinAt I (I.prod 𝓘(ℝ, ℝ)) ∞ (fun y : M => (y, t)) univ x :=
        (contMDiffAt_id.prodMk contMDiffAt_const).contMDiffWithinAt
      have h := (hj (x, t) ⟨mem_univ _, ht⟩).comp x hg
        (fun y _ => (⟨mem_univ _, ht⟩ : (y, t) ∈ (univ : Set M) ×ˢ Icc 0 T))
      exact contMDiffWithinAt_univ.mp h
    exact ⟨{ toSection := { toFun := fun x => Φ.F lam t x (valAt (fun c => V c t) x)
                            contMDiff_toFun := hs }
             hasCompactSupport := HasCompactSupport.of_compactSpace _ }, fun x => rfl⟩
  refine ⟨hex, hj.congr fun q hq => ?_⟩
  rw [Φ.apply_toSection lam V q.2 (hex q.2 hq.2) q.1]

/-! The pointwise tame bound `exists_tame_pointwise` is in `ShortTime.Nonlinear.FibreMapTame`. -/

end FibreMap

end ShortTime
