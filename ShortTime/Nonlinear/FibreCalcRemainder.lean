import ShortTime.Nonlinear.FibreCalcTaylor
import ShortTime.Linear.TimeCalc

/-!
# Taylor's formula for fibre maps and the remainder bound (bound (T) of `prop:nemytskii`)

* `derivF_taylor` (fibre level): for `t ∈ [0, T₀]` and a segment `ζ + [0,1] η` in the domain,
  `G_k(ζ + η)[η⃗] - G_k(ζ)[η⃗] - G_{k+1}(ζ)[η, η⃗] = Q_k(ζ, η; η, η, η⃗)`.
* `derivFam_taylor` (families): the same identity for `g_k(u)(h⃗) = D^k_ζ F(t, u)[h⃗]` on `[0,T]`.
* `exists_taylor_bound` (**bound (T)**): near a smooth reference `w`,
  `‖g_k(u + h)(h⃗) - g_k(u)(h⃗) - g_{k+1}(u)(h, h⃗)‖²_{𝒫^N} ≤ C ‖h‖⁴_{𝒫^N} ∏_l ‖h_l‖²_{𝒫^N}`.
  It is the bound (M) (`exists_block_bound`) for the Taylor remainder `Q_k`, which is multilinear in
  its `k + 2` blocks, evaluated at `(u, h; h, h, h⃗)`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set Filter Topology MeasureTheory
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev DifferentialGeometry.Analysis.Elliptic
open scoped Manifold ContDiff BigOperators

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

variable {ι : Type*} [Fintype ι] {b : ι → ℕ}

/-! ### Points and families with blocks -/

section Points

variable {κ ι₀ : Type*} [Fintype κ] [Fintype ι₀] {a : κ → ℕ} {b₀ : ι₀ → ℕ} {k : ℕ}

/-- A point `ζ` followed by `k` blocks `η_l`. -/
def joinPt {x : M} (ζ : ProdFiber I a x) (η : Fin k → ProdFiber I b₀ x) :
    ProdFiber I (blkRanks a b₀ k) x
  | .inl c => ζ c
  | .inr q => η q.1 q.2

@[simp] theorem fbase_joinPt {x : M} (ζ : ProdFiber I a x) (η : Fin k → ProdFiber I b₀ x) :
    fbase (joinPt ζ η) = ζ := rfl

@[simp] theorem fblk_joinPt {x : M} (ζ : ProdFiber I a x) (η : Fin k → ProdFiber I b₀ x)
    (l : Fin k) : fblk (joinPt ζ η) l = η l := rfl

/-- A pair of points. -/
def pairPt {x : M} (ζ η : ProdFiber I b x) : ProdFiber I (pairRanks b) x
  | .inl c => ζ c
  | .inr c => η c

@[simp] theorem pfst_pairPt {x : M} (ζ η : ProdFiber I b x) : pfst (pairPt ζ η) = ζ := rfl

@[simp] theorem psnd_pairPt {x : M} (ζ η : ProdFiber I b x) : psnd (pairPt ζ η) = η := rfl

variable {g : SmoothRiemannianMetric I M}

theorem valAt_joinFam (u : ∀ c : κ, ℝ → SmoothCcTensor g 0 (a c))
    (h : Fin k → ∀ c : ι₀, ℝ → SmoothCcTensor g 0 (b₀ c)) (t : ℝ) (x : M) :
    FibreMap.valAt (fun q => joinFam u h q t) x =
      joinPt (FibreMap.valAt (fun c => u c t) x) fun l => FibreMap.valAt (fun c => h l c t) x := by
  funext q
  rcases q with c | ⟨l, c⟩ <;> rfl

/-- A pair of tuples of families. -/
def pairFam (u h : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c)) :
    ∀ q : ι ⊕ ι, ℝ → SmoothCcTensor g 0 (pairRanks b q)
  | .inl c => u c
  | .inr c => h c

theorem valAt_pairFam (u h : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c)) (t : ℝ) (x : M) :
    FibreMap.valAt (fun q => pairFam u h q t) x =
      pairPt (FibreMap.valAt (fun c => u c t) x) (FibreMap.valAt (fun c => h c t) x) := by
  funext q
  rcases q with c | c <;> rfl

theorem jointlySmoothOn_pairFam {S : Set ℝ} {u h : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c)}
    (hu : ∀ c, JointlySmoothOn g 0 (b c) S (u c)) (hh : ∀ c, JointlySmoothOn g 0 (b c) S (h c)) :
    ∀ q, JointlySmoothOn g 0 (pairRanks b q) S (pairFam u h q)
  | .inl c => hu c
  | .inr c => hh c

end Points

theorem fun_fin_cons {X X' : Type*} (f : X → X') {k : ℕ} (a : X) (v : Fin k → X) :
    (fun l => f ((Fin.cons a v : Fin (k + 1) → X) l)) =
      (Fin.cons (f a) (fun l => f (v l)) : Fin (k + 1) → X') := by
  funext l
  refine Fin.cases ?_ (fun i => ?_) l <;> simp

variable {g : SmoothRiemannianMetric I M}

theorem toSection_sub_apply {a : ℕ} (S S' : SmoothCcTensor g 0 a) (x : M) :
    (S - S').toSection x = S.toSection x - S'.toSection x := by
  rw [SmoothCcTensor.toSection_sub]
  rfl

theorem toSection_add_apply {a : ℕ} (S S' : SmoothCcTensor g 0 a) (x : M) :
    (S + S').toSection x = S.toSection x + S'.toSection x := by
  rw [SmoothCcTensor.toSection_add]
  rfl

theorem toSection_zero_apply {a : ℕ} (x : M) : (0 : SmoothCcTensor g 0 a).toSection x = 0 := by
  rw [SmoothCcTensor.toSection_zero]
  rfl

/-- `‖φ‖_{𝒫^N}` only depends on `φ` on `[0,T]`. -/
theorem parabolicInner_congr_self {a : ℕ} {T : ℝ} (hT : 0 < T) {u v : ℝ → SmoothCcTensor g 0 a}
    (hu : JointlySmoothOn g 0 a (Icc 0 T) u) (hv : JointlySmoothOn g 0 a (Icc 0 T) v)
    (h : EqOn u v (Icc 0 T)) (p N : ℕ) :
    parabolicInner g a p N T u u = parabolicInner g a p N T v v := by
  rw [parabolicInner_self_eq hT hu, parabolicInner_self_eq hT hv]
  refine Finset.sum_congr rfl fun j _ => intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le hT.le] at ht
  simp only [timeDerivIter_congr hT hu hv h j ht]

namespace FibreMap

variable {Λ : Type*} [NormedAddCommGroup Λ] [NormedSpace ℝ Λ] {b' : ℕ}

/-! ### Smoothness of the model representative -/

/-- In model coordinates, the slice of the domain is open and `F` is smooth on it. -/
theorem modelRep_contDiffOn (Φ : FibreMap I M Λ b b') (lam : Λ) {t : ℝ} (ht : t ∈ Icc 0 Φ.T₀)
    (x : M) :
    IsOpen {z : ProdModel E b | (prodL I b x).symm z ∈ Φ.dom lam t x} ∧
      ContDiffOn ℝ ∞ (Φ.modelRep lam t x) {z | (prodL I b x).symm z ∈ Φ.dom lam t x} := by
  have hx : x ∈ prodBase (I := I) b b' x := mem_prodBase_self b b' x
  have hU := (Φ.dom_relOpen x).choose_spec.1
  set U := (Φ.dom_relOpen x).choose with hU_def
  have hsym : ∀ z, (prodL I b x).symm z = prodOfModel b x x ((chgB hx).symm z) := by
    intro z
    have e := chgB_apply hx ((chgB hx).symm z)
    rw [ContinuousLinearEquiv.apply_symm_apply] at e
    conv_lhs => rw [e]
    exact LinearEquiv.symm_apply_apply _ _
  have hmem : ∀ z, (prodL I b x).symm z ∈ Φ.dom lam t x ↔ (lam, t, x, (chgB hx).symm z) ∈ U := by
    intro z
    rw [hsym]
    exact Φ.mem_relOpen_iff x (q := (lam, t, x, (chgB hx).symm z)) ⟨ht, hx⟩
  have hι : Continuous fun z' : ProdModel E b => ((lam, t, x, z') : Λ × ℝ × M × ProdModel E b) :=
    continuous_const.prodMk (continuous_const.prodMk (continuous_const.prodMk continuous_id))
  have hS' : IsOpen {z' : ProdModel E b | (lam, t, x, z') ∈ U} := hU.preimage hι
  have hset : {z : ProdModel E b | (prodL I b x).symm z ∈ Φ.dom lam t x} =
      (chgB hx).symm ⁻¹' {z' | (lam, t, x, z') ∈ U} := by
    ext z
    exact hmem z
  refine ⟨hset ▸ hS'.preimage (chgB hx).symm.continuous, ?_⟩
  have hιs : ContMDiff 𝓘(ℝ, ProdModel E b) (𝓘(ℝ, Λ).prod (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, ProdModel E b))))
      ∞ fun z' : ProdModel E b => ((lam, t, x, z') : Λ × ℝ × M × ProdModel E b) :=
    contMDiff_const.prodMk (contMDiff_const.prodMk (contMDiff_const.prodMk contMDiff_id))
  have hrep : ContDiffOn ℝ ∞ (fun z' => Φ.rep x (lam, t, x, z')) {z' | (lam, t, x, z') ∈ U} := by
    refine contMDiffOn_iff_contDiffOn.mp ((Φ.smooth_rep x).comp hιs.contMDiffOn ?_)
    intro z' hz'
    exact ⟨⟨ht, hx⟩, (Φ.mem_relOpen_iff x (q := (lam, t, x, z')) ⟨ht, hx⟩).mpr hz'⟩
  have h2 := (chgA hx).symm.contDiff.comp_contDiffOn
    (hrep.comp (chgB hx).symm.contDiff.contDiffOn (fun z hz => hz))
  rw [hset]
  refine h2.congr fun z _ => ?_
  have e := congrFun (rep_eq_comp Φ hx lam t) ((chgB hx).symm z)
  simp only [Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply] at e
  simp only [Function.comp_apply, e, ContinuousLinearEquiv.symm_apply_apply]

/-! ### Taylor's formula for fibre maps -/

/-- **Taylor's formula for fibre maps**:
`G_k(ζ + η)[η⃗] - G_k(ζ)[η⃗] - G_{k+1}(ζ)[η, η⃗] = Q_k(ζ, η; η, η, η⃗)`. -/
theorem derivF_taylor (Φ : FibreMap I M Λ b b') (k : ℕ) (lam : Λ) {t : ℝ} (ht : t ∈ Icc 0 Φ.T₀)
    (x : M) (ζ η : ProdFiber I b x) (hseg : ∀ τ ∈ Icc (0 : ℝ) 1, ζ + τ • η ∈ Φ.dom lam t x)
    (ηs : Fin k → ProdFiber I b x) :
    Φ.derivF k lam t x (joinPt (ζ + η) ηs) - Φ.derivF k lam t x (joinPt ζ ηs) -
        Φ.derivF (k + 1) lam t x (joinPt ζ (Fin.cons η ηs)) =
      Φ.taylorF k lam t x (joinPt (pairPt ζ η) (Fin.cons η (Fin.cons η ηs))) := by
  obtain ⟨hO, hf⟩ := Φ.modelRep_contDiffOn lam ht x
  apply (fibL I b' x).injective
  simp only [map_sub, derivF, taylorF, LinearEquiv.apply_symm_apply, fbase_joinPt, fblk_joinPt,
    pfst_pairPt, psnd_pairPt, map_add]
  rw [fun_fin_cons (prodL I b x), fun_fin_cons (prodL I b x), fun_fin_cons (prodL I b x)]
  refine taylor_iteratedFDeriv hO hf (fun τ hτ => ?_) k _
  show (prodL I b x).symm (prodL I b x ζ + τ • prodL I b x η) ∈ Φ.dom lam t x
  rw [← map_smul, ← map_add, LinearEquiv.symm_apply_apply]
  exact hseg τ hτ

/-! ### Families -/

/-- `Q_k(u, h; h₁, …, h_{k+2})` at the level of families. -/
def taylorFam (Φ : FibreMap I M Λ b b') (k : ℕ) (lam : Λ) (u h : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c))
    (hs : Fin (k + 2) → ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c)) : ℝ → SmoothCcTensor g 0 b' :=
  (Φ.taylorMap k).apply lam (joinFam (pairFam u h) hs)

theorem jointlySmoothOn_taylorFam (Φ : FibreMap I M Λ b b') (k : ℕ) (lam : Λ) {T : ℝ}
    (hTT : T ≤ Φ.T₀) {u h : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c)}
    (hu : ∀ c, JointlySmoothOn g 0 (b c) (Icc 0 T) (u c))
    (hh : ∀ c, JointlySmoothOn g 0 (b c) (Icc 0 T) (h c))
    (hseg : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, ∀ τ ∈ Icc (0 : ℝ) 1,
      valAt (fun c => u c t) x + τ • valAt (fun c => h c t) x ∈ Φ.dom lam t x)
    {hs : Fin (k + 2) → ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c)}
    (hhs : ∀ l c, JointlySmoothOn g 0 (b c) (Icc 0 T) (hs l c)) :
    (∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, (Φ.taylorFam k lam u h hs t).toSection x =
      Φ.taylorF k lam t x (valAt (fun q => joinFam (pairFam u h) hs q t) x)) ∧
    JointlySmoothOn g 0 b' (Icc 0 T) (Φ.taylorFam k lam u h hs) := by
  have hj := (Φ.taylorMap k).jointlySmoothOn_fibreApply lam hTT
    (jointlySmoothOn_joinFam (jointlySmoothOn_pairFam hu hh) hhs)
    (fun t ht x => hseg t ht x)
  exact ⟨fun t ht x => apply_toSection _ lam _ t (hj.1 t ht) x, hj.2⟩

/-- **Taylor's formula for the families** `g_k(u)(h⃗) = D^k_ζ F(t, u)[h⃗]` on `[0,T]`:
`g_k(u + h)(h⃗) - g_k(u)(h⃗) - g_{k+1}(u)(h, h⃗) = Q_k(u, h; h, h, h⃗)`. -/
theorem derivFam_taylor (Φ : FibreMap I M Λ b b') (k : ℕ) (lam : Λ) {T : ℝ} (hTT : T ≤ Φ.T₀)
    {u h : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c)}
    (hu : ∀ c, JointlySmoothOn g 0 (b c) (Icc 0 T) (u c))
    (hh : ∀ c, JointlySmoothOn g 0 (b c) (Icc 0 T) (h c))
    (hseg : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, ∀ τ ∈ Icc (0 : ℝ) 1,
      valAt (fun c => u c t) x + τ • valAt (fun c => h c t) x ∈ Φ.dom lam t x)
    {hs : Fin k → ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c)}
    (hhs : ∀ l c, JointlySmoothOn g 0 (b c) (Icc 0 T) (hs l c)) :
    ∀ t ∈ Icc (0 : ℝ) T,
      Φ.derivFam k lam (fun c τ => u c τ + h c τ) hs t - Φ.derivFam k lam u hs t -
          Φ.derivFam (k + 1) lam u (Fin.cons h hs) t =
        Φ.taylorFam k lam u h (Fin.cons h (Fin.cons h hs)) t := by
  intro t ht
  have huh : ∀ c, JointlySmoothOn g 0 (b c) (Icc 0 T) (fun τ => u c τ + h c τ) := fun c =>
    jointlySmoothOn_add (hu c) (hh c)
  have hconsS : ∀ l c, JointlySmoothOn g 0 (b c) (Icc 0 T)
      ((Fin.cons h hs : Fin (k + 1) → ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c)) l c) := by
    intro l c
    refine Fin.cases ?_ (fun i => ?_) l
    · exact hh c
    · exact hhs i c
  have hconsS2 : ∀ l c, JointlySmoothOn g 0 (b c) (Icc 0 T)
      ((Fin.cons h (Fin.cons h hs) : Fin (k + 2) → ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c)) l c) := by
    intro l c
    refine Fin.cases ?_ (fun i => ?_) l
    · exact hh c
    · exact hconsS i c
  have hdom0 : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, valAt (fun c => u c t) x ∈ Φ.dom lam t x :=
    fun t ht x => by simpa using hseg t ht x 0 ⟨le_rfl, zero_le_one⟩
  have hvadd : ∀ t x, valAt (fun c => u c t + h c t) x =
      valAt (fun c => u c t) x + valAt (fun c => h c t) x := fun t x => by
    funext c
    exact toSection_add_apply _ _ x
  have hdom1 : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      valAt (fun c => u c t + h c t) x ∈ Φ.dom lam t x :=
    fun t ht x => by simpa [hvadd] using hseg t ht x 1 ⟨zero_le_one, le_rfl⟩
  have e1 := (Φ.jointlySmoothOn_derivFam k lam hTT huh hdom1 hhs).1 t ht
  have e2 := (Φ.jointlySmoothOn_derivFam k lam hTT hu hdom0 hhs).1 t ht
  have e3 := (Φ.jointlySmoothOn_derivFam (k + 1) lam hTT hu hdom0 hconsS).1 t ht
  have e4 := (Φ.jointlySmoothOn_taylorFam k lam hTT hu hh hseg hconsS2).1 t ht
  refine smoothCcTensor_eq_of_toSection fun x => ?_
  rw [toSection_sub_apply, toSection_sub_apply, e1, e2, e3, e4, valAt_joinFam, valAt_joinFam,
    valAt_joinFam, valAt_joinFam, valAt_pairFam, hvadd]
  have hc1 : (fun l => valAt (fun c => (Fin.cons h hs : Fin (k + 1) → ∀ c : ι,
      ℝ → SmoothCcTensor g 0 (b c)) l c t) x) =
      Fin.cons (valAt (fun c => h c t) x) (fun l => valAt (fun c => hs l c t) x) := by
    funext l
    refine Fin.cases ?_ (fun i => ?_) l <;> rfl
  have hc2 : (fun l => valAt (fun c => (Fin.cons h (Fin.cons h hs) : Fin (k + 2) → ∀ c : ι,
      ℝ → SmoothCcTensor g 0 (b c)) l c t) x) =
      Fin.cons (valAt (fun c => h c t) x)
        (Fin.cons (valAt (fun c => h c t) x) (fun l => valAt (fun c => hs l c t) x)) := by
    funext l
    refine Fin.cases ?_ (fun i => ?_) l
    · rfl
    · exact congrFun hc1 i
  rw [hc1, hc2]
  exact Φ.derivF_taylor k lam ⟨ht.1, ht.2.trans hTT⟩ x _ _ (hseg t ht x) _

/-! ### Bound (T) -/

/-- **Bound (T)** of `prop:nemytskii`. Near a smooth reference `w` with values in the domain, there
is `δ > 0` such that for every `B` there is `C` with
`‖g_k(u + h)(h⃗) - g_k(u)(h⃗) - g_{k+1}(u)(h, h⃗)‖²_{𝒫^N} ≤ C ‖h‖⁴_{𝒫^N} ∏_l ‖h_l‖²_{𝒫^N}`
for all smooth `u, h` with `|u - w|² ≤ δ`, `|h|² ≤ δ` pointwise, `‖u‖² + ‖h‖² ≤ B` (in `𝒫^N`) and
`u + [0,1] h` in the domain, and all smooth `h_l`. -/
theorem exists_taylor_bound (Φ : FibreMap I M Λ b b') (k : ℕ) (lam : Λ) {T : ℝ} (hT : 0 < T)
    (hTT : T ≤ Φ.T₀) {p N : ℕ} (hp : 1 ≤ p) (hN : Module.finrank ℝ E / (2 * p) + 3 ≤ N)
    [CompleteSpace E]
    {w : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c)} (hw : ∀ c, JointlySmoothOn g 0 (b c) (Icc 0 T) (w c))
    (hwdom : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, valAt (fun c => w c t) x ∈ Φ.dom lam t x) :
    ∃ δ > 0, ∀ B : ℝ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ u h : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c),
        (∀ c, JointlySmoothOn g 0 (b c) (Icc 0 T) (u c)) →
        (∀ c, JointlySmoothOn g 0 (b c) (Icc 0 T) (h c)) →
        (∀ c, ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 0 (b c) x ((u c t - w c t).toSection x) ≤ δ) →
        (∀ c, ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 0 (b c) x ((h c t).toSection x) ≤ δ) →
        ∑ c, parabolicInner g (b c) p N T (u c) (u c) +
          ∑ c, parabolicInner g (b c) p N T (h c) (h c) ≤ B →
        (∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, ∀ τ ∈ Icc (0 : ℝ) 1,
          valAt (fun c => u c t) x + τ • valAt (fun c => h c t) x ∈ Φ.dom lam t x) →
        ∀ hs : Fin k → ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c),
          (∀ l c, JointlySmoothOn g 0 (b c) (Icc 0 T) (hs l c)) →
          parabolicInner g b' p N T
              (fun t => Φ.derivFam k lam (fun c τ => u c τ + h c τ) hs t -
                Φ.derivFam k lam u hs t - Φ.derivFam (k + 1) lam u (Fin.cons h hs) t)
              (fun t => Φ.derivFam k lam (fun c τ => u c τ + h c τ) hs t -
                Φ.derivFam k lam u hs t - Φ.derivFam (k + 1) lam u (Fin.cons h hs) t) ≤
            C * (∑ c, parabolicInner g (b c) p N T (h c) (h c)) ^ 2 *
              ∏ l, ∑ c, parabolicInner g (b c) p N T (hs l c) (hs l c) := by
  have hz : ∀ c, JointlySmoothOn g 0 (b c) (Icc 0 T) (fun _ : ℝ => (0 : SmoothCcTensor g 0 (b c))) :=
    fun c => jointlySmoothOn_const g _ (0 : SmoothCcTensor g 0 (b c))
  obtain ⟨δ, hδ, hB⟩ := exists_block_bound (isBlockMultilinear_taylorMap Φ k) lam hT hTT hp hN
    (w := pairFam w fun _ _ => 0) (jointlySmoothOn_pairFam hw hz) (fun t ht x τ _ => by
      have e : psnd (fbase (valAt (fun q => joinFam (pairFam w fun _ _ => 0)
          (zeroBlk (g := g) (b₀ := b) (k := k + 2)) q t) x)) = 0 := by
        funext c
        exact toSection_zero_apply x
      show pfst (fbase _) + τ • psnd (fbase _) ∈ Φ.dom lam t x
      rw [e, smul_zero, add_zero]
      exact hwdom t ht x)
  refine ⟨δ, hδ, fun B => ?_⟩
  obtain ⟨C, hC0, hC⟩ := hB B
  refine ⟨C, hC0, ?_⟩
  intro u h hu hh hut hht huB hseg hs hhs
  have hconsS : ∀ l c, JointlySmoothOn g 0 (b c) (Icc 0 T)
      ((Fin.cons h hs : Fin (k + 1) → ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c)) l c) := by
    intro l c
    refine Fin.cases ?_ (fun i => ?_) l
    · exact hh c
    · exact hhs i c
  have hconsS2 : ∀ l c, JointlySmoothOn g 0 (b c) (Icc 0 T)
      ((Fin.cons h (Fin.cons h hs) : Fin (k + 2) → ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c)) l c) := by
    intro l c
    refine Fin.cases ?_ (fun i => ?_) l
    · exact hh c
    · exact hconsS i c
  have hQ := hC (pairFam u h) (jointlySmoothOn_pairFam hu hh)
    (by
      rintro (c | c) t ht x
      · exact hut c t ht x
      · change riemannianFiberNormSq (I := I) (M := M) g 0 (b c) x ((h c t - 0).toSection x) ≤ δ
        rw [sub_zero]
        exact hht c t ht x)
    (by rw [Fintype.sum_sum_type]; exact huB)
    (fun t ht x τ hτ => hseg t ht x τ hτ)
    (Fin.cons h (Fin.cons h hs)) hconsS2
  -- the remainder agrees with `Q_k` on `[0,T]`
  have hdom0 : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, valAt (fun c => u c t) x ∈ Φ.dom lam t x :=
    fun t ht x => by simpa using hseg t ht x 0 ⟨le_rfl, zero_le_one⟩
  have hvadd : ∀ t x, valAt (fun c => u c t + h c t) x =
      valAt (fun c => u c t) x + valAt (fun c => h c t) x := fun t x => by
    funext c
    exact toSection_add_apply _ _ x
  have hdom1 : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      valAt (fun c => u c t + h c t) x ∈ Φ.dom lam t x :=
    fun t ht x => by simpa [hvadd] using hseg t ht x 1 ⟨zero_le_one, le_rfl⟩
  have huh : ∀ c, JointlySmoothOn g 0 (b c) (Icc 0 T) (fun τ => u c τ + h c τ) := fun c =>
    jointlySmoothOn_add (hu c) (hh c)
  have hR : JointlySmoothOn g 0 b' (Icc 0 T)
      (fun t => Φ.derivFam k lam (fun c τ => u c τ + h c τ) hs t -
        Φ.derivFam k lam u hs t - Φ.derivFam (k + 1) lam u (Fin.cons h hs) t) :=
    jointlySmoothOn_sub (jointlySmoothOn_sub
      (Φ.jointlySmoothOn_derivFam k lam hTT huh hdom1 hhs).2
      (Φ.jointlySmoothOn_derivFam k lam hTT hu hdom0 hhs).2)
      (Φ.jointlySmoothOn_derivFam (k + 1) lam hTT hu hdom0 hconsS).2
  rw [parabolicInner_congr_self hT hR (Φ.jointlySmoothOn_taylorFam k lam hTT hu hh hseg hconsS2).2
    (fun t ht => Φ.derivFam_taylor k lam hTT hu hh hseg hhs t ht) p N]
  refine hQ.trans (le_of_eq ?_)
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  ring

end FibreMap

end ShortTime
