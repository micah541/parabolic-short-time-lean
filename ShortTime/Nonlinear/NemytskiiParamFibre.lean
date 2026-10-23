import ShortTime.Nonlinear.Nemytskii

/-!
# A parameter as extra scalar inputs of a fibre map

For the parametric nonlinear operator (`cor:N`, "jointly in `(s,u)`") the parameter `λ ∈ Λ`
(`Λ` finite dimensional) is turned into extra *inputs*: `d = dim Λ` scalar fields (sections of
`T⁰_0 M`, constant in `(t, x)`), the coordinates of `λ` in `Module.finBasis ℝ Λ` times the unit
section. Then the fibre derivatives of the resulting fibre map `FibreMap.paramLift Φ` (with a dummy
parameter) are the joint derivatives in `(λ, ζ)`, and all the bounds proved for fibre maps apply
uniformly in `λ`.

* `scal00`, `unit00`, `unitSec`: the scalar of a `(0,0)`-tensor, the unit, the unit section.
* `scal00_symmL`, `trivAt_unit00`: both read in the trivializations at `x₀`.
* `FibreMap.paramLift`: `Ψ(t, x; ζ, a) = Φ(λ(a), t, x, ζ)`, `λ(a) = Σ_i scal(a_i) e_i`.
* `FibreMap.parFam`: a tuple of families followed by the constant scalar families of `λ`;
  `paramLift_apply_parFam`: `Ψ[parFam λ u] = Φ[λ, u]`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set Filter Topology MeasureTheory Metric
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Spectral DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff BigOperators

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

/-! ### Scalars -/

/-- The scalar of a `(0,0)`-tensor `ξ ∈ Hom(T⁰_0, T⁰_0)`: the number `ξ(1)`. -/
def scal00 (x : M) : TensorRSSpace 0 0 I x →L[ℝ] ℝ :=
  (tensor00Scalar (I := I) (M := M) x).comp
    (ContinuousLinearMap.apply ℝ (Tensor0SSpace 0 I x) (unitZeroSec (I := I) (M := M) x))

/-- The unit `(0,0)`-tensor. -/
def unit00 (x : M) : TensorRSSpace 0 0 I x := ContinuousLinearMap.id ℝ (Tensor0SSpace 0 I x)

variable (E) in
/-- The scalar of a model `(0,0)`-tensor. -/
def scal00M : TensorRSModel 0 0 ℝ E →L[ℝ] ℝ :=
  (scalarM (E := E)).comp (ContinuousLinearMap.apply ℝ (Tensor0SModel 0 ℝ E) (unitM (E := E)))

variable (E) in
/-- The unit model `(0,0)`-tensor. -/
def unit00M : TensorRSModel 0 0 ℝ E := ContinuousLinearMap.id ℝ (Tensor0SModel 0 ℝ E)

theorem tensor00Scalar_unit (x : M) :
    tensor00Scalar (I := I) (M := M) x (unitZeroSec (I := I) (M := M) x) = 1 := by
  rw [tensor00Scalar_apply (I := I) (M := M) x _ (fun k : Fin 0 => k.elim0)]
  rw [show ((unitZeroSec (I := I) (M := M) x) (fun k : Fin 0 => k.elim0) : ℝ) =
      Tensor0SSpace.toModel (unitZeroSec (I := I) (M := M) x) (fun k : Fin 0 => k.elim0) from rfl]
  rw [unitZeroSec_apply (I := I) (M := M) x, Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.constOfIsEmpty_apply]

theorem scal00_unit00 (x : M) : scal00 x (unit00 (I := I) x) = 1 :=
  tensor00Scalar_unit (E := E) (I := I) x

/-- The unit `0`-tensor in the trivialization at `x₀`. -/
theorem symmL_unitM {x₀ y : M} (hy : y ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    letI := tensor0SBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 0
    (trivializationAt (Tensor0SModel 0 ℝ E) (fun x => Tensor0SSpace 0 I x) x₀).symmL ℝ y
      unitM = unitZeroSec (I := I) (M := M) y := by
  let := tensor0SBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 0
  have h : (trivializationAt (Tensor0SModel 0 ℝ E) (fun x => Tensor0SSpace 0 I x)
      x₀).continuousLinearMapAt ℝ y (unitZeroSec (I := I) (M := M) y) = unitM := by
    refine ContinuousMultilinearMap.ext fun w => ?_
    rw [Tensor0SSpace.continuousLinearMapAt_apply (𝕜 := ℝ) (I := I) 0 hy]
    simp [unitM]
    rfl
  rw [← h, (trivializationAt (Tensor0SModel 0 ℝ E) (fun x => Tensor0SSpace 0 I x)
    x₀).symmL_continuousLinearMapAt (R := ℝ) hy]

/-- **The scalar, read in the trivialization at `x₀`**, is the fixed functional `scal00M`. -/
theorem scal00_symmL {x₀ y : M} (hy : y ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (z : TensorRSModel 0 0 ℝ E) :
    scal00 y ((trivAt I M 0 0 x₀).symmL ℝ y z) = scal00M E z := by
  let := tensor0SBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 0
  have hb : y ∈ (trivAt I M 0 0 x₀).baseSet := ⟨hy, hy⟩
  have hz : z = (trivAt I M 0 0 x₀ ⟨y, (trivAt I M 0 0 x₀).symmL ℝ y z⟩).2 := by
    rw [Trivialization.symmL_apply _ hb, Trivialization.apply_mk_symm _ hb]
  have e1 : scal00M E z = (z unitM) (fun k : Fin 0 => k.elim0) := by
    change (continuousMultilinearCurryFin0 ℝ E ℝ) (z unitM) = _
    rw [continuousMultilinearCurryFin0_apply]
    exact congrArg (z unitM) (Subsingleton.elim _ _)
  rw [e1]
  conv_rhs => rw [hz]
  rw [TensorRSSpace.trivializationAt_apply (𝕜 := ℝ) (I := I) 0 0 hy, symmL_unitM hy]
  exact tensor00Scalar_apply (I := I) (M := M) y _ _

/-- **The unit, read in the trivialization at `x₀`**, is constant. -/
theorem trivAt_unit00 {x₀ y : M} (hy : y ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    (trivAt I M 0 0 x₀ ⟨y, unit00 y⟩).2 = unit00M E := by
  let := tensor0SBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 0
  refine ContinuousLinearMap.ext fun β => ContinuousMultilinearMap.ext fun v => ?_
  rw [TensorRSSpace.trivializationAt_apply (𝕜 := ℝ) (I := I) 0 0 hy]
  have hβ := congrArg (fun A : Tensor0SModel 0 ℝ E => A v)
    ((trivializationAt (Tensor0SModel 0 ℝ E) (fun x => Tensor0SSpace 0 I x)
      x₀).continuousLinearMapAt_symmL (R := ℝ) hy β)
  simp only [Tensor0SSpace.continuousLinearMapAt_apply (𝕜 := ℝ) (I := I) 0 hy] at hβ
  exact hβ

theorem contMDiff_unit00 :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 0 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 0 0 ℝ E)
        (E := fun x : M => TensorRSSpace 0 0 I x) x (unit00 x)) := by
  intro x₀
  have hon : ContMDiffOn I (I.prod 𝓘(ℝ, TensorRSModel 0 0 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 0 0 ℝ E)
        (E := fun x : M => TensorRSSpace 0 0 I x) x (unit00 x)) (trivAt I M 0 0 x₀).baseSet := by
    rw [(trivAt I M 0 0 x₀).contMDiffOn_iff fun y hy => (trivAt I M 0 0 x₀).mem_source.mpr hy]
    refine ⟨contMDiffOn_id, (contMDiffOn_const (c := unit00M E)).congr
      fun y hy => ?_⟩
    exact trivAt_unit00 (show y ∈ (trivializationAt E (TangentSpace I) x₀).baseSet ∩
      (trivializationAt E (TangentSpace I) x₀).baseSet from hy).1
  exact (hon x₀ (mem_baseSet_trivializationAt _ _ x₀)).contMDiffAt
    ((trivAt I M 0 0 x₀).open_baseSet.mem_nhds (mem_baseSet_trivializationAt _ _ x₀))

variable (I) in
/-- The unit section of `T⁰_0 M`. -/
def unitSec (g : SmoothRiemannianMetric I M) : SmoothCcTensor g 0 0 where
  toSection := { toFun := fun x => unit00 x
                 contMDiff_toFun := contMDiff_unit00 }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

theorem unitSec_toSection (g : SmoothRiemannianMetric I M) (x : M) :
    (unitSec I g).toSection x = unit00 x := rfl

/-! ### The parameter as scalar inputs -/

section Param

variable {ι : Type*} [Fintype ι] {b : ι → ℕ} {b' : ℕ}
variable {Λ : Type*} [NormedAddCommGroup Λ] [NormedSpace ℝ Λ] [FiniteDimensional ℝ Λ]

/-- The ranks of a tuple followed by `d` scalar inputs. -/
abbrev parRanks (b : ι → ℕ) (d : ℕ) : ι ⊕ Fin d → ℕ := Sum.elim b fun _ => 0

/-- The leading tuple. -/
def pbase {d : ℕ} {x : M} (V : ProdFiber I (parRanks b d) x) : ProdFiber I b x :=
  fun c => V (.inl c)

/-- The scalar inputs. -/
def ppar {d : ℕ} {x : M} (V : ProdFiber I (parRanks b d) x) : Fin d → TensorRSSpace 0 0 I x :=
  fun i => V (.inr i)

/-- The leading tuple, in model coordinates. -/
def mpbase {d : ℕ} (z : ProdModel E (parRanks b d)) : ProdModel E b := fun c => z (.inl c)

/-- The scalar inputs, in model coordinates. -/
def mppar {d : ℕ} (z : ProdModel E (parRanks b d)) : Fin d → TensorRSModel 0 0 ℝ E :=
  fun i => z (.inr i)

variable (Λ) in
/-- The parameter carried by scalar inputs: `Σ_i scal(a_i) e_i`. -/
def lamOf {x : M} (a : Fin (Module.finrank ℝ Λ) → TensorRSSpace 0 0 I x) : Λ :=
  ∑ i, scal00 x (a i) • Module.finBasis ℝ Λ i

variable (E Λ) in
/-- The parameter carried by scalar inputs in model coordinates. -/
def lamOfM : (Fin (Module.finrank ℝ Λ) → TensorRSModel 0 0 ℝ E) →L[ℝ] Λ :=
  ∑ i, ((scal00M E).comp (ContinuousLinearMap.proj i)).smulRight (Module.finBasis ℝ Λ i)

theorem lamOfM_apply (z : Fin (Module.finrank ℝ Λ) → TensorRSModel 0 0 ℝ E) :
    lamOfM E Λ z = ∑ i, scal00M E (z i) • Module.finBasis ℝ Λ i := by
  simp [lamOfM]

theorem mem_tangent_of_prodBase {x₀ y : M} (hy : y ∈ prodBase (I := I) b b' x₀) :
    y ∈ (trivializationAt E (TangentSpace I) x₀).baseSet :=
  (show y ∈ (trivializationAt E (TangentSpace I) x₀).baseSet ∩
    (trivializationAt E (TangentSpace I) x₀).baseSet from hy.1).1

theorem prodBase_of_parRanks {d : ℕ} {x₀ y : M} (hy : y ∈ prodBase (I := I) (parRanks b d) b' x₀) :
    y ∈ prodBase (I := I) b b' x₀ :=
  ⟨hy.1, mem_iInter.2 fun c => mem_iInter.1 hy.2 (.inl c)⟩

theorem lamOf_prodOfModel {x₀ y : M}
    (hy : y ∈ prodBase (I := I) (parRanks b (Module.finrank ℝ Λ)) b' x₀)
    (z : ProdModel E (parRanks b (Module.finrank ℝ Λ))) :
    lamOf Λ (ppar (prodOfModel (I := I) (parRanks b (Module.finrank ℝ Λ)) x₀ y z)) = lamOfM E Λ (mppar z) := by
  have ht := mem_tangent_of_prodBase hy
  rw [lamOfM_apply, lamOf]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  exact scal00_symmL ht (z (.inr i))

theorem contDiff_lamOfM_mppar :
    ContDiff ℝ ∞ (fun z : ProdModel E (parRanks b (Module.finrank ℝ Λ)) => lamOfM E Λ (mppar z)) :=
  (lamOfM E Λ).contDiff.comp (contDiff_pi.mpr fun i => (ContinuousLinearMap.proj (R := ℝ)
    (φ := fun c => TensorRSModel 0 (parRanks b (Module.finrank ℝ Λ) c) ℝ E) (Sum.inr i)).contDiff)

theorem contDiff_mpbase {d : ℕ} :
    ContDiff ℝ ∞ (fun z : ProdModel E (parRanks b d) => mpbase z) :=
  contDiff_pi.mpr fun c => (ContinuousLinearMap.proj (R := ℝ)
    (φ := fun c => TensorRSModel 0 (parRanks b d c) ℝ E) (Sum.inl c)).contDiff

namespace FibreMap

/-- **The parameter as scalar inputs**: `Ψ(t, x; ζ, a) = Φ(λ(a), t, x, ζ)`, a fibre map on
`⊕_c T⁰_{b c} ⊕ (T⁰_0)^d` with a dummy parameter. -/
def paramLift (Φ : FibreMap I M Λ b b') :
    FibreMap I M ℝ (parRanks b (Module.finrank ℝ Λ)) b' where
  T₀ := Φ.T₀
  dom _ t x := {V | pbase V ∈ Φ.dom (lamOf Λ (ppar V)) t x}
  F _ t x V := Φ.F (lamOf Λ (ppar V)) t x (pbase V)
  dom_relOpen x₀ := by
    obtain ⟨U, hU, hdom⟩ := Φ.dom_relOpen x₀
    refine ⟨{q | (lamOfM E Λ (mppar q.2.2.2), q.2.1, q.2.2.1, mpbase q.2.2.2) ∈ U}, ?_, ?_⟩
    · exact hU.preimage (((contDiff_lamOfM_mppar (E := E) (b := b) (Λ := Λ)).continuous.comp continuous_snd.snd.snd).prodMk
        (continuous_snd.fst.prodMk (continuous_snd.snd.fst.prodMk
          ((contDiff_mpbase (E := E) (b := b) (d := Module.finrank ℝ Λ)).continuous.comp continuous_snd.snd.snd))))
    · ext q
      have h := congrArg (fun S => ((lamOfM E Λ (mppar q.2.2.2), q.2.1, q.2.2.1,
        mpbase q.2.2.2) : Λ × ℝ × M × ProdModel E b) ∈ S) hdom
      simp only [prodSlab, mem_inter_iff, mem_setOf_eq, eq_iff_iff] at h
      simp only [prodSlab, mem_inter_iff, mem_setOf_eq]
      constructor
      · rintro ⟨⟨ht, hy⟩, hd⟩
        have hd' : prodOfModel b x₀ q.2.2.1 (mpbase q.2.2.2) ∈
            Φ.dom (lamOfM E Λ (mppar q.2.2.2)) q.2.1 q.2.2.1 := by
          rw [← lamOf_prodOfModel hy]
          exact hd
        exact ⟨(h.mp ⟨⟨ht, prodBase_of_parRanks hy⟩, hd'⟩).1, ht, hy⟩
      · rintro ⟨hU', ht, hy⟩
        refine ⟨⟨ht, hy⟩, ?_⟩
        have h2 := (h.mpr ⟨hU', ht, prodBase_of_parRanks hy⟩).2
        change pbase (prodOfModel (parRanks b (Module.finrank ℝ Λ)) x₀ q.2.2.1 q.2.2.2) ∈
          Φ.dom (lamOf Λ (ppar (prodOfModel (I := I) (parRanks b (Module.finrank ℝ Λ)) x₀ q.2.2.1
            q.2.2.2))) q.2.1 q.2.2.1
        rw [lamOf_prodOfModel hy]
        exact h2
  smooth x₀ := by
    have hσ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod
          (I.prod 𝓘(ℝ, ProdModel E (parRanks b (Module.finrank ℝ Λ))))))
        (𝓘(ℝ, Λ).prod (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, ProdModel E b)))) ∞
        (fun q : ℝ × ℝ × M × ProdModel E (parRanks b (Module.finrank ℝ Λ)) =>
          ((lamOfM E Λ (mppar q.2.2.2), q.2.1, q.2.2.1, mpbase q.2.2.2) :
            Λ × ℝ × M × ProdModel E b)) :=
      ((contDiff_lamOfM_mppar (E := E) (b := b) (Λ := Λ)).contMDiff.comp (contMDiff_snd.comp (contMDiff_snd.comp
        contMDiff_snd))).prodMk ((contMDiff_fst.comp contMDiff_snd).prodMk
        ((contMDiff_fst.comp (contMDiff_snd.comp contMDiff_snd)).prodMk
          ((contDiff_mpbase (E := E) (b := b) (d := Module.finrank ℝ Λ)).contMDiff.comp (contMDiff_snd.comp (contMDiff_snd.comp
            contMDiff_snd)))))
    refine ((Φ.smooth x₀).comp hσ.contMDiffOn ?_).congr ?_
    · rintro q ⟨⟨ht, hy⟩, hd⟩
      refine ⟨⟨ht, prodBase_of_parRanks hy⟩, ?_⟩
      change prodOfModel b x₀ q.2.2.1 (mpbase q.2.2.2) ∈
        Φ.dom (lamOfM E Λ (mppar q.2.2.2)) q.2.1 q.2.2.1
      rw [← lamOf_prodOfModel hy]
      exact hd
    · rintro q ⟨⟨-, hy⟩, -⟩
      change (trivAt I M 0 b' x₀).continuousLinearMapAt ℝ q.2.2.1
          (Φ.F (lamOf Λ (ppar (prodOfModel (I := I) (parRanks b (Module.finrank ℝ Λ)) x₀ q.2.2.1
            q.2.2.2))) q.2.1 q.2.2.1 (prodOfModel b x₀ q.2.2.1 (mpbase q.2.2.2))) =
        (trivAt I M 0 b' x₀).continuousLinearMapAt ℝ q.2.2.1
          (Φ.F (lamOfM E Λ (mppar q.2.2.2)) q.2.1 q.2.2.1
            (prodOfModel b x₀ q.2.2.1 (mpbase q.2.2.2)))
      rw [lamOf_prodOfModel hy]

@[simp] theorem paramLift_F (Φ : FibreMap I M Λ b b') (μ t : ℝ) (x : M)
    (V : ProdFiber I (parRanks b (Module.finrank ℝ Λ)) x) :
    (paramLift Φ).F μ t x V = Φ.F (lamOf Λ (ppar V)) t x (pbase V) := rfl

@[simp] theorem paramLift_dom (Φ : FibreMap I M Λ b b') (μ t : ℝ) (x : M) :
    (paramLift Φ).dom μ t x = {V | pbase V ∈ Φ.dom (lamOf Λ (ppar V)) t x} := rfl

@[simp] theorem paramLift_T₀ (Φ : FibreMap I M Λ b b') : (paramLift Φ).T₀ = Φ.T₀ := rfl

/-! ### Families -/

variable {g : SmoothRiemannianMetric I M}

variable (Λ) in
/-- The scalar family `t ↦ λ_i · 1` of the `i`-th coordinate of `λ`. -/
def parScal (lam : Λ) (i : Fin (Module.finrank ℝ Λ)) : SmoothCcTensor g 0 0 :=
  (Module.finBasis ℝ Λ).repr lam i • unitSec I g

/-- A tuple of families followed by the coordinates of `λ`, as constant scalar families. -/
def parFam (lam : Λ) (u : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c)) :
    ∀ c : ι ⊕ Fin (Module.finrank ℝ Λ), ℝ →
      SmoothCcTensor g 0 (parRanks b (Module.finrank ℝ Λ) c)
  | .inl c => u c
  | .inr i => fun _ => parScal Λ lam i

theorem jointlySmoothOn_parFam {S : Set ℝ} (lam : Λ) {u : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c)}
    (hu : ∀ c, JointlySmoothOn g 0 (b c) S (u c)) :
    ∀ c, JointlySmoothOn g 0 (parRanks b (Module.finrank ℝ Λ) c) S (parFam lam u c)
  | .inl c => hu c
  | .inr i => jointlySmoothOn_const g S (parScal Λ lam i)

theorem pbase_valAt_parFam (lam : Λ) (u : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c)) (t : ℝ)
    (x : M) : pbase (valAt (fun c => parFam lam u c t) x) = valAt (fun c => u c t) x := rfl

theorem parScal_toSection (lam : Λ) (i : Fin (Module.finrank ℝ Λ)) (x : M) :
    (parScal (g := g) Λ lam i).toSection x = (Module.finBasis ℝ Λ).repr lam i • unit00 x := by
  rw [parScal, toSection_smul_apply]
  rfl

theorem lamOf_valAt_parFam (lam : Λ) (u : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c)) (t : ℝ)
    (x : M) : lamOf Λ (ppar (valAt (fun c => parFam lam u c t) x)) = lam := by
  rw [lamOf]
  have e : ∀ i, scal00 x (ppar (valAt (fun c => parFam lam u c t) x) i) =
      (Module.finBasis ℝ Λ).repr lam i := by
    intro i
    change scal00 x ((parScal (g := g) Λ lam i).toSection x) = _
    rw [parScal_toSection, map_smul, scal00_unit00, smul_eq_mul, mul_one]
  simp_rw [e]
  exact (Module.finBasis ℝ Λ).sum_repr lam

theorem paramLift_F_parFam (Φ : FibreMap I M Λ b b') (μ : ℝ) (lam : Λ)
    (u : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c)) (t : ℝ) (x : M) :
    (paramLift Φ).F μ t x (valAt (fun c => parFam lam u c t) x) =
      Φ.F lam t x (valAt (fun c => u c t) x) := by
  rw [paramLift_F, lamOf_valAt_parFam, pbase_valAt_parFam]

theorem mem_paramLift_dom_parFam (Φ : FibreMap I M Λ b b') (μ : ℝ) (lam : Λ)
    (u : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c)) (t : ℝ) (x : M) :
    valAt (fun c => parFam lam u c t) x ∈ (paramLift Φ).dom μ t x ↔
      valAt (fun c => u c t) x ∈ Φ.dom lam t x := by
  rw [paramLift_dom, mem_setOf_eq, lamOf_valAt_parFam, pbase_valAt_parFam]

/-- `Φ.apply` only depends on the values `x ↦ F(λ, t, x, V(t, x))`. -/
theorem apply_eq_of_F {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] {b₁ : ι₁ → ℕ} {b₂ : ι₂ → ℕ}
    {Λ₁ Λ₂ : Type*} [NormedAddCommGroup Λ₁] [NormedSpace ℝ Λ₁] [NormedAddCommGroup Λ₂]
    [NormedSpace ℝ Λ₂] (Φ₁ : FibreMap I M Λ₁ b₁ b') (Φ₂ : FibreMap I M Λ₂ b₂ b') (lam₁ : Λ₁)
    (lam₂ : Λ₂) (V₁ : ∀ c : ι₁, ℝ → SmoothCcTensor g 0 (b₁ c))
    (V₂ : ∀ c : ι₂, ℝ → SmoothCcTensor g 0 (b₂ c)) (t : ℝ)
    (h : ∀ x : M, Φ₁.F lam₁ t x (valAt (fun c => V₁ c t) x) =
      Φ₂.F lam₂ t x (valAt (fun c => V₂ c t) x)) :
    Φ₁.apply lam₁ V₁ t = Φ₂.apply lam₂ V₂ t := by
  by_cases h2 : ∃ S : SmoothCcTensor g 0 b', ∀ x : M,
      S.toSection x = Φ₂.F lam₂ t x (valAt (fun c => V₂ c t) x)
  · have h1 : ∃ S : SmoothCcTensor g 0 b', ∀ x : M,
        S.toSection x = Φ₁.F lam₁ t x (valAt (fun c => V₁ c t) x) := by
      obtain ⟨S, hS⟩ := h2
      exact ⟨S, fun x => (hS x).trans (h x).symm⟩
    exact smoothCcTensor_eq_of_toSection fun x => by
      rw [apply_toSection _ _ _ _ h1 x, apply_toSection _ _ _ _ h2 x, h x]
  · have h1 : ¬ ∃ S : SmoothCcTensor g 0 b', ∀ x : M,
        S.toSection x = Φ₁.F lam₁ t x (valAt (fun c => V₁ c t) x) := by
      rintro ⟨S, hS⟩
      exact h2 ⟨S, fun x => (hS x).trans (h x)⟩
    simp only [apply, dif_neg h1, dif_neg h2]

/-- **`Ψ[parFam λ u] = Φ[λ, u]`.** -/
theorem paramLift_apply_parFam (Φ : FibreMap I M Λ b b') (μ : ℝ) (lam : Λ)
    (u : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c)) (t : ℝ) :
    (paramLift Φ).apply μ (parFam lam u) t = Φ.apply lam u t :=
  apply_eq_of_F _ _ _ _ _ _ t fun x => paramLift_F_parFam Φ μ lam u t x

/-- The scalar inputs of a sum. -/
theorem valAt_parFam_add (lam lam' : Λ) (u u' : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c))
    (t : ℝ) (x : M) :
    valAt (fun c => parFam (lam + lam') (fun c τ => u c τ + u' c τ) c t) x =
      valAt (fun c => parFam lam u c t) x + valAt (fun c => parFam lam' u' c t) x := by
  funext c
  rcases c with c | i
  · exact toSection_add_apply _ _ x
  · change (parScal (g := g) Λ (lam + lam') i).toSection x =
      (parScal (g := g) Λ lam i).toSection x + (parScal (g := g) Λ lam' i).toSection x
    rw [parScal_toSection, parScal_toSection, parScal_toSection, map_add, Finsupp.add_apply,
      add_smul]

theorem valAt_parFam_smul (a : ℝ) (lam : Λ) (u : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c))
    (t : ℝ) (x : M) :
    valAt (fun c => parFam (a • lam) (fun c τ => a • u c τ) c t) x =
      a • valAt (fun c => parFam lam u c t) x := by
  funext c
  rcases c with c | i
  · exact toSection_smul_apply _ _ x
  · change (parScal (g := g) Λ (a • lam) i).toSection x = a • (parScal (g := g) Λ lam i).toSection x
    rw [parScal_toSection, parScal_toSection, map_smul, Finsupp.smul_apply, smul_eq_mul, smul_smul]

theorem valAt_parFam_congr {lam : Λ} {u u' : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c)} {t : ℝ}
    (h : ∀ c, u c t = u' c t) (x : M) :
    valAt (fun c => parFam lam u c t) x = valAt (fun c => parFam lam u' c t) x := by
  funext c
  rcases c with c | i
  · change (u c t).toSection x = (u' c t).toSection x
    rw [h c]
  · rfl

end FibreMap

end Param

end ShortTime
