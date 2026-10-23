import ShortTime.Linear.PermField

/-!
# Inserting a vector field into the first slot

For a smooth vector field `B`, `insField g B : T⁰_{a+1} → T⁰_a` is the operator field
`D ↦ D(B, ·)`. With it, the covariant derivative along `B` is `∇_B W = (insField B)(∇W)`, so it is
an operator of order `1` in the `IsDiffOp` calculus.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Tensor.Multilinear
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open scoped Manifold ContDiff

set_option linter.unusedSectionVars false

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

variable (I) in
/-- Fibrewise insertion `T⁰_{a+1}|_x → T⁰_a|_x`, `D ↦ D(v, ·)`. -/
def insFib {a : ℕ} (x : M) (v : TangentSpace I x) :
    Tensor0SSpace (a + 1) I x →L[ℝ] Tensor0SSpace a I x :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace (a + 1) I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun D => Tensor0SSpace.ofModel ((Tensor0SSpace.toModel D).curryLeft (tangentSpaceModelContinuousLinearEquiv (I := I) x v))
      map_add' := fun D₁ D₂ => by
        apply Tensor0SSpace.toModel_injective
        simp only [Tensor0SSpace.toModel_add, Tensor0SSpace.toModel_ofModel]
        ext m
        rfl
      map_smul' := fun c D => by
        apply Tensor0SSpace.toModel_injective
        simp only [Tensor0SSpace.toModel_smul, Tensor0SSpace.toModel_ofModel, RingHom.id_apply]
        ext m
        rfl }

theorem toModel_insFib {a : ℕ} {x : M} (v : TangentSpace I x) (D : Tensor0SSpace (a + 1) I x) :
    Tensor0SSpace.toModel (insFib I x v D) =
      (Tensor0SSpace.toModel D).curryLeft (tangentSpaceModelContinuousLinearEquiv (I := I) x v) :=
  Tensor0SSpace.toModel_ofModel _

theorem contMDiff_insFib_apply {a : ℕ} (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Y : Cₛ^∞⟮I; Tensor0SModel a.succ ℝ E, fun x : M => Tensor0SSpace a.succ I x⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel a ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel a ℝ E) (E := fun z : M => Tensor0SSpace a I z) x
        (insFib I x (B x) (Y x))) := by
  classical
  refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
    (fun x => (insFib I x (B x) (Y x) : Tensor0SSpace a I x))).mpr ?_
  have hS := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
    (fun x => (Y x : Tensor0SSpace (a + 1) I x))).mp Y.contMDiff
  intro τ x₀
  set e := trivializationAt E (TangentSpace I : M → Type _) x₀ with he
  set b := Module.finBasis ℝ E
  -- the coordinates of `B` in the trivialization at `x₀`
  have hw : ContMDiffAt I 𝓘(ℝ, E) ∞ (fun x => (e ⟨x, B x⟩).2) x₀ :=
    ((contMDiffAt_section x₀).mp B.contMDiff.contMDiffAt)
  have hc : ∀ k, ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun x => b.repr (e ⟨x, B x⟩).2 k) x₀ := fun k =>
    (LinearMap.toContinuousLinearMap (b.coord k)).contMDiffAt.comp x₀ hw
  have hsum : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun x => ∑ k, b.repr (e ⟨x, B x⟩).2 k *
        (Tensor.Multilinear.continuousMultilinearMapBasis b (a + 1)).repr
          (trivializationAt (Tensor0SModel (a + 1) ℝ E)
            (_root_.Bundle.continuousMultilinearMap ℝ (a + 1) E (TangentSpace I : M → Type _)) x₀
            ⟨x, Y x⟩).2 (Fin.cons k τ)) x₀ :=
    ContMDiffAt.sum fun k _ => (hc k).mul (hS (Fin.cons k τ) x₀)
  refine hsum.congr_of_eventuallyEq ?_
  filter_upwards [e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt E _ x₀)] with x hx
  rw [continuousMultilinearMap_basis_repr]
  simp only [continuousMultilinearMap_basis_repr]
  set ψ : E →L[ℝ] E :=
    (tangentSpaceModelContinuousLinearEquiv (I := I) x).toContinuousLinearMap.comp
      (e.symmL ℝ x) with hψ
  have hB0 : tangentSpaceModelContinuousLinearEquiv (I := I) x (B x) = ψ (e ⟨x, B x⟩).2 := by
    rw [hψ, ContinuousLinearMap.comp_apply, Trivialization.symmL_apply _ hx,
      e.symm_apply_apply_mk hx]
    rfl
  have hB' : tangentSpaceModelContinuousLinearEquiv (I := I) x (B x) =
      ∑ k, b.repr (e ⟨x, B x⟩).2 k • ψ (b k) := by
    rw [hB0]
    conv_lhs => rw [← b.sum_repr (e ⟨x, B x⟩).2]
    rw [map_sum]
    simp only [map_smul]
  have hlin : ∀ (c : Fin (Module.finrank ℝ E) → ℝ) (v : Fin (Module.finrank ℝ E) → E) (rest : Fin a → E),
      Tensor0SSpace.toModel (Y x) (Fin.cons (∑ k, c k • v k) rest) =
        ∑ k, c k * Tensor0SSpace.toModel (Y x) (Fin.cons (v k) rest) := by
    intro c v rest
    rw [← ContinuousMultilinearMap.curryLeft_apply, map_sum]
    simp [ContinuousMultilinearMap.curryLeft_apply]
  change Tensor0SSpace.toModel (insFib I x (B x) (Y x)) (fun j => ψ (b (τ j))) =
    ∑ k, b.repr (e ⟨x, B x⟩).2 k *
      Tensor0SSpace.toModel (Y x) (fun j => ψ (b ((Fin.cons k τ : Fin (a + 1) → Fin _) j)))
  rw [toModel_insFib, ContinuousMultilinearMap.curryLeft_apply, hB', hlin]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 2
  funext j
  refine Fin.cases ?_ (fun j => ?_) j <;> simp

/-- Insertion of the vector field `B` into the first slot, as an operator field `T⁰_{a+1} → T⁰_a`. -/
def insField (g : SmoothRiemannianMetric I M) {a : ℕ}
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) : SmoothCcTensor g (a + 1) a where
  toSection :=
    { toFun := fun x => (show TensorRSSpace (a + 1) a I x from insFib I x (B x))
      contMDiff_toFun := Geometry.Connection.Realization.contMDiff_clm_section_of_pointwise
        (I := I) (M := M)
        (F₁ := Tensor0SModel (a + 1) ℝ E) (V₁ := fun x : M => Tensor0SSpace (a + 1) I x)
        (F₂ := Tensor0SModel a ℝ E) (V₂ := fun x : M => Tensor0SSpace a I x)
        (fun x => insFib I x (B x)) (contMDiff_insFib_apply B) }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

end ShortTime
