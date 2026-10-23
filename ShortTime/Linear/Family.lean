import ShortTime.Linear.Flip
import ShortTime.Setting.Jet
import DifferentialGeometry.Bundle.ContinuousLinearMapSection.ParametricSmoothness

/-!
# Jointly smooth families of operator fields

The coefficients of a linear operator depend smoothly on `(x, t)`. The constructions of
`ShortTime.Linear.Flip` (the flip) and the library's composition of operator fields preserve this
joint smoothness. Together with the library's `covGrad_iter_joint` and `joint_jet_bdd` this gives
bounds on the coefficients that are uniform in `t ∈ [0, T]`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Spectral DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Geometry.Connection.Realization DifferentialGeometry.TensorMultilinear
open scoped Manifold ContDiff BigOperators

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

variable (g : SmoothRiemannianMetric I M)

/-- Parametric version of `contMDiff_uncurriedSection_of_contMDiff_homSection`: a family of
sections of `Hom(TM, T⁰_n)` that is jointly smooth gives, after uncurrying, a jointly smooth family
of sections of `T⁰_{n+1}`. -/
theorem contMDiffOn_uncurry_param {n : ℕ} {S : Set ℝ}
    (G : ∀ p : M × ℝ, TangentSpace I p.1 →L[ℝ] Tensor0SSpace n I p.1)
    (hG : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel n ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] Tensor0SModel n ℝ E)
        (E := fun y : M => TangentSpace I y →L[ℝ] Tensor0SSpace n I y) p.1 (G p))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel (n + 1) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel (n + 1) ℝ E)
        (E := fun y : M => Tensor0SSpace (n + 1) I y) p.1
        ((tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) n p.1).symm (G p)))
      ((Set.univ : Set M) ×ˢ S) := by
  let : TopologicalSpace (TotalSpace (Tensor0SModel (n + 1) ℝ E)
      (fun y : M => Tensor0SSpace (n + 1) I y)) :=
    tensor0SBundleTopology (n + 1)
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  have hG_at := ((Bundle.contMDiffWithinAt_totalSpace (F := E →L[ℝ] Tensor0SModel n ℝ E)
    (E := fun y : M => TangentSpace I y →L[ℝ] Tensor0SSpace n I y)).mp (hG p₀ hp₀)).2
  have huncurry :
      ContMDiff 𝓘(ℝ, E →L[ℝ] Tensor0SModel n ℝ E) 𝓘(ℝ, Tensor0SModel (n + 1) ℝ E)
        (∞ : WithTop ℕ∞)
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℝ).symm :=
    ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℝ
      ).toContinuousLinearEquiv.symm.toContinuousLinearMap).contMDiff
  have hcomp := huncurry.contMDiffAt.comp_contMDiffWithinAt p₀ hG_at
  have key : ∀ p : M × ℝ, p.1 ∈ (trivializationAt (Tensor0SModel n ℝ E)
      (fun x : M => Tensor0SSpace n I x) p₀.1).baseSet →
      (trivializationAt (Tensor0SModel (n + 1) ℝ E)
        (fun y : M => Tensor0SSpace (n + 1) I y) p₀.1
        ⟨p.1, (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) n p.1).symm (G p)⟩).2 =
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℝ).symm
        ((trivializationAt (E →L[ℝ] Tensor0SModel n ℝ E)
          (fun y : M => TangentSpace I y →L[ℝ] Tensor0SSpace n I y) p₀.1 ⟨p.1, G p⟩).2) := by
    intro p hp
    have h := trivializationAt_homBundle_curriedSection_eq (I := I) (M := M)
      (fun b : M => (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) n b).symm (G (b, p.2))) p₀.1 p.1 hp
    have hc : curriedSection (I := I) (M := M)
        (fun b : M => (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) n b).symm (G (b, p.2))) p.1 =
        G p := ContinuousLinearEquiv.apply_symm_apply _ _
    rw [hc] at h
    rw [h]
    exact (LinearIsometryEquiv.symm_apply_apply
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℝ) _).symm
  refine hcomp.congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S),
        p.1 ∈ (trivializationAt (Tensor0SModel n ℝ E)
          (fun x : M => Tensor0SSpace n I x) p₀.1).baseSet :=
      nhdsWithin_le_nhds (continuousAt_fst.preimage_mem_nhds
        ((trivializationAt (Tensor0SModel n ℝ E) (fun x : M => Tensor0SSpace n I x)
          p₀.1).open_baseSet.mem_nhds (mem_baseSet_trivializationAt _ _ _)))
    filter_upwards [hbase] with p hp
    exact key p hp
  · exact key p₀ (mem_baseSet_trivializationAt _ _ _)

omit [CompleteSpace E] in
/-- A single smooth field is a jointly smooth (constant) family. -/
theorem jointlySmoothOn_const {a b : ℕ} (S : Set ℝ) (A : SmoothCcTensor g a b) :
    JointlySmoothOn g a b S (fun _ => A) := by
  unfold JointlySmoothOn
  have hfst : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞ (Prod.fst : M × ℝ → M)
      ((Set.univ : Set M) ×ˢ S) := contMDiffOn_fst
  exact A.toSection.contMDiff.comp_contMDiffOn hfst

omit [CompleteSpace E] in
/-- Composition of jointly smooth families of operator fields. -/
theorem jointlySmoothOn_comp {a b c : ℕ} {S : Set ℝ}
    {A : ℝ → SmoothCcTensor g b c} {B : ℝ → SmoothCcTensor g a b}
    (hA : JointlySmoothOn g b c S A) (hB : JointlySmoothOn g a b S B) :
    JointlySmoothOn g a c S (fun t => ccOperatorFieldComp (I := I) (M := M) g a b c (A t) (B t)) := by
  apply contMDiffOn_clm_section_of_apply (I := I) (M := M)
    (F₁ := Tensor0SModel a ℝ E) (V₁ := fun x : M => Tensor0SSpace a I x)
    (F₂ := Tensor0SModel c ℝ E) (V₂ := fun x : M => Tensor0SSpace c I x)
    (φ := fun p : M × ℝ =>
      (show Tensor0SSpace a I p.1 →L[ℝ] Tensor0SSpace c I p.1 from
        (ccOperatorFieldComp (I := I) (M := M) g a b c (A p.2) (B p.2)).toSection p.1))
    (S := S)
  intro Y
  have hY : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel a ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel a ℝ E)
        (E := fun x : M => Tensor0SSpace a I x) p.1 (Y p.1))
      ((Set.univ : Set M) ×ˢ S) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hBY := ContMDiffOn.clm_bundle_apply (b := Prod.fst) hB hY
  have hABY := ContMDiffOn.clm_bundle_apply (b := Prod.fst) hA hBY
  refine hABY.congr (fun p _ => ?_)
  rfl

/-- The flip of a jointly smooth family is jointly smooth. -/
theorem jointlySmoothOn_flipField {m n : ℕ} {S : Set ℝ} {A : ℝ → SmoothCcTensor g (m + 1) n}
    (hA : JointlySmoothOn g (m + 1) n S A) :
    JointlySmoothOn g m (n + 1) S (fun t => flipField g m n (A t)) := by
  apply contMDiffOn_clm_section_of_apply (I := I) (M := M)
    (F₁ := Tensor0SModel m ℝ E) (V₁ := fun x : M => Tensor0SSpace m I x)
    (F₂ := Tensor0SModel (n + 1) ℝ E) (V₂ := fun x : M => Tensor0SSpace (n + 1) I x)
    (φ := fun p : M × ℝ => flipFib g m n p.1
      (show Tensor0SSpace (m + 1) I p.1 →L[ℝ] Tensor0SSpace n I p.1 from (A p.2).toSection p.1))
    (S := S)
  intro Y
  apply contMDiffOn_uncurry_param (I := I) (M := M)
    (fun p : M × ℝ => flipCurried g m n p.1
      (show Tensor0SSpace (m + 1) I p.1 →L[ℝ] Tensor0SSpace n I p.1 from (A p.2).toSection p.1)
      (Y p.1))
  apply contMDiffOn_clm_section_of_apply (I := I) (M := M)
    (F₁ := E) (V₁ := fun x : M => TangentSpace I x)
    (F₂ := Tensor0SModel n ℝ E) (V₂ := fun x : M => Tensor0SSpace n I x)
    (φ := fun p : M × ℝ => flipCurried g m n p.1
      (show Tensor0SSpace (m + 1) I p.1 →L[ℝ] Tensor0SSpace n I p.1 from (A p.2).toSection p.1)
      (Y p.1))
    (S := S)
  intro Z
  have hfst : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞ (Prod.fst : M × ℝ → M)
      ((Set.univ : Set M) ×ˢ S) := contMDiffOn_fst
  have hZY := (flatPrepend_contMDiff g m Z Y).comp_contMDiffOn hfst
  have h := ContMDiffOn.clm_bundle_apply (b := Prod.fst) hA hZY
  exact h

end ShortTime
