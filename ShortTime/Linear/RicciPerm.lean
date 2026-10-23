import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Permutation.Naturality
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurck.Linearization

/-!
# Covariant derivatives and slot permutations (towards `lem:ricci`)

`∇` adds a slot in front, so permuting the slots of `S` and then differentiating `i` times is the
same as differentiating and then permuting the *last* slots by the shifted permutation
`liftPerm σ i`. The library proves this with the shifted permutation only asserted to exist
(`exists_iteratedCovGrad_unit_toModel_domDomCongr`); here it is made explicit, which is what the
Ricci identity for a transposition of two inner slots needs.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral DifferentialGeometry.Analysis.Sobolev
open scoped Manifold ContDiff BigOperators

namespace ShortTime

/-- `σ` acting on the last `m` of `m + i` slots (the first `i` are fixed). -/
def liftPerm {m : ℕ} (σ : Equiv.Perm (Fin m)) : ∀ i : ℕ, Equiv.Perm (Fin (m + i))
  | 0 => σ
  | i + 1 => Equiv.Perm.decomposeFin.symm (0, liftPerm σ i)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

/-- **Naturality, explicit form.** If `Φ'` is `Φ` with output slots permuted by `σ`, then
`∇^i Φ'` is `∇^i Φ` with output slots permuted by `liftPerm σ i`. -/
theorem toModel_iteratedCovGrad_domDomCongr (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (σ : Equiv.Perm (Fin s)) (Φ Φ' : SmoothCcTensor g r s)
    (hrel : ∀ (y : M) (d : Tensor0SSpace r I y),
      Tensor0SSpace.toModel
          ((show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y from Φ'.toSection y) d) =
        ContinuousMultilinearMap.domDomCongr σ
          (Tensor0SSpace.toModel
            ((show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y from Φ.toSection y) d))) :
    ∀ (i : ℕ) (x : M) (d : Tensor0SSpace r I x),
      Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + i) I x from
            (iteratedCovGrad (I := I) g r s i Φ').toSection x) d) =
        ContinuousMultilinearMap.domDomCongr (liftPerm σ i)
          (Tensor0SSpace.toModel
            ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + i) I x from
              (iteratedCovGrad (I := I) g r s i Φ).toSection x) d))
  | 0, x, d => hrel x d
  | i + 1, x, d => by
    apply ContinuousMultilinearMap.ext
    intro v
    exact covGrad_rs_toModel_domDomCongr (I := I) (M := M) g r (s + i) (liftPerm σ i)
      (iteratedCovGrad (I := I) g r s i Φ) (iteratedCovGrad (I := I) g r s i Φ')
      (toModel_iteratedCovGrad_domDomCongr g r s σ Φ Φ' hrel i) x d v

/-- `liftPerm` of the swap of the first two slots is the swap of slots `k, k+1`. -/
theorem liftPerm_swap (t : ℕ) : ∀ k : ℕ,
    liftPerm (Equiv.swap (0 : Fin (t + 2)) 1) k =
      Equiv.swap (⟨k, by omega⟩ : Fin (t + 2 + k)) ⟨k + 1, by omega⟩
  | 0 => by
    ext i
    rfl
  | k + 1 => by
    ext i
    change (Equiv.Perm.decomposeFin.symm (0, liftPerm (Equiv.swap (0 : Fin (t + 2)) 1) k) i).val = _
    rw [liftPerm_swap t k]
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.swap_apply_of_ne_of_ne]
      · simp [Fin.ext_iff]
      · simp [Fin.ext_iff]
    · rw [Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply]
      simp only [Equiv.swap_apply_def, Fin.ext_iff, Fin.val_succ]
      split_ifs <;> simp_all <;> omega

/-- Iterating `∇` in two stages gives the same field as iterating at once (up to the rank
equation `(s + j) + i = s + (j + i)`). -/
theorem iteratedCovGrad_comp_heq {g : SmoothRiemannianMetric I M} (r s j : ℕ)
    (S : SmoothCcTensor g r s) : ∀ i : ℕ,
    HEq (iteratedCovGrad g r (s + j) i (iteratedCovGrad g r s j S))
      (iteratedCovGrad g r s (j + i) S)
  | 0 => HEq.rfl
  | i + 1 => by
    have ih := iteratedCovGrad_comp_heq r s j S i
    change HEq (covGrad (I := I) (M := M) g r (s + j + i)
        (iteratedCovGrad g r (s + j) i (iteratedCovGrad g r s j S)))
      (covGrad (I := I) (M := M) g r (s + (j + i)) (iteratedCovGrad g r s (j + i) S))
    have h : s + j + i = s + (j + i) := by omega
    revert ih
    generalize iteratedCovGrad g r (s + j) i (iteratedCovGrad g r s j S) = Y
    generalize iteratedCovGrad g r s (j + i) S = Z
    revert Y Z
    rw [h]
    intro Z Y hYZ
    rw [eq_of_heq hYZ]

end ShortTime
