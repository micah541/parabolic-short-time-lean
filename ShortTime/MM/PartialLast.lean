import ShortTime.Nonlinear.Linearize
import ShortTime.Nonlinear.ModelCoords

/-!
# The top partial derivative of an equation that is affine in the top jet component

`EquationData.partialDeriv_last_eq`: if `F(t,x,ζ + e_top(w)) = F(t,x,ζ) + L w` (at the fixed jet `ζ`, for
all `w`) for a linear `L`, then the pinned partial derivative `D_{2p}F(t,ζ)` is `L`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff BigOperators Topology

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

namespace EquationData

variable {r s p : ℕ} (D : EquationData I M r s p)

theorem partialDeriv_last_eq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) D.T₀) {x : M}
    {ζ : CovJetFiber I r s (2 * p) x} (hζ : ζ ∈ D.dom t x)
    (L : TensorRSSpace r (s + ((Fin.last (2 * p) : Fin (2 * p + 1)) : ℕ)) I x →ₗ[ℝ]
      TensorRSSpace r s I x)
    (hL : ∀ (w : TensorRSSpace r (s + ((Fin.last (2 * p) : Fin (2 * p + 1)) : ℕ)) I x),
      D.F t x (ζ + Pi.single (Fin.last (2 * p)) w) = D.F t x ζ + L w)
    (w : TensorRSSpace r (s + ((Fin.last (2 * p) : Fin (2 * p + 1)) : ℕ)) I x) :
    D.partialDeriv (Fin.last (2 * p)) t x ζ w = L w := by
  apply (fibIso I r s x).injective
  rw [fibIso_partialDeriv]
  set z₀ := jetIso I r s (2 * p) x ζ with hz₀
  set e : JetModel E r s (2 * p) := Pi.single (Fin.last (2 * p)) (fibIso I r (s + ((Fin.last (2 * p) : Fin (2 * p + 1)) : ℕ)) x w) with he
  have hdiff : DifferentiableAt ℝ (D.Fmod t x) z₀ :=
    (D.contDiffAt_Fmod ht x hζ).differentiableAt (by simp)
  have hline : HasDerivAt (fun σ : ℝ => z₀ + σ • e) e 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add z₀
  have hl : HasFDerivAt (D.Fmod t x) (fderiv ℝ (D.Fmod t x) z₀) (z₀ + (0 : ℝ) • e) := by
    simpa using hdiff.hasFDerivAt
  have h1 := hl.comp_hasDerivAt (0 : ℝ) hline
  have h2 : HasDerivAt (fun σ : ℝ => D.Fmod t x (z₀ + σ • e))
      (fibIso I r s x (L w)) 0 := by
    have hEq : ∀ σ : ℝ, D.Fmod t x (z₀ + σ • e) =
        D.Fmod t x z₀ + σ • fibIso I r s x (L w) := by
      intro σ
      have hsym : (jetIso I r s (2 * p) x).symm (z₀ + σ • e) =
          ζ + Pi.single (Fin.last (2 * p)) (σ • w) := by
        apply (jetIso I r s (2 * p) x).injective
        simp only [map_add, map_smul, LinearIsometryEquiv.apply_symm_apply, hz₀, he,
          jetIso_symm_single]
        congr 1
        rw [LinearIsometryEquiv.symm_apply_apply, ← map_smul, ← Pi.single_smul]
      simp only [EquationData.Fmod]
      rw [hsym, hL, map_add, map_smul, hz₀, LinearIsometryEquiv.symm_apply_apply, map_smul]
    simpa [hEq] using ((hasDerivAt_id (0 : ℝ)).smul_const (fibIso I r s x (L w))).const_add
      (D.Fmod t x z₀)
  have := h1.unique h2
  simpa using this

end EquationData

end ShortTime
