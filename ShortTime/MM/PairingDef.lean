import ShortTime.Sanity.LegendreProduct
import ShortTime.Nonlinear.RicciJetSmooth
import ShortTime.Setting.Equation

/-!
# The Mantegazza–Martinazzi pairing (interleaved ordering)

Paper: `cor:MM`, `rem:rewrite`, `lem:legendre-examples` (a).

For symmetric forms `E_ℓ` on covectors, `mmPairing` is the contraction
`(-1)^{p+1} Σ E_1^{i₁j₁}⋯E_p^{i_pj_p} ζ_{i₁j₁⋯i_pj_p}` of the `2p`-tensor `ζ`: the pair `E_ℓ` occupies
the slots `(2ℓ, 2ℓ+1)`. It differs from the split pairing `productCLM` (pairs `(ℓ, p+ℓ)`) by the slot
permutation `mmSlotPerm p`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Analysis.Sobolev
open scoped Manifold ContDiff BigOperators

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-- `(K₀, K'₀, K₁, K'₁, …)`: the interleaved vector. -/
def interleave {A : Type*} {p : ℕ} (K K' : Fin p → A) : Fin (2 * p) → A :=
  fun m => if m.val % 2 = 0 then K ⟨m.val / 2, by have := m.isLt; omega⟩
    else K' ⟨m.val / 2, by have := m.isLt; omega⟩

/-- `(K₀, …, K_{p-1}, K'₀, …, K'_{p-1})`: the split vector. -/
def splitVec {A : Type*} {p : ℕ} (K K' : Fin p → A) : Fin (2 * p) → A :=
  fun m => if h : m.val < p then K ⟨m.val, h⟩ else K' ⟨m.val - p, by have := m.isLt; omega⟩

/-- The permutation of `Fin (2p)` with `splitVec K K' ∘ mmSlotPerm = interleave K K'`. -/
def mmSlotPerm (p : ℕ) : Equiv.Perm (Fin (2 * p)) where
  toFun m := if m.val % 2 = 0 then ⟨m.val / 2, by have := m.isLt; omega⟩
    else ⟨p + m.val / 2, by have := m.isLt; omega⟩
  invFun n := if h : n.val < p then ⟨2 * n.val, by omega⟩
    else ⟨2 * (n.val - p) + 1, by have := n.isLt; omega⟩
  left_inv m := by
    have hm := m.isLt
    by_cases h : m.val % 2 = 0
    · dsimp only
      rw [if_pos h, dif_pos (show m.val / 2 < p by omega)]
      ext; simp only; omega
    · dsimp only
      rw [if_neg h, dif_neg (show ¬ p + m.val / 2 < p by omega)]
      ext; simp only; omega
  right_inv n := by
    have hn := n.isLt
    by_cases h : n.val < p
    · dsimp only
      rw [dif_pos h, if_pos (show 2 * n.val % 2 = 0 by omega)]
      ext; simp only; omega
    · dsimp only
      rw [dif_neg h, if_neg (show ¬ (2 * (n.val - p) + 1) % 2 = 0 by omega)]
      ext; simp only; omega

theorem splitVec_slotPerm {A : Type*} {p : ℕ} (K K' : Fin p → A) :
    splitVec K K' ∘ mmSlotPerm p = interleave K K' := by
  funext m
  have := m.isLt
  by_cases h : m.val % 2 = 0
  · simp only [Function.comp_apply, splitVec, interleave, mmSlotPerm, Equiv.coe_fn_mk, if_pos h]
    rw [dif_pos (by omega)]
  · simp only [Function.comp_apply, splitVec, interleave, mmSlotPerm, Equiv.coe_fn_mk, if_neg h]
    rw [dif_neg (by simp only [not_lt]; omega)]
    congr 2
    omega

variable (g : SmoothRiemannianMetric I M)

/-- **The Mantegazza–Martinazzi pairing.** For bilinear forms `E_ℓ` on covectors,
`ζ ↦ (-1)^{p+1} Σ_{K,K'} ∏_ℓ E_ℓ(e^{K_ℓ}, e^{K'_ℓ}) ζ(e_{K₀}, e_{K'₀}, …, e_{K_{p-1}}, e_{K'_{p-1}})`,
the sum over a `g`-orthonormal frame. -/
def mmPairing (p : ℕ) (x : M)
    (Ef : Fin p → (TangentSpace I x →L[ℝ] ℝ) →ₗ[ℝ] (TangentSpace I x →L[ℝ] ℝ) →ₗ[ℝ] ℝ) :
    TensorRSSpace 0 (0 + 2 * p) I x →L[ℝ] TensorRSSpace 0 0 I x :=
  (-1 : ℝ) ^ (p + 1) • ∑ K : Fin p → Fin (Module.finrank ℝ (TangentSpace I x)),
    ∑ K' : Fin p → Fin (Module.finrank ℝ (TangentSpace I x)),
      (∏ l, Ef l (coframe g x (K l)) (coframe g x (K' l))) •
        evalFirstCLM (r := 0) (s := 0) (2 * p)
          (interleave (fun i => tangentFrame g x (K i)) (fun i => tangentFrame g x (K' i)))

end ShortTime
