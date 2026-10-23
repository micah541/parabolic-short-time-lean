import ShortTime.Nonlinear.RicciJetOps

/-!
# The exact Ricci identity for slot permutations (`lem:ricci`, `rem:rewrite`)

For every permutation `σ` of the `p` derivative slots of `∇^p u`, the defect
`σ(∇^p u) - ∇^p u` is a jet operator of order `≤ p - 2` (`jetOp_perm_defect`): an exact finite sum
`∑_{j ≤ p-2} Q_j ∇^j u` with smooth bundle maps `Q_j`. This is the exact version of
`ShortTime.exists_perm_bound`, proved by the same induction on a product of adjacent transpositions.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff BigOperators

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]
variable {g : SmoothRiemannianMetric I M}

theorem JetOp.of_heq {s n c c' : ℕ} (hc : c = c')
    {D : SmoothCcTensor g 0 s → SmoothCcTensor g 0 c}
    {D' : SmoothCcTensor g 0 s → SmoothCcTensor g 0 c'} (h : JetOp g s n c D)
    (hD : ∀ u, HEq (D u) (D' u)) : JetOp g s n c' D' := by
  subst hc
  have : D = D' := funext fun u => eq_of_heq (hD u)
  exact this ▸ h

theorem swapDiff_heq {N N' : ℕ} (h : N = N') (T : SmoothCcTensor g 0 N)
    (T' : SmoothCcTensor g 0 N') (hT : HEq T T') (k : ℕ) (hk : k + 1 < N) (hk' : k + 1 < N') :
    HEq (domDomCongrSection (I := I) g (Equiv.swap (⟨k, by omega⟩ : Fin N) ⟨k + 1, hk⟩) T - T)
      (domDomCongrSection (I := I) g (Equiv.swap (⟨k, by omega⟩ : Fin N') ⟨k + 1, hk'⟩) T' - T') := by
  subst h
  cases eq_of_heq hT
  rfl

/-- **One adjacent transposition of the derivative slots of `∇^p u`**, exactly. -/
theorem jetOp_adjSwap (s p k : ℕ) (hk : k + 2 ≤ p) :
    JetOp g s (p - 2) (s + p) (fun u =>
      domDomCongrSection (I := I) g
          (Equiv.swap (⟨k, by omega⟩ : Fin (s + p)) ⟨k + 1, by omega⟩)
          (iteratedCovGrad g 0 s p u) - iteratedCovGrad g 0 s p u) := by
  obtain ⟨R, hR⟩ := exists_swap_field (I := I) (M := M) (g := g) (s + (p - 2 - k)) k
  have hbase : JetOp g s (p - 2 - k) (s + (p - 2 - k) + 2) (fun u =>
      homTensorRSFieldApply (I := I) (M := M) g 0 (s + (p - 2 - k)) (s + (p - 2 - k) + 2) R
        (iteratedCovGrad g 0 s (p - 2 - k) u)) := JetOp.term _ le_rfl R
  have h2 := ((hbase.iterNabla k).mono (n' := p - 2) (by omega)).neg
  have hc : s + (p - 2 - k) + 2 + k = s + p := by omega
  refine JetOp.of_heq hc h2 (fun u => ?_)
  have hheq : HEq (iteratedCovGrad g 0 (s + (p - 2 - k) + 2) k
      (iteratedCovGrad g 0 (s + (p - 2 - k)) 2 (iteratedCovGrad g 0 s (p - 2 - k) u)))
      (iteratedCovGrad g 0 s p u) := by
    have h1 := iteratedCovGrad_comp_heq (g := g) 0 s (p - 2 - k + 2) u k
    have hp : p - 2 - k + 2 + k = p := by omega
    rw [hp] at h1
    exact h1
  have e : (-(iteratedCovGrad g 0 (s + (p - 2 - k) + 2) k
        (homTensorRSFieldApply (I := I) (M := M) g 0 (s + (p - 2 - k)) (s + (p - 2 - k) + 2) R
          (iteratedCovGrad g 0 s (p - 2 - k) u)))) =
      domDomCongrSection (I := I) g
          (Equiv.swap (⟨k, by omega⟩ : Fin (s + (p - 2 - k) + 2 + k)) ⟨k + 1, by omega⟩)
          (iteratedCovGrad g 0 (s + (p - 2 - k) + 2) k
            (iteratedCovGrad g 0 (s + (p - 2 - k)) 2 (iteratedCovGrad g 0 s (p - 2 - k) u))) -
        iteratedCovGrad g 0 (s + (p - 2 - k) + 2) k
            (iteratedCovGrad g 0 (s + (p - 2 - k)) 2 (iteratedCovGrad g 0 s (p - 2 - k) u)) := by
    rw [hR (iteratedCovGrad g 0 s (p - 2 - k) u)]
    abel
  rw [e]
  exact swapDiff_heq hc _ _ hheq k (by omega) (by omega)

theorem domDomCongrSection_defect_mul {a : ℕ} (τ₁ τ₂ : Equiv.Perm (Fin a)) (T : SmoothCcTensor g 0 a) :
    domDomCongrSection (I := I) g (τ₁ * τ₂) T - T =
      domDomCongrSection (I := I) g τ₁ (domDomCongrSection (I := I) g τ₂ T - T) +
        (domDomCongrSection (I := I) g τ₁ T - T) := by
  rw [domDomCongrSection_mul, domDomCongrSection_sub]
  abel

/-- **Exact Ricci identity** (`lem:ricci`): permuting the derivative slots of `∇^p u` changes it by
a jet operator of order `≤ p - 2` with smooth bundle-map coefficients. -/
theorem jetOp_perm_defect (s p : ℕ) (σ : Equiv.Perm (Fin p)) :
    JetOp g s (p - 2) (s + p) (fun u =>
      domDomCongrSection (I := I) g (extPerm s p σ) (iteratedCovGrad g 0 s p u) -
        iteratedCovGrad g 0 s p u) := by
  let Pr : Equiv.Perm (Fin (s + p)) → Prop := fun τ =>
    JetOp g s (p - 2) (s + p) (fun u =>
      domDomCongrSection (I := I) g τ (iteratedCovGrad g 0 s p u) - iteratedCovGrad g 0 s p u)
  have hone : Pr 1 := JetOp.zero.congr fun u => by
    rw [domDomCongrSection_one, sub_self]
  have hmul : ∀ τ₁ τ₂, Pr τ₁ → Pr τ₂ → Pr (τ₁ * τ₂) := by
    intro τ₁ τ₂ h₁ h₂
    exact ((h₂.perm τ₁).add h₁).congr fun u => (domDomCongrSection_defect_mul τ₁ τ₂ _).symm
  rcases p with _ | n
  · have hσ : σ = 1 := Subsingleton.elim _ _
    rw [hσ, map_one]
    exact hone
  · have hmem : σ ∈ Submonoid.closure (Set.range fun i : Fin n => Equiv.swap i.castSucc i.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]
      exact Submonoid.mem_top σ
    induction hmem using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [extPerm_swap]
      exact jetOp_adjSwap s (n + 1) i (by omega)
    | one => rw [map_one]; exact hone
    | mul x y _ _ hx hy => rw [map_mul]; exact hmul _ _ hx hy

end ShortTime
