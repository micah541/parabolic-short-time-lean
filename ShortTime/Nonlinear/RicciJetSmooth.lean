import ShortTime.Nonlinear.RicciJetPerm
import ShortTime.Setting.LinearData

/-!
# Jet operators are smooth jet maps (towards `rem:rewrite`)

A jet operator `D = ∑_{j ≤ n} Q_j ∇^j` is evaluated at a point through the jet of `u`:
`(D u)(x) = Qj x (j^N u (x))` with `Qj x ζ = ∑ Q_j(x) ζ_j`. This is a fibrewise linear map on jets,
smooth in the trivializations at each `x₀` (`SmoothJetMap`), which is the smoothness notion of
`EquationData`. Combined with `jetOp_perm_defect` this gives the exact Ricci identity in jet form
(`exists_ricci_jetMap`).
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

variable (I M) in
/-- `Qj` is a smooth fibre map `J^N(T⁰_s) → T⁰_c`: read in the trivializations at each `x₀`, it is
smooth in `(x, jet coordinates)` on the part over `jetBase x₀`. -/
def SmoothJetMap (s N c : ℕ)
    (Qj : ∀ x : M, CovJetFiber I 0 s N x → TensorRSSpace 0 c I x) : Prop :=
  ∀ x₀ : M, ContMDiffOn (I.prod 𝓘(ℝ, JetModel E 0 s N)) 𝓘(ℝ, TensorRSModel 0 c ℝ E) ∞
    (fun q : M × JetModel E 0 s N => (trivAt I M 0 c x₀).continuousLinearMapAt ℝ q.1
      (Qj q.1 (jetOfModel 0 s N x₀ q.1 q.2)))
    {q | q.1 ∈ jetBase (I := I) 0 s N x₀ ∧ q.1 ∈ (trivAt I M 0 c x₀).baseSet}

theorem smoothJetMap_zero (s N c : ℕ) :
    SmoothJetMap I M s N c (fun _ _ => 0) := by
  intro x₀
  refine (contMDiffOn_const (c := (0 : TensorRSModel 0 c ℝ E))).congr ?_
  intro q _
  simp

theorem smoothJetMap_add {s N c : ℕ}
    {Q₁ Q₂ : ∀ x : M, CovJetFiber I 0 s N x → TensorRSSpace 0 c I x}
    (h₁ : SmoothJetMap I M s N c Q₁) (h₂ : SmoothJetMap I M s N c Q₂) :
    SmoothJetMap I M s N c (fun x ζ => Q₁ x ζ + Q₂ x ζ) := by
  intro x₀
  refine ((h₁ x₀).add (h₂ x₀)).congr ?_
  intro q _
  simp [map_add]

theorem smoothJetMap_term (s N c j : ℕ) (hj : j ≤ N)
    (Q : HomTensorRSField (E := E) (M := M) 0 (s + j) c I) :
    SmoothJetMap I M s N c (fun x ζ => Q x (ζ ⟨j, Nat.lt_succ_of_le hj⟩)) := by
  have hP : SmoothHomSection I M 0 (s + j) c (fun x => Q x) := Q.contMDiff
  intro x₀ q hq
  have hy : q.1 ∈ jetBase (I := I) 0 s N x₀ := hq.1
  have hy₀ : q.1 ∈ (trivAt I M 0 c x₀).baseSet := hq.2
  have hy₂ : q.1 ∈ (trivAt I M 0 (s + j) x₀).baseSet :=
    Set.mem_iInter.mp hy.2 ⟨j, Nat.lt_succ_of_le hj⟩
  have hb : ContMDiffAt (I.prod 𝓘(ℝ, JetModel E 0 s N)) I ∞
      (fun q : M × JetModel E 0 s N => q.1) q := contMDiff_fst.contMDiffAt
  have hz : ContMDiffAt (I.prod 𝓘(ℝ, JetModel E 0 s N)) 𝓘(ℝ, TensorRSModel 0 (s + j) ℝ E) ∞
      (fun q : M × JetModel E 0 s N => q.2 ⟨j, Nat.lt_succ_of_le hj⟩) q := by
    let pr : JetModel E 0 s N →L[ℝ] TensorRSModel 0 (s + j) ℝ E :=
      ContinuousLinearMap.proj (R := ℝ)
        (φ := fun k : Fin (N + 1) => TensorRSModel 0 (s + (k : ℕ)) ℝ E) ⟨j, Nat.lt_succ_of_le hj⟩
    have hproj : ContMDiff 𝓘(ℝ, JetModel E 0 s N) 𝓘(ℝ, TensorRSModel 0 (s + j) ℝ E) ∞
        (fun z : JetModel E 0 s N => pr z) := pr.contDiff.contMDiff
    exact (hproj.comp contMDiff_snd).contMDiffAt
  have hv₁ := contMDiffAt_symmL_apply (I := I) (M := M) x₀ _ _ hb hz hy₂
  have hv₂ := ((hP q.1).comp q hb).clm_bundle_apply hv₁
  exact (contMDiffAt_continuousLinearMapAt_apply (I := I) (M := M) x₀ _ _ hv₂ hy₀).contMDiffWithinAt

/-- Every jet operator of order `≤ N` is evaluated through a smooth jet map. -/
theorem JetOp.exists_jetMap {s n c N : ℕ} {D : SmoothCcTensor g 0 s → SmoothCcTensor g 0 c}
    (h : JetOp g s n c D) (hN : n ≤ N) :
    ∃ Qj : ∀ x : M, CovJetFiber I 0 s N x → TensorRSSpace 0 c I x,
      SmoothJetMap I M s N c Qj ∧ ∀ u x, (D u).toSection x = Qj x (covJet g 0 s N u x) := by
  induction h with
  | zero =>
    refine ⟨fun _ _ => 0, smoothJetMap_zero s N _, fun u x => ?_⟩
    rw [SmoothCcTensor.toSection_zero]
    rfl
  | term j hj Q =>
    refine ⟨fun x ζ => Q x (ζ ⟨j, Nat.lt_succ_of_le (hj.trans hN)⟩),
      smoothJetMap_term s N _ j (hj.trans hN) Q, fun u x => ?_⟩
    rw [homTensorRSFieldApply_toSection]
    rfl
  | add _ _ ih1 ih2 =>
    obtain ⟨Q₁, hQ₁, e₁⟩ := ih1
    obtain ⟨Q₂, hQ₂, e₂⟩ := ih2
    refine ⟨fun x ζ => Q₁ x ζ + Q₂ x ζ, smoothJetMap_add hQ₁ hQ₂, fun u x => ?_⟩
    rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply, e₁, e₂]

/-- **Exact Ricci identity in jet form** (`lem:ricci`, `rem:rewrite`). Permuting the derivative slots
of `∇^p u` by `σ` changes `∇^p u` by `Qj(j^N u)`, a smooth fibrewise linear function of the jet of
order `N ≥ p - 2` (the top slots `p - 1, …` do not enter). -/
theorem exists_ricci_jetMap (s p N : ℕ) (hN : p - 2 ≤ N) (σ : Equiv.Perm (Fin p)) :
    ∃ Qj : ∀ x : M, CovJetFiber I 0 s N x → TensorRSSpace 0 (s + p) I x,
      SmoothJetMap I M s N (s + p) Qj ∧ ∀ (u : SmoothCcTensor g 0 s) (x : M),
        (domDomCongrSection (I := I) g (extPerm s p σ) (iteratedCovGrad g 0 s p u)).toSection x =
          (iteratedCovGrad g 0 s p u).toSection x + Qj x (covJet g 0 s N u x) := by
  obtain ⟨Qj, hQ, e⟩ := (jetOp_perm_defect (g := g) s p σ).exists_jetMap hN
  refine ⟨Qj, hQ, fun u x => ?_⟩
  rw [← e u x, SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
  abel

end ShortTime
