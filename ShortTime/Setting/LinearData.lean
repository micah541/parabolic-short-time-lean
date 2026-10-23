import ShortTime.Setting.Equation
import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-!
# Linear equations `∂ₜu = P(∇^{2p}u)`

If `P` is a smooth section of `Hom(T^r_{s+2p}, T^r_s)`, then `∂ₜu = P(∇^{2p}u)`, with every jet in
the domain, is valid `EquationData` (`linearData`), and its principal coefficient is `P`
(`linearData_principal`).

Also provided: two lemmas about reading sections in the fixed trivializations used by
`EquationData`, which are useful well beyond linear equations.
-/

noncomputable section

set_option linter.unusedSectionVars false
open Bundle Manifold Set
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Analysis.Sobolev
open scoped Manifold ContDiff
namespace ShortTime
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

variable (I M) in
/-- `P` is a smooth section of the bundle `Hom(T^r_a M, T^r_b M)`. -/
def SmoothHomSection (r a b : ℕ)
    (P : ∀ x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r b I x) : Prop :=
  ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r b ℝ E)) ∞
    (fun x => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r b ℝ E)
      (E := fun x : M => TensorRSSpace r a I x →L[ℝ] TensorRSSpace r b I x) x (P x))


/-- The inverse trivialization, applied to a smooth model-valued map, is a smooth section. -/
theorem contMDiffAt_symmL_apply {r a : ℕ}
    {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] {HN : Type*} [TopologicalSpace HN]
    {IN : ModelWithCorners ℝ EN HN} {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]
    (x₀ : M) (b : N → M) (z : N → TensorRSModel r a ℝ E) {q : N}
    (hb : ContMDiffAt IN I ∞ b q) (hz : ContMDiffAt IN 𝓘(ℝ, TensorRSModel r a ℝ E) ∞ z q)
    (hq : b q ∈ (trivAt I M r a x₀).baseSet) :
    ContMDiffAt IN (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E)) ∞
      (fun q => TotalSpace.mk' (TensorRSModel r a ℝ E)
        (E := fun x : M => TensorRSSpace r a I x) (b q)
        ((trivAt I M r a x₀).symmL ℝ (b q) (z q))) q := by
  have hsymm := ((trivAt I M r a x₀).contMDiffAt_symmL hq).comp q hb
  have hz' : ContMDiffAt IN (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E)) ∞
      (fun q => TotalSpace.mk' (TensorRSModel r a ℝ E)
        (E := Bundle.Trivial M (TensorRSModel r a ℝ E)) (b q) (z q)) q := by
    rw [contMDiffAt_totalSpace]
    exact ⟨hb, by simpa using hz⟩
  exact hsymm.clm_bundle_apply hz'

/-- Reading a smooth section in a fixed trivialization gives smooth coordinates on the base set. -/
theorem contMDiffAt_continuousLinearMapAt_apply {r a : ℕ}
    {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] {HN : Type*} [TopologicalSpace HN]
    {IN : ModelWithCorners ℝ EN HN} {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]
    (x₀ : M) (b : N → M) (v : ∀ q, TensorRSSpace r a I (b q)) {q : N}
    (hv : ContMDiffAt IN (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E)) ∞
      (fun q => TotalSpace.mk' (TensorRSModel r a ℝ E)
        (E := fun x : M => TensorRSSpace r a I x) (b q) (v q)) q)
    (hq : b q ∈ (trivAt I M r a x₀).baseSet) :
    ContMDiffAt IN 𝓘(ℝ, TensorRSModel r a ℝ E) ∞
      (fun q => (trivAt I M r a x₀).continuousLinearMapAt ℝ (b q) (v q)) q := by
  have h := ((trivAt I M r a x₀).contMDiffAt_iff
    (by simpa [Trivialization.mem_source] using hq)).mp hv
  have hbc : ContinuousAt b q := (contMDiffAt_totalSpace.mp hv).1.continuousAt
  apply h.2.congr_of_eventuallyEq
  filter_upwards [hbc.preimage_mem_nhds ((trivAt I M r a x₀).open_baseSet.mem_nhds hq)]
    with q' hq'
  rw [Trivialization.continuousLinearMapAt_apply,
    Trivialization.coe_linearMapAt_of_mem _ hq']

/-- For a linear equation `∂ₜu = P(∇^{2p}u)` with `P` smooth, the local representative of `F`
is smooth: the smoothness field of `EquationData`. -/
theorem localRep_linear_contMDiffOn (r s p : ℕ) (T₀ : ℝ)
    (P : ∀ x : M, TensorRSSpace r (s + 2 * p) I x →L[ℝ] TensorRSSpace r s I x)
    (hP : SmoothHomSection I M r (s + 2 * p) s P) (x₀ : M) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, JetModel E r s (2 * p))))
      𝓘(ℝ, TensorRSModel r s ℝ E) ∞
      (localRep r s (2 * p)
        (fun (_ : ℝ) (x : M) (ζ : CovJetFiber I r s (2 * p) x) => P x (ζ ⟨2 * p, Nat.lt_succ_self _⟩))
        x₀)
      (localDom r s (2 * p) T₀
        (fun (_ : ℝ) (x : M) => (Set.univ : Set (CovJetFiber I r s (2 * p) x))) x₀) := by
  intro q hq
  have hy : q.2.1 ∈ jetBase (I := I) r s (2 * p) x₀ := hq.1.2
  have hy₀ : q.2.1 ∈ (trivAt I M r s x₀).baseSet := hy.1
  have hy₂ : q.2.1 ∈ (trivAt I M r (s + 2 * p) x₀).baseSet :=
    Set.mem_iInter.mp hy.2 ⟨2 * p, Nat.lt_succ_self _⟩
  have hsnd : ContMDiff (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, JetModel E r s (2 * p))))
      (I.prod 𝓘(ℝ, JetModel E r s (2 * p))) ∞
      (fun q : ℝ × M × JetModel E r s (2 * p) => q.2) :=
    contMDiff_snd
  have hb : ContMDiffAt (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, JetModel E r s (2 * p)))) I ∞
      (fun q : ℝ × M × JetModel E r s (2 * p) => q.2.1) q :=
    (contMDiff_fst.comp hsnd).contMDiffAt
  have hz : ContMDiffAt (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, JetModel E r s (2 * p))))
      𝓘(ℝ, TensorRSModel r (s + 2 * p) ℝ E) ∞
      (fun q : ℝ × M × JetModel E r s (2 * p) =>
        q.2.2 ⟨2 * p, Nat.lt_succ_self _⟩) q := by
    let pr : JetModel E r s (2 * p) →L[ℝ] TensorRSModel r (s + 2 * p) ℝ E :=
      ContinuousLinearMap.proj (R := ℝ)
        (φ := fun k : Fin (2 * p + 1) => TensorRSModel r (s + (k : ℕ)) ℝ E) ⟨2 * p, Nat.lt_succ_self _⟩
    have hproj : ContMDiff 𝓘(ℝ, JetModel E r s (2 * p)) 𝓘(ℝ, TensorRSModel r (s + 2 * p) ℝ E) ∞
        (fun z : JetModel E r s (2 * p) => pr z) := pr.contDiff.contMDiff
    exact (hproj.comp (contMDiff_snd.comp hsnd)).contMDiffAt
  have hv₁ := contMDiffAt_symmL_apply (I := I) (M := M) x₀ _ _ hb hz hy₂
  have hv₂ := ((hP q.2.1).comp q hb).clm_bundle_apply hv₁
  exact (contMDiffAt_continuousLinearMapAt_apply (I := I) (M := M) x₀ _ _ hv₂ hy₀).contMDiffWithinAt

variable (I M) in
/-- The linear equation `∂ₜu = P(∇^{2p}u)`, with every jet in the domain, for a smooth
section `P` of `Hom(T^r_{s+2p}, T^r_s)`. -/
def linearData (r s p : ℕ) (T₀ : ℝ) (hT₀ : 0 < T₀)
    (P : ∀ x : M, TensorRSSpace r (s + 2 * p) I x →L[ℝ] TensorRSSpace r s I x)
    (hP : SmoothHomSection I M r (s + 2 * p) s P) : EquationData I M r s p where
  T₀ := T₀
  T₀_pos := hT₀
  dom := fun (_ : ℝ) (x : M) => (Set.univ : Set (CovJetFiber I r s (2 * p) x))
  F := fun (_ : ℝ) (x : M) (ζ : CovJetFiber I r s (2 * p) x) => P x (ζ ⟨2 * p, Nat.lt_succ_self _⟩)
  dom_relOpen := fun x₀ => ⟨Set.univ, isOpen_univ, by ext q; simp [localDom]⟩
  smooth := localRep_linear_contMDiffOn r s p T₀ P hP

/-- The principal coefficient of a linear equation is `P` itself (up to reindexing). -/
theorem linearData_principal (r s p : ℕ) (T₀ : ℝ) (hT₀ : 0 < T₀)
    (P : ∀ x : M, TensorRSSpace r (s + 2 * p) I x →L[ℝ] TensorRSSpace r s I x)
    (hP : SmoothHomSection I M r (s + 2 * p) s P) (t : ℝ) (x : M)
    (ζ : CovJetFiber I r s (2 * p) x) (ξ : TensorRSSpace r (s + p + p) I x) :
    (linearData I M r s p T₀ hT₀ P hP).principal t x ζ ξ =
      P x (EquationData.castIdx (r := r) (by omega : s + p + p = s + 2 * p) x ξ) := by
  have hF : (linearData I M r s p T₀ hT₀ P hP).F t x =
      (P x).comp (ContinuousLinearMap.proj (R := ℝ)
        (φ := fun k : Fin (2 * p + 1) => TensorRSSpace r (s + (k : ℕ)) I x)
        ⟨2 * p, Nat.lt_succ_self _⟩) := rfl
  simp only [EquationData.principal, EquationData.partialDeriv, hF, ContinuousLinearMap.fderiv,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  congr 1
  exact Pi.single_eq_same (M := fun k : Fin (2 * p + 1) => TensorRSSpace r (s + (k : ℕ)) I x)
    (Fin.last (2 * p)) _

end ShortTime
