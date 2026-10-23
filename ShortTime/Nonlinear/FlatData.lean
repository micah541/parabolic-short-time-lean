import ShortTime.Nonlinear.FlatCoord
import ShortTime.Nonlinear.LocalRep

/-!
# Lowering the equation

Paper: Lemma `lem:lowering`, the transported equation `F^♭(t, ζ) = ♭ F(t, ♭_J⁻¹ ζ)`.

* `jetFlat`: the jet map `♭_J`, `(♭_J ζ)_k = σ_k ♭ ζ_k`. It maps covariant jets to covariant jets
  (`covJet_flatCc_eq`).
* `EquationData.flatData`: the equation data `D^♭` on `T⁰_{r+s}`, with domain `♭_J(𝒟)`.
  In the coordinates at `x₀` it reads `(t, y, z) ↦ Ψ(y) F(t, y, Φ(y) z)` with `Ψ` (lowering) and
  `Φ` (raising, then unpermuting) smooth in `y` (`FlatCoord.lean`), which gives openness and
  smoothness.
* `jointlySmoothOn_flatCc`: lowering preserves jointly smooth families.
-/

noncomputable section

open Bundle Manifold Set Filter
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

variable (g : SmoothRiemannianMetric I M)

/-! ### The jet map -/

/-- Lowering on covariant jets: `(♭_J ζ)_k = σ_k ♭ ζ_k`. -/
def jetFlat (r s N : ℕ) (y : M) : CovJetFiber I r s N y ≃L[ℝ] CovJetFiber I 0 (r + s) N y :=
  ContinuousLinearEquiv.piCongrRight fun k =>
    (flat g r (s + k) y).trans (slotPerm I (jetPerm r s k) y)

theorem jetFlat_apply {r s N : ℕ} {y : M} (ζ : CovJetFiber I r s N y) (k : Fin (N + 1)) :
    jetFlat g r s N y ζ k = slotPerm I (jetPerm r s k) y (flat g r (s + k) y (ζ k)) := rfl

theorem jetFlat_symm_apply {r s N : ℕ} {y : M} (ζ : CovJetFiber I 0 (r + s) N y) (k : Fin (N + 1)) :
    (jetFlat g r s N y).symm ζ k = (flat g r (s + k) y).symm ((slotPerm I (jetPerm r s k) y).symm (ζ k)) :=
  rfl

/-- `♭` maps covariant jets to covariant jets. -/
theorem covJet_flatCc_eq {r s : ℕ} (N : ℕ) (T : SmoothCcTensor g r s) (x : M) :
    covJet g 0 (r + s) N (flatCc g r s T) x = jetFlat g r s N x (covJet g r s N T x) :=
  funext fun k => covJet_flatCc g N T x k

/-! ### Jointly smooth families -/

/-- Lowering preserves jointly smooth families. -/
theorem jointlySmoothOn_flatCc {r s : ℕ} {S : Set ℝ} {u : ℝ → SmoothCcTensor g r s}
    (hu : JointlySmoothOn g r s S u) :
    JointlySmoothOn g 0 (r + s) S (fun t => flatCc g r s (u t)) := by
  have h := ContMDiffOn.clm_bundle_apply (b := Prod.fst) (contMDiffOn_flat_param g r s S) hu
  refine h.congr fun p _ => ?_
  simp only
  rw [flatCc_toSection]
  rfl

/-! ### Base sets -/

theorem mem_jetBase_iff {r s N : ℕ} {x₀ y : M} :
    y ∈ jetBase (I := I) r s N x₀ ↔ y ∈ (trivializationAt E (TangentSpace I) x₀).baseSet :=
  ⟨fun h => h.1.1, fun h => ⟨⟨h, h⟩, mem_iInter.mpr fun _ => ⟨h, h⟩⟩⟩

/-! ### The jet map in coordinates -/

variable [CompleteSpace E]

/-- The inverse jet map in the coordinates at `x₀`: raise the indices of each component after
undoing its slot permutation. -/
def jetFlatInvCoord (r s N : ℕ) (x₀ y : M) (z : JetModel E 0 (r + s) N) : JetModel E r s N :=
  fun k => (flatCoord g r (s + k) x₀ y).inverse ((permModel E (jetPerm r s k)).symm (z k))

theorem trivAt_slotPerm_symm {a b : ℕ} (e : Fin a ≃ Fin b) {x₀ y : M}
    (hy : y ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) (W : TensorRSSpace 0 b I y) :
    (trivAt I M 0 a x₀).continuousLinearMapAt ℝ y ((slotPerm I e y).symm W) =
      (permModel E e).symm ((trivAt I M 0 b x₀).continuousLinearMapAt ℝ y W) := by
  rw [eq_comm, ContinuousLinearEquiv.symm_apply_eq, ← trivAt_slotPerm e hy,
    ContinuousLinearEquiv.apply_symm_apply]

theorem trivAt_flat_symm {r s : ℕ} {x₀ y : M}
    (hy : y ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) (W : TensorRSSpace 0 (r + s) I y) :
    (trivAt I M r s x₀).continuousLinearMapAt ℝ y ((flat g r s y).symm W) =
      (flatCoord g r s x₀ y).inverse ((trivAt I M 0 (r + s) x₀).continuousLinearMapAt ℝ y W) := by
  rw [← flatCoordEquiv_coe g r s (mem_trivAt_baseSet hy) (mem_trivAt_baseSet hy),
    ContinuousLinearMap.inverse_equiv]
  apply (flatCoordEquiv g r s (mem_trivAt_baseSet hy) (mem_trivAt_baseSet hy)).injective
  rw [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
  change (flatCoordEquiv g r s _ _ : TensorRSModel r s ℝ E →L[ℝ] TensorRSModel 0 (r + s) ℝ E) _ = _
  rw [flatCoordEquiv_coe, flatCoord_trivAt g (mem_trivAt_baseSet hy),
    ContinuousLinearEquiv.apply_symm_apply]

/-- In the coordinates at `x₀`, the inverse jet map is `jetFlatInvCoord`. -/
theorem jetFlat_symm_jetOfModel {r s N : ℕ} {x₀ y : M}
    (hy : y ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) (z : JetModel E 0 (r + s) N) :
    (jetFlat g r s N y).symm (jetOfModel 0 (r + s) N x₀ y z) =
      jetOfModel r s N x₀ y (jetFlatInvCoord g r s N x₀ y z) := by
  funext k
  rw [jetFlat_symm_apply]
  apply ((trivAt I M r (s + k) x₀).continuousLinearEquivAt ℝ y (mem_trivAt_baseSet hy)).injective
  rw [Trivialization.coe_continuousLinearEquivAt_eq, trivAt_flat_symm g hy,
    trivAt_slotPerm_symm _ hy]
  simp only [jetOfModel, jetFlatInvCoord, Trivialization.continuousLinearMapAt_symmL _
    (mem_trivAt_baseSet hy)]

/-- The inverse jet map is smooth in coordinates. -/
theorem contMDiffAt_jetFlatInvCoord {r s N : ℕ} {x₀ y : M}
    (hy : y ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) (z : JetModel E 0 (r + s) N) :
    ContMDiffAt (I.prod 𝓘(ℝ, JetModel E 0 (r + s) N)) 𝓘(ℝ, JetModel E r s N) ∞
      (fun q : M × JetModel E 0 (r + s) N => jetFlatInvCoord g r s N x₀ q.1 q.2) (y, z) := by
  rw [contMDiffAt_pi_space]
  intro k
  have hA : ContMDiffAt (I.prod 𝓘(ℝ, JetModel E 0 (r + s) N))
      𝓘(ℝ, TensorRSModel 0 (r + (s + k)) ℝ E →L[ℝ] TensorRSModel r (s + k) ℝ E) ∞
      (fun q : M × JetModel E 0 (r + s) N => (flatCoord g r (s + k) x₀ q.1).inverse) (y, z) :=
    (contMDiffAt_flatCoord_inverse g r (s + k) (mem_trivAt_baseSet hy)
      (mem_trivAt_baseSet hy)).comp (y, z) contMDiffAt_fst
  have hz : ContMDiffAt (I.prod 𝓘(ℝ, JetModel E 0 (r + s) N)) 𝓘(ℝ, TensorRSModel 0 (r + (s + k)) ℝ E) ∞
      (fun q : M × JetModel E 0 (r + s) N => (permModel E (jetPerm r s k)).symm (q.2 k)) (y, z) := by
    have h1 : ContMDiffAt (I.prod 𝓘(ℝ, JetModel E 0 (r + s) N)) 𝓘(ℝ, JetModel E 0 (r + s) N) ∞
        (fun q : M × JetModel E 0 (r + s) N => q.2) (y, z) := contMDiffAt_snd
    have h2 := (contMDiffAt_pi_space.mp h1) k
    exact (permModel E (jetPerm r s k)).symm.toContinuousLinearMap.contMDiff.contMDiffAt.comp
      (y, z) h2
  exact hA.clm_apply hz

/-! ### The lowered equation -/

/-- The change of coordinates `(t, y, z) ↦ (t, y, Φ(y) z)` from the coordinates of the lowered
equation to those of the original one. -/
def flatParam {r s : ℕ} (N : ℕ) (x₀ : M) (q : ℝ × M × JetModel E 0 (r + s) N) :
    ℝ × M × JetModel E r s N :=
  (q.1, q.2.1, jetFlatInvCoord g r s N x₀ q.2.1 q.2.2)

theorem contMDiffAt_flatParam {r s N : ℕ} {x₀ : M} {q : ℝ × M × JetModel E 0 (r + s) N}
    (hq : q.2.1 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, JetModel E 0 (r + s) N)))
      (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, JetModel E r s N))) ∞ (flatParam g N x₀) q := by
  have hsnd := contMDiffAt_snd (I := 𝓘(ℝ, ℝ)) (J := I.prod 𝓘(ℝ, JetModel E 0 (r + s) N)) (n := ∞)
    (p := q)
  have hΦ := (contMDiffAt_jetFlatInvCoord g (N := N) hq q.2.2).comp q hsnd
  have hy := (contMDiffAt_fst (I := I) (J := 𝓘(ℝ, JetModel E 0 (r + s) N)) (n := ∞)).comp q hsnd
  exact (contMDiffAt_fst (I := 𝓘(ℝ, ℝ)) (J := I.prod 𝓘(ℝ, JetModel E 0 (r + s) N)) (n := ∞)).prodMk
    (hy.prodMk hΦ)

theorem mem_localSlab_iff {r s N : ℕ} {T₀ : ℝ} {x₀ : M} {q : ℝ × M × JetModel E r s N} :
    q ∈ localSlab (I := I) r s N T₀ x₀ ↔
      q.1 ∈ Icc 0 T₀ ∧ q.2.1 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
  change _ ∧ _ ↔ _
  rw [mem_jetBase_iff]

namespace EquationData

variable {r s p : ℕ} (D : EquationData I M r s p)

/-- The domain `♭_J(𝒟)` of the lowered equation. -/
def flatDom (t : ℝ) (x : M) : Set (CovJetFiber I 0 (r + s) (2 * p) x) :=
  (jetFlat g r s (2 * p) x).symm ⁻¹' D.dom t x

/-- The lowered nonlinearity `F^♭(t, ζ) = ♭ F(t, ♭_J⁻¹ ζ)`. -/
def flatF (t : ℝ) (x : M) (ζ : CovJetFiber I 0 (r + s) (2 * p) x) : TensorRSSpace 0 (r + s) I x :=
  flat g r s x (D.F t x ((jetFlat g r s (2 * p) x).symm ζ))

theorem localDom_flat (x₀ : M) :
    localDom 0 (r + s) (2 * p) D.T₀ (D.flatDom g) x₀ =
      localSlab (I := I) 0 (r + s) (2 * p) D.T₀ x₀ ∩
        flatParam g (2 * p) x₀ ⁻¹' localDom r s (2 * p) D.T₀ D.dom x₀ := by
  ext q
  constructor
  · rintro ⟨hs, hd⟩
    have hy := (mem_localSlab_iff.mp hs).2
    refine ⟨hs, mem_localSlab_iff.mpr (mem_localSlab_iff.mp hs), ?_⟩
    change jetOfModel r s (2 * p) x₀ q.2.1 (jetFlatInvCoord g r s (2 * p) x₀ q.2.1 q.2.2) ∈
      D.dom q.1 q.2.1
    rw [← jetFlat_symm_jetOfModel g hy]
    exact hd
  · rintro ⟨hs, -, hd⟩
    have hy := (mem_localSlab_iff.mp hs).2
    refine ⟨hs, ?_⟩
    change (jetFlat g r s (2 * p) q.2.1).symm (jetOfModel 0 (r + s) (2 * p) x₀ q.2.1 q.2.2) ∈
      D.dom q.1 q.2.1
    rw [jetFlat_symm_jetOfModel g hy]
    exact hd

theorem flatDom_relOpen (x₀ : M) : ∃ U : Set (ℝ × M × JetModel E 0 (r + s) (2 * p)),
    IsOpen U ∧ localDom 0 (r + s) (2 * p) D.T₀ (D.flatDom g) x₀ =
      U ∩ localSlab (I := I) 0 (r + s) (2 * p) D.T₀ x₀ := by
  obtain ⟨U, hU, hdom⟩ := D.dom_relOpen x₀
  set B := (trivializationAt E (TangentSpace I) x₀).baseSet
  have hB : IsOpen ((Set.univ : Set ℝ) ×ˢ (B ×ˢ (Set.univ : Set (JetModel E 0 (r + s) (2 * p))))) :=
    isOpen_univ.prod ((trivializationAt E (TangentSpace I) x₀).open_baseSet.prod isOpen_univ)
  have hc : ContinuousOn (flatParam g (2 * p) x₀)
      ((Set.univ : Set ℝ) ×ˢ (B ×ˢ (Set.univ : Set (JetModel E 0 (r + s) (2 * p))))) :=
    fun q hq => (contMDiffAt_flatParam g hq.2.1).continuousAt.continuousWithinAt
  refine ⟨_ ∩ flatParam g (2 * p) x₀ ⁻¹' U, hc.isOpen_inter_preimage hB hU, ?_⟩
  rw [localDom_flat, hdom]
  ext q
  constructor
  · rintro ⟨hs, hU', -⟩
    exact ⟨⟨⟨trivial, (mem_localSlab_iff.mp hs).2, trivial⟩, hU'⟩, hs⟩
  · rintro ⟨⟨-, hU'⟩, hs⟩
    exact ⟨hs, hU', mem_localSlab_iff.mpr (mem_localSlab_iff.mp hs)⟩

theorem localRep_flatF {x₀ : M} {q : ℝ × M × JetModel E 0 (r + s) (2 * p)}
    (hq : q.2.1 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    localRep 0 (r + s) (2 * p) (D.flatF g) x₀ q =
      flatCoord g r s x₀ q.2.1 (localRep r s (2 * p) D.F x₀ (flatParam g (2 * p) x₀ q)) := by
  simp only [localRep, flatF, flatParam]
  rw [jetFlat_symm_jetOfModel g hq]
  exact (flatCoord_trivAt g (mem_trivAt_baseSet hq) _).symm

theorem flatF_smooth (x₀ : M) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, JetModel E 0 (r + s) (2 * p))))
      𝓘(ℝ, TensorRSModel 0 (r + s) ℝ E) ∞
      (localRep 0 (r + s) (2 * p) (D.flatF g) x₀)
      (localDom 0 (r + s) (2 * p) D.T₀ (D.flatDom g) x₀) := by
  intro q hq
  have hq' := hq
  rw [localDom_flat] at hq'
  have hy := (mem_localSlab_iff.mp hq'.1).2
  have hmaps : MapsTo (flatParam g (2 * p) x₀) (localDom 0 (r + s) (2 * p) D.T₀ (D.flatDom g) x₀)
      (localDom r s (2 * p) D.T₀ D.dom x₀) := fun q' hq'' => by
    rw [localDom_flat] at hq''
    exact hq''.2
  have h1 := (D.smooth x₀ _ hq'.2).comp q (contMDiffAt_flatParam g hy).contMDiffWithinAt hmaps
  have hU : (trivAt I M r s x₀).baseSet ∩ (trivAt I M 0 (r + s) x₀).baseSet ∈ 𝓝 q.2.1 :=
    ((trivAt I M r s x₀).open_baseSet.inter (trivAt I M 0 (r + s) x₀).open_baseSet).mem_nhds
      ⟨mem_trivAt_baseSet hy, mem_trivAt_baseSet hy⟩
  have hsnd := (contMDiffAt_fst (I := I) (J := 𝓘(ℝ, JetModel E 0 (r + s) (2 * p))) (n := ∞)).comp q
    (contMDiffAt_snd (I := 𝓘(ℝ, ℝ)) (J := I.prod 𝓘(ℝ, JetModel E 0 (r + s) (2 * p))) (n := ∞))
  have h2 := (((contMDiffOn_flatCoord g r s x₀).contMDiffAt hU).comp q hsnd).contMDiffWithinAt
    (s := localDom 0 (r + s) (2 * p) D.T₀ (D.flatDom g) x₀)
  refine (h2.clm_apply h1).congr (fun q' hq'' => ?_) ?_
  · rw [localDom_flat] at hq''
    exact D.localRep_flatF g (mem_localSlab_iff.mp hq''.1).2
  · exact D.localRep_flatF g hy

/-- **The lowered equation** `∂ₜ(♭u) = F^♭(t, j^{2p}(♭u))` on `T⁰_{r+s}` (`lem:lowering`). -/
def flatData : EquationData I M 0 (r + s) p where
  T₀ := D.T₀
  T₀_pos := D.T₀_pos
  dom := D.flatDom g
  F := D.flatF g
  dom_relOpen := D.flatDom_relOpen g
  smooth := D.flatF_smooth g

theorem flatData_F (t : ℝ) (x : M) (ζ : CovJetFiber I r s (2 * p) x) :
    (D.flatData g).F t x (jetFlat g r s (2 * p) x ζ) = flat g r s x (D.F t x ζ) := by
  change flat g r s x (D.F t x ((jetFlat g r s (2 * p) x).symm (jetFlat g r s (2 * p) x ζ))) = _
  rw [ContinuousLinearEquiv.symm_apply_apply]

theorem mem_flatData_dom (t : ℝ) (x : M) (ζ : CovJetFiber I r s (2 * p) x) :
    jetFlat g r s (2 * p) x ζ ∈ (D.flatData g).dom t x ↔ ζ ∈ D.dom t x := by
  change (jetFlat g r s (2 * p) x).symm (jetFlat g r s (2 * p) x ζ) ∈ D.dom t x ↔ _
  rw [ContinuousLinearEquiv.symm_apply_apply]

end EquationData

end ShortTime
