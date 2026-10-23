import ShortTime.Nonlinear.Flows
import ShortTime.Linear.LimitSmooth

/-!
# The derivative of the horizontal pullback at `σ = 0`

Paper: Lemma `lem:flows` (a), the derivative formula for one vector field:
`d/dσ|_{σ=0} Π_σ u = ∇_X u` (`hasDerivAt_hpull_zero`), with `∇_X u = (insField X)(∇u)`.

Proof, in the trivialization `e` at `x`. Write `w(σ)` for the coordinates of `(Π_σ u)(x)`, `c(σ)`
for those of `u(φ_σ x)`, and `B(σ, v)` for those of `P_σ(x) v`. Then `c(σ) = B(σ, w(σ))`, `B` is
smooth with `B(0, ·) = id`, and `∂_σ B(0, v) = -A v`, where `A` is the connection form along the
flow line (`P_σ(x) v` is parallel). The coordinate formula for `∇_{φ'} u` gives
`c'(0) = (∇_X u)(x) - A c(0)`, so `w'(0) = c'(0) + A w(0) = (∇_X u)(x)`.

We also record uniform jet bounds of `Π_σ u` for `|σ| ≤ 1` (`exists_jet_bound_hpull`).
-/

noncomputable section

open Bundle Manifold Set Filter
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Analysis.ODE
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

namespace ShortTime

namespace HFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

variable (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
variable (g : SmoothRiemannianMetric I M) (s : ℕ)

/-- Uniform jet bounds of `Π_σ u` for `|σ| ≤ 1`. -/
theorem exists_jet_bound_hpull (u : SmoothCcTensor g 0 s) :
    ∃ B : ℕ → ℝ, (∀ i, 0 ≤ B i) ∧
      ∀ i σ, σ ∈ Icc (-1 : ℝ) 1 → ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g 0 (s + i) x
          ((iteratedCovGrad (I := I) g 0 s i (hpull X g s σ u)).toSection x) ≤ B i :=
  Vendor.joint_jet_bdd g 0 s (fun σ => hpull X g s σ u) isCompact_Icc (subset_univ _)
    (jointlySmoothOn_hpull_param X g s u)

/-- The derivative at `σ = 0` in a trivialization at `x`. -/
theorem hasDerivAt_hpullFib_coord (u : SmoothCcTensor g 0 s) (x : M)
    (e : Trivialization (TensorRSModel 0 s ℝ E)
      (TotalSpace.proj : TotalSpace (TensorRSModel 0 s ℝ E)
        (fun x : M => TensorRSSpace 0 s I x) → M)) [MemTrivializationAtlas e]
    (hxe : x ∈ e.baseSet) :
    HasDerivAt (fun σ => (e ⟨x, hpullFib X g s σ u x⟩).2)
      ((e ⟨x, (covT g s) (fun z => u.toSection z) x (X x)⟩).2) 0 := by
  have h0 : flow X 0 x = x := flow_zero X x
  have h0e : flow X 0 x ∈ e.baseSet := h0.symm ▸ hxe
  have hcurve := contMDiff_flow_curve X x
  -- `w`: the coordinates of `(Π_σ u)(x)`
  obtain ⟨w, hw⟩ : ∃ w : ℝ → TensorRSModel 0 s ℝ E,
      ∀ σ, w σ = (e ⟨x, hpullFib X g s σ u x⟩).2 := ⟨_, fun _ => rfl⟩
  have hwfun : (fun σ => (e ⟨x, hpullFib X g s σ u x⟩).2) = w := funext fun σ => (hw σ).symm
  rw [hwfun]
  have hwd : DifferentiableAt ℝ w 0 := by
    have h1 : ContMDiff 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
        (fun σ : ℝ => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
          (E := fun z : M => TensorRSSpace 0 s I z) x (hpullFib X g s σ u x)) :=
      (jointlySmoothOn_hpull_param X g s u).comp_contMDiff
        (contMDiff_const.prodMk contMDiff_id) (fun _ => ⟨mem_univ _, mem_univ _⟩)
    have h2 := ((e.contMDiffAt_iff (e.mem_source.mpr hxe)).mp (h1 0)).2
    rw [hwfun] at h2
    exact (contMDiffAt_iff_contDiffAt.mp h2).differentiableAt (by simp)
  -- `B`: the coordinates of parallel transport
  obtain ⟨B, hB⟩ : ∃ B : ℝ × TensorRSModel 0 s ℝ E → TensorRSModel 0 s ℝ E,
      ∀ p, B p = (e ⟨flow X p.1 x,
        ptRaw X g s p.1 x (e.symmL ℝ (flow X 0 x) p.2)⟩).2 := ⟨_, fun _ => rfl⟩
  have hBsm : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, TensorRSModel 0 s ℝ E))
      (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun p : ℝ × TensorRSModel 0 s ℝ E =>
        (⟨flow X p.1 x, ptRaw X g s p.1 x (e.symmL ℝ (flow X 0 x) p.2)⟩ :
          TotalSpace (TensorRSModel 0 s ℝ E) (fun z : M => TensorRSSpace 0 s I z))) :=
    (ptRaw_forward X g s e).comp_contMDiff
      ((contMDiff_fst.prodMk contMDiff_const).prodMk contMDiff_snd) (fun _ => ⟨mem_univ _, h0e⟩)
  have hBd : DifferentiableAt ℝ B (0, w 0) := by
    have h2 := ((e.contMDiffAt_iff (e.mem_source.mpr h0e)).mp (hBsm (0, w 0))).2
    have hBfun : (fun p : ℝ × TensorRSModel 0 s ℝ E => (e ⟨flow X p.1 x,
        ptRaw X g s p.1 x (e.symmL ℝ (flow X 0 x) p.2)⟩).2) = B := funext fun p => (hB p).symm
    rw [hBfun, ← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h2
    exact (contMDiffAt_iff_contDiffAt.mp h2).differentiableAt (by simp)
  have hB0 : ∀ v, B (0, v) = v := by
    intro v
    rw [hB]
    simp only
    rw [ptRaw_zero, ← e.continuousLinearMapAt_apply_of_mem ℝ h0e,
      e.continuousLinearMapAt_symmL h0e]
  have hBw : ∀ σ, B (σ, w σ) = (e ⟨flow X σ x, u.toSection (flow X σ x)⟩).2 := by
    intro σ
    rw [hB, hw]
    simp only
    rw [mk_hpullFib, symmL_coord e h0e, ContinuousLinearEquiv.apply_symm_apply]
  -- the curve and its velocity
  have hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I (fun σ => flow X σ x) univ 0 :=
    ((hcurve.mdifferentiable (by simp)) 0).mdifferentiableWithinAt
  -- the coordinates `c` of `u` along the flow line
  have hZ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E))
      (fun σ => (⟨flow X σ x, u.toSection (flow X σ x)⟩ :
        TotalSpace (TensorRSModel 0 s ℝ E) (fun z : M => TensorRSSpace 0 s I z))) univ 0 :=
    (((u.toSection.contMDiff.comp hcurve).mdifferentiable (by simp)) 0).mdifferentiableWithinAt
  have hsec : (covT g s).derivAlongWithin (fun σ => flow X σ x)
      (fun σ => u.toSection (flow X σ x)) univ 0 =
      (covT g s) (fun z => u.toSection z) (flow X 0 x) (X (flow X 0 x)) := by
    rw [← mfderiv_flow_curve X x 0]
    exact (covT g s).derivAlongWithin_section (σ := fun z => u.toSection z) hγ
      ((u.toSection.contMDiff.mdifferentiable (by simp)) _)
  have hc := (covT g s).hasDerivWithinAt_coord (γ := fun σ => flow X σ x)
    (Z := fun σ => u.toSection (flow X σ x)) e h0e hZ
  rw [hsec, mfderiv_flow_curve] at hc
  -- the parallel section through `e.symmL (w 0)`
  have hP : MDifferentiableWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E))
      (fun σ => (⟨flow X σ x, ptRaw X g s σ x (e.symmL ℝ (flow X 0 x) (w 0))⟩ :
        TotalSpace (TensorRSModel 0 s ℝ E) (fun z : M => TensorRSSpace 0 s I z))) univ 0 :=
    (((hBsm.comp (contMDiff_id.prodMk contMDiff_const)).mdifferentiable (by simp))
      0).mdifferentiableWithinAt
  have hpar := (covT g s).hasDerivWithinAt_coord (γ := fun σ => flow X σ x)
    (Z := fun σ => ptRaw X g s σ x (e.symmL ℝ (flow X 0 x) (w 0))) e h0e hP
  rw [ptRaw_parallel, mfderiv_flow_curve, ptRaw_zero, e.continuousLinearMapAt_symmL h0e,
    map_zero, zero_sub] at hpar
  generalize (covT g s).connectionForm e (flow X 0 x) (X (flow X 0 x)) = A at hc hpar
  -- eventually, the coordinates `e.continuousLinearMapAt` agree with `e`
  have hev : ∀ᶠ σ in 𝓝 (0 : ℝ), flow X σ x ∈ e.baseSet :=
    hcurve.continuous.continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds h0e)
  have hc' : HasDerivAt (fun σ => B (σ, w σ))
      (e.continuousLinearMapAt ℝ (flow X 0 x)
          ((covT g s) (fun z => u.toSection z) (flow X 0 x) (X (flow X 0 x))) -
        A (e.continuousLinearMapAt ℝ (flow X 0 x) (u.toSection (flow X 0 x)))) 0 := by
    refine (hasDerivWithinAt_univ.mp hc).congr_of_eventuallyEq ?_
    filter_upwards [hev] with σ hσ
    rw [hBw, e.continuousLinearMapAt_apply_of_mem ℝ hσ]
  have hpar' : HasDerivAt (fun σ => B (σ, w 0)) (-A (w 0)) 0 := by
    refine (hasDerivWithinAt_univ.mp hpar).congr_of_eventuallyEq ?_
    filter_upwards [hev] with σ hσ
    rw [hB, e.continuousLinearMapAt_apply_of_mem ℝ hσ]
  -- the chain rule
  have hBf := hBd.hasFDerivAt
  generalize fderiv ℝ B (0, w 0) = L at hBf
  have hw' := hwd.hasDerivAt
  generalize deriv w 0 = w' at hw'
  have hchain : HasDerivAt (fun σ => B (σ, w σ)) (L (1, w')) 0 :=
    hBf.comp_hasDerivAt (x := 0) ((hasDerivAt_id' 0).prodMk hw')
  have hchain0 : HasDerivAt (fun σ => B (σ, w 0)) (L (1, 0)) 0 :=
    hBf.comp_hasDerivAt (x := 0) ((hasDerivAt_id' 0).prodMk (hasDerivAt_const 0 (w 0)))
  have hL1 : L (1, w') = _ := hchain.unique hc'
  have hL10 : L (1, 0) = -A (w 0) := hchain0.unique hpar'
  have hL0 : L (0, w') = w' := by
    have h1 : HasFDerivAt (fun v => B (0, v)) (L.comp (ContinuousLinearMap.inr ℝ ℝ _)) (w 0) :=
      hBf.comp (w 0) (hasFDerivAt_prodMk_right (0 : ℝ) (w 0))
    have h2 : HasFDerivAt (fun v => B (0, v)) (ContinuousLinearMap.id ℝ _) (w 0) := by
      have : (fun v => B (0, v)) = id := funext hB0
      rw [this]
      exact hasFDerivAt_id _
    have h3 := congrArg (fun T => T w') (h1.unique h2)
    simpa using h3
  have hsplit : L (1, w') = L (1, 0) + L (0, w') := by
    rw [← map_add, Prod.mk_add_mk, add_zero, zero_add]
  have hw0 : w 0 = e.continuousLinearMapAt ℝ (flow X 0 x) (u.toSection (flow X 0 x)) := by
    rw [← hB0 (w 0), hBw, e.continuousLinearMapAt_apply_of_mem ℝ h0e]
  have hw'eq : w' = e.continuousLinearMapAt ℝ (flow X 0 x)
      ((covT g s) (fun z => u.toSection z) (flow X 0 x) (X (flow X 0 x))) := by
    rw [hsplit, hL10, hL0, ← hw0] at hL1
    rw [← sub_eq_iff_eq_add'.mpr hL1.symm]
    abel
  have hfin : ∀ y (hy : y = x),
      e.continuousLinearMapAt ℝ y ((covT g s) (fun z => u.toSection z) y (X y)) =
        (e ⟨x, (covT g s) (fun z => u.toSection z) x (X x)⟩).2 := by
    rintro _ rfl
    exact e.continuousLinearMapAt_apply_of_mem ℝ hxe _
  rw [← hfin _ h0, ← hw'eq]
  exact hw'

/-- **Derivative of the horizontal pullback at `σ = 0`**, in the model fibre:
`d/dσ|_{σ=0} (Π_σ u)(x) = (∇_X u)(x)`. -/
theorem hasDerivAt_hpullFib_zero (u : SmoothCcTensor g 0 s) (x : M) :
    HasDerivAt (fun σ => TensorRSSpace.toModel (hpullFib X g s σ u x))
      (TensorRSSpace.toModel ((covT g s) (fun z => u.toSection z) x (X x))) 0 := by
  obtain ⟨e, he⟩ : ∃ e, e = trivializationAt (TensorRSModel 0 s ℝ E)
      (fun z : M => TensorRSSpace 0 s I z) x := ⟨_, rfl⟩
  have : MemTrivializationAtlas e := by rw [he]; infer_instance
  have hxe : x ∈ e.baseSet := by rw [he]; exact mem_baseSet_trivializationAt _ _ _
  let Ψl : TensorRSModel 0 s ℝ E →ₗ[ℝ] TensorRSModel 0 s ℝ E :=
    { toFun := fun v => TensorRSSpace.toModel (e.symmL ℝ x v)
      map_add' := fun a b => by rw [map_add, TensorRSSpace.toModel_add]
      map_smul' := fun c a => by rw [map_smul, TensorRSSpace.toModel_smul]; rfl }
  have hΨ : ∀ v : TensorRSSpace 0 s I x,
      LinearMap.toContinuousLinearMap Ψl (e ⟨x, v⟩).2 = TensorRSSpace.toModel v := by
    intro v
    change TensorRSSpace.toModel (e.symmL ℝ x (e ⟨x, v⟩).2) = _
    rw [symmL_coord e hxe]
  have h := (LinearMap.toContinuousLinearMap Ψl).hasFDerivAt.comp_hasDerivAt (x := 0)
    (hasDerivAt_hpullFib_coord X g s u x e hxe)
  rw [hΨ] at h
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun σ => ?_)
  exact (hΨ _).symm

/-- The covariant derivative `∇_X u = (insField X)(∇u)` of a smooth tensor field along `X`. -/
def covAlong (u : SmoothCcTensor g 0 s) : SmoothCcTensor g 0 s :=
  operatorFieldApply (I := I) (M := M) g (s + 1) s (insField g X) (covGrad (I := I) (M := M) g 0 s u)

/-- **Derivative of the horizontal pullback at `σ = 0`**: `d/dσ|_{σ=0} Π_σ u = ∇_X u`,
pointwise in the model fibre. -/
theorem hasDerivAt_hpull_zero (u : SmoothCcTensor g 0 s) (x : M) :
    HasDerivAt (fun σ => TensorRSSpace.toModel ((hpull X g s σ u).toSection x))
      (TensorRSSpace.toModel ((covAlong X g s u).toSection x)) 0 := by
  have h := hasDerivAt_hpullFib_zero X g s u x
  rw [covAlong, ← covApply_eq_insField X u x]
  exact h

end HFlow

end ShortTime
