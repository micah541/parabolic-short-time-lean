import ShortTime.Nonlinear.Flows

/-!
# The group law for the horizontal pullback

Paper: Lemma `lem:flows`, the one-parameter group `Π_σ ∘ Π_τ = Π_{σ+τ}` (`hpull_hpull`).

Parallel transport along the flow line of `x` over `[0, τ + σ]` is the transport over `[0, σ]`
followed by the transport along the flow line of `φ_σ x` over `[0, τ]` (`pt_add`). Both sides are
parallel sections along `r ↦ φ_{r+σ}(x)` that agree at `r = 0`, so they agree by uniqueness of
parallel sections (`parallel_section_eq_on_interval`). The two facts used are that reparametrizing
by a shift preserves parallelism (`derivAlongWithin_flow_shift`) and so does identifying the
fibres over equal points (`derivAlongWithin_fibCast`).
-/

noncomputable section

open Bundle Manifold Set Filter
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Analysis.ODE
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Geometry.Connection
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

section Cast

variable {s : ℕ}

theorem mk_fibCast {x y : M} (h : x = y) (v : TensorRSSpace 0 s I x) :
    (⟨y, fibCast h v⟩ :
      TotalSpace (TensorRSModel 0 s ℝ E) (fun z : M => TensorRSSpace 0 s I z)) = ⟨x, v⟩ := by
  subst h
  rfl

theorem fibCast_apply_section {x y : M} (h : x = y) (u : ∀ z : M, TensorRSSpace 0 s I z) :
    fibCast h (u x) = u y := by
  subst h
  rfl

theorem fibCast_fibCast {x y z : M} (h₁ : x = y) (h₂ : y = z) (v : TensorRSSpace 0 s I x) :
    fibCast h₂ (fibCast h₁ v) = fibCast (h₁.trans h₂) v := by
  subst h₁
  subst h₂
  rfl

end Cast

variable (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
variable (g : SmoothRiemannianMetric I M) (s : ℕ)

theorem flow_add' (σ τ : ℝ) (x : M) : flow X τ (flow X σ x) = flow X (τ + σ) x := by
  rw [add_comm, flow_add]

/-- Identifying the fibres over a curve with those over an equal curve commutes with `∇_{γ'}`. -/
theorem derivAlongWithin_fibCast {γ₁ γ₂ : ℝ → M} (h : ∀ r, γ₁ r = γ₂ r)
    (Z : ∀ r, TensorRSSpace 0 s I (γ₁ r)) (J : Set ℝ) (t : ℝ) :
    (covT g s).derivAlongWithin γ₂ (fun r => fibCast (h r) (Z r)) J t =
      fibCast (h t) ((covT g s).derivAlongWithin γ₁ Z J t) := by
  obtain rfl : γ₁ = γ₂ := funext h
  rfl

/-- Shifting the parameter of a flow line commutes with `∇_{γ'}`. -/
theorem derivAlongWithin_flow_shift (p : M) (a : ℝ)
    (Z : ∀ r, TensorRSSpace 0 s I (flow X r p)) (t : ℝ) :
    (covT g s).derivAlongWithin (fun r => flow X (r + a) p) (fun r => Z (r + a)) univ t =
      (covT g s).derivAlongWithin (fun r => flow X r p) Z univ (t + a) := by
  have hm1 : mfderivWithin 𝓘(ℝ, ℝ) I (fun r => flow X (r + a) p) univ t
      ((NormedSpace.fromTangentSpace t).symm 1) = X (flow X (t + a) p) := by
    have hm := ((isMIntegralCurve_flow X p).comp_add a t).mfderiv
    rw [mfderivWithin_univ]
    change mfderiv 𝓘(ℝ, ℝ) I (fun r => flow X (r + a) p) t = _ at hm
    rw [hm]
    change (1 : ℝ) • X (flow X (t + a) p) = _
    exact one_smul ℝ _
  have hm2 := mfderiv_flow_curve X p (t + a)
  have hd : deriv (fun r => (trivializationAt (TensorRSModel 0 s ℝ E)
        (fun z : M => TensorRSSpace 0 s I z) (flow X (t + a) p)).continuousLinearMapAt ℝ
          (flow X (r + a) p) (Z (r + a))) t =
      deriv (fun r => (trivializationAt (TensorRSModel 0 s ℝ E)
        (fun z : M => TensorRSSpace 0 s I z) (flow X (t + a) p)).continuousLinearMapAt ℝ
          (flow X r p) (Z r)) (t + a) :=
    deriv_comp_add_const (fun r => (trivializationAt (TensorRSModel 0 s ℝ E)
        (fun z : M => TensorRSSpace 0 s I z) (flow X (t + a) p)).continuousLinearMapAt ℝ
          (flow X r p) (Z r)) a t
  unfold CovariantDerivative.derivAlongWithin
  simp only
  rw [hm1, hm2, derivWithin_univ, derivWithin_univ, hd]

/-- Parallel transport along a flow line is smooth in the time parameter. -/
theorem contMDiff_ptRaw_apply (p : M) (v : TensorRSSpace 0 s I (flow X 0 p)) :
    ContMDiff 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun σ => (⟨flow X σ p, ptRaw X g s σ p v⟩ :
        TotalSpace (TensorRSModel 0 s ℝ E) (fun z : M => TensorRSSpace 0 s I z))) := by
  obtain ⟨e, he⟩ : ∃ e, e = trivializationAt (TensorRSModel 0 s ℝ E)
      (fun z : M => TensorRSSpace 0 s I z) (flow X 0 p) := ⟨_, rfl⟩
  have : MemTrivializationAtlas e := by rw [he]; infer_instance
  have hp : flow X 0 p ∈ e.baseSet := by rw [he]; exact mem_baseSet_trivializationAt _ _ _
  have h := (ptRaw_forward X g s e).comp_contMDiff
    (f := fun σ : ℝ => ((σ, p), e.continuousLinearMapAt ℝ (flow X 0 p) v))
    ((contMDiff_id.prodMk contMDiff_const).prodMk contMDiff_const) (fun _ => ⟨mem_univ _, hp⟩)
  convert h using 1
  funext σ
  simp only [Function.comp_apply]
  rw [e.symmL_continuousLinearMapAt hp]

theorem pt_congr {a b : ℝ} (hab : a = b) (x : M) (v : TensorRSSpace 0 s I x) :
    pt X g s b x v = fibCast (congrArg (fun r => flow X r x) hab) (pt X g s a x v) := by
  subst hab
  rfl

/-- **Composition of parallel transports along a flow line**:
`P_{τ+σ}(x) = P_τ(φ_σ x) ∘ P_σ(x)`. -/
theorem pt_add (σ τ : ℝ) (x : M) (v : TensorRSSpace 0 s I x) :
    pt X g s (τ + σ) x v =
      fibCast (flow_add' X σ τ x) (pt X g s τ (flow X σ x) (pt X g s σ x v)) := by
  have hshift : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun r : ℝ => r + σ) :=
    (contDiff_id.add contDiff_const).contMDiff
  have hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 (fun r => flow X (r + σ) x) univ :=
    (((contMDiff_flow_curve X x).comp hshift).of_le (by norm_num)).contMDiffOn
  have hZ : MDifferentiableOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E))
      (fun r => (⟨flow X (r + σ) x, pt X g s (r + σ) x v⟩ :
        TotalSpace (TensorRSModel 0 s ℝ E) (fun z : M => TensorRSSpace 0 s I z))) univ :=
    (((contMDiff_ptRaw_apply X g s x _).comp hshift).mdifferentiable (by simp)).mdifferentiableOn
  have hW : MDifferentiableOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E))
      (fun r => (⟨flow X (r + σ) x,
        fibCast (flow_add' X σ r x) (pt X g s r (flow X σ x) (pt X g s σ x v))⟩ :
        TotalSpace (TensorRSModel 0 s ℝ E) (fun z : M => TensorRSSpace 0 s I z))) univ := by
    refine (((contMDiff_ptRaw_apply X g s (flow X σ x)
      (fibCast (flow_zero X (flow X σ x)).symm (pt X g s σ x v))).mdifferentiable
      (by simp)).mdifferentiableOn).congr fun r _ => ?_
    exact mk_fibCast _ _
  have hZpar : ∀ t ∈ (univ : Set ℝ), (covT g s).derivAlongWithin (fun r => flow X (r + σ) x)
      (fun r => pt X g s (r + σ) x v) univ t = 0 := by
    intro t _
    exact (derivAlongWithin_flow_shift X g s x σ
      (fun r => ptRaw X g s r x (fibCast (flow_zero X x).symm v)) t).trans
      (ptRaw_parallel X g s x _ (t + σ))
  have hWpar : ∀ t ∈ (univ : Set ℝ), (covT g s).derivAlongWithin (fun r => flow X (r + σ) x)
      (fun r => fibCast (flow_add' X σ r x) (pt X g s r (flow X σ x) (pt X g s σ x v)))
      univ t = 0 := by
    intro t _
    rw [derivAlongWithin_fibCast g s (γ₁ := fun r => flow X r (flow X σ x))
      (γ₂ := fun r => flow X (r + σ) x) (fun r => flow_add' X σ r x)
      (fun r => pt X g s r (flow X σ x) (pt X g s σ x v)) univ t]
    have h0 := ptRaw_parallel X g s (flow X σ x)
      (fibCast (flow_zero X (flow X σ x)).symm (pt X g s σ x v)) t
    change fibCast _ ((covT g s).derivAlongWithin (fun r => flow X r (flow X σ x))
      (fun r => ptRaw X g s r (flow X σ x)
        (fibCast (flow_zero X (flow X σ x)).symm (pt X g s σ x v))) univ t) = 0
    rw [h0, map_zero]
  have hinit : pt X g s (0 + σ) x v =
      fibCast (flow_add' X σ 0 x) (pt X g s 0 (flow X σ x) (pt X g s σ x v)) := by
    have h1 : pt X g s 0 (flow X σ x) (pt X g s σ x v) =
        fibCast (flow_zero X (flow X σ x)).symm (pt X g s σ x v) := by
      change ptRaw X g s 0 (flow X σ x) _ = _
      rw [ptRaw_zero]
      rfl
    rw [h1, fibCast_fibCast, pt_congr X g s (zero_add σ).symm]
  exact (covT g s).parallel_section_eq_on_interval inferInstance (J := univ) (t₀ := 0)
    (γ := fun r => flow X (r + σ) x) (Z := fun r => pt X g s (r + σ) x v)
    (W := fun r => fibCast (flow_add' X σ r x) (pt X g s r (flow X σ x) (pt X g s σ x v)))
    ordConnected_univ (mem_univ 0) hγ hZ hW hZpar hWpar hinit τ (mem_univ τ)

/-- **The group law** `Π_σ ∘ Π_τ = Π_{σ+τ}`. -/
theorem hpull_hpull (σ τ : ℝ) (u : SmoothCcTensor g 0 s) :
    hpull X g s σ (hpull X g s τ u) = hpull X g s (σ + τ) u := by
  rw [add_comm σ τ]
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  change (pt X g s σ x).symm ((pt X g s τ (flow X σ x)).symm
      (u.toSection (flow X τ (flow X σ x)))) =
    (pt X g s (τ + σ) x).symm (u.toSection (flow X (τ + σ) x))
  symm
  rw [ContinuousLinearEquiv.symm_apply_eq, pt_add, ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearEquiv.apply_symm_apply]
  exact (fibCast_apply_section (flow_add' X σ τ x) (fun z => u.toSection z)).symm

end HFlow

end ShortTime
