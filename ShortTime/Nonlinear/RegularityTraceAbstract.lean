import ShortTime.Nonlinear.AngenentIFT
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-!
# Angenent's trick with an initial trace, abstract form

Paper: `thm:C`, Step 2 (regularity with a neighbourhood uniform in the initial datum).

`Angenent.exists_contDiffAt_of_natural` works on a complete subspace `Z` (for us `𝒫^m_0`), so the
neighbourhood of `0` that it produces is a neighbourhood in `Z`: perturbations must vanish at `t = 0`.
To control perturbations of the initial datum as well, we apply the same lemma on all of `X` to the
map `U ↦ (A U - 𝒩 U, [U])` with values in `Y × X/S`, where `S` is the closed subspace of zero-start
elements and `[U]` is the class of `U` modulo `S` (the trace).  The linearisation at `W`,
`z ↦ (A z - D𝒩(W) z, [z])`, is an isomorphism `X ≃L Y × X/S` as soon as `A - D𝒩(W) : S ≃L Y` is
(`traceEquiv`).  The families `P σ` preserve `S`, so they act on `X/S` (`quotMap`).

Result (`exists_contDiffAt_of_natural_trace`): for `v` in a neighbourhood of `0` *in `X`*,

  `σ ↦ Q σ (A(W+v) - 𝒩(W+v))` and `σ ↦ [P σ (W+v)]` are `C^k` at `σ`  ⟹  `σ ↦ P σ v` is `C^k` at `σ`.
-/

noncomputable section

open Set Filter Topology Metric

namespace ShortTime

namespace Angenent

section Quot

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  (S : Submodule ℝ X) [IsClosed (S : Set X)]

/-- The action of an operator preserving `S` on the quotient `X / S`. -/
def quotMap (T : X →L[ℝ] X) (h : ∀ z ∈ S, T z ∈ S) : X ⧸ S →L[ℝ] X ⧸ S :=
  S.liftQL (S.mkQL.comp T) (fun z hz => LinearMap.mem_ker.2
    ((Submodule.Quotient.mk_eq_zero S).2 (h z hz)))

theorem quotMap_mk (T : X →L[ℝ] X) (h : ∀ z ∈ S, T z ∈ S) (x : X) :
    quotMap S T h (S.mkQ x) = S.mkQ (T x) := rfl

end Quot

section Equiv

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
  (S : Submodule ℝ X) [IsClosed (S : Set X)]

/-- If `Ψ : S ≃L Y` is the restriction of `B : X →L Y`, then `x ↦ (B x, [x])` is an isomorphism
`X ≃L Y × X/S`. -/
def traceEquiv (B : X →L[ℝ] Y) (Ψ : S ≃L[ℝ] Y) (hΨ : ∀ z : S, Ψ z = B z) :
    X ≃L[ℝ] Y × (X ⧸ S) :=
  ContinuousLinearEquiv.ofBijective (B.prod S.mkQL)
    (LinearMap.ker_eq_bot'.2 (fun x hx => by
      have h1 : B x = 0 := congrArg Prod.fst hx
      have h2 : S.mkQ x = 0 := congrArg Prod.snd hx
      have hxS : x ∈ S := (Submodule.Quotient.mk_eq_zero S).1 h2
      have h3 : Ψ ⟨x, hxS⟩ = 0 := by rw [hΨ]; exact h1
      have h4 : (⟨x, hxS⟩ : S) = 0 := Ψ.injective (by rw [h3, map_zero])
      exact congrArg Subtype.val h4))
    (LinearMap.range_eq_top.2 (fun q => by
      obtain ⟨y, c⟩ := q
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective S c
      refine ⟨b + (Ψ.symm (y - B b) : X), Prod.ext ?_ ?_⟩
      · change B (b + (Ψ.symm (y - B b) : X)) = y
        have h := hΨ (Ψ.symm (y - B b))
        rw [Ψ.apply_symm_apply] at h
        rw [map_add, ← h]
        abel
      · change S.mkQ (b + (Ψ.symm (y - B b) : X)) = Submodule.Quotient.mk b
        rw [map_add, show S.mkQ (Ψ.symm (y - B b) : X) = 0 from
          (Submodule.Quotient.mk_eq_zero S).2 (Ψ.symm (y - B b)).2, add_zero]
        rfl))

theorem traceEquiv_apply (B : X →L[ℝ] Y) (Ψ : S ≃L[ℝ] Y) (hΨ : ∀ z : S, Ψ z = B z) (x : X) :
    traceEquiv S B Ψ hΨ x = (B x, S.mkQ x) := rfl

end Equiv

variable {Λ X Y : Type*} [NormedAddCommGroup Λ] [NormedSpace ℝ Λ] [CompleteSpace Λ]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

/-- **Angenent's trick with an initial trace, abstract form.** See the module docstring. -/
theorem exists_contDiffAt_of_natural_trace (S : Submodule ℝ X) [IsClosed (S : Set X)]
    (A : X →L[ℝ] Y) (P : Λ → X →L[ℝ] X) (Q : Λ → Y →L[ℝ] Y) (W : X) (𝒩 : X → Y)
    (𝒩' : Λ × X → Y) {k : WithTop ℕ∞} (hk : k ≠ 0) {r : ℝ} (hr : 0 < r)
    (h𝒩' : ContDiffOn ℝ k 𝒩' (ball ((0 : Λ), W) r))
    (hPW : ContDiff ℝ k fun σ => P σ W)
    (hP0 : P 0 = ContinuousLinearMap.id ℝ X) (hQ0 : Q 0 = ContinuousLinearMap.id ℝ Y)
    (hPS : ∀ σ, ∀ z ∈ S, P σ z ∈ S)
    {ρ₀ C : ℝ} (hρ₀ : 0 < ρ₀) (hPb : ∀ σ : Λ, ‖σ‖ < ρ₀ → ∀ x, ‖P σ x‖ ≤ C * ‖x‖)
    (hA : ∀ σ x, Q σ (A x) = A (P σ x))
    {ρ₁ r₁ : ℝ} (hρ₁ : 0 < ρ₁) (hr₁ : 0 < r₁)
    (hnat : ∀ σ : Λ, ‖σ‖ < ρ₁ → ∀ u, dist u W < r₁ → 𝒩' (σ, P σ u) = Q σ (𝒩 u))
    (hd𝒩 : DifferentiableAt ℝ 𝒩 W)
    (Φ₀ : S ≃L[ℝ] Y) (hΦ₀ : ∀ z : S, Φ₀ z = A z - fderiv ℝ 𝒩 W z) :
    ∃ V ∈ 𝓝 (0 : X), ∃ ρ > 0, ∀ v ∈ V, ∀ σ ∈ ball (0 : Λ) ρ,
      ContDiffAt ℝ k (fun τ => Q τ (A (W + v) - 𝒩 (W + v))) σ →
      ContDiffAt ℝ k (fun τ => S.mkQ (P τ (W + v))) σ →
        ContDiffAt ℝ k (fun τ => P τ v) σ := by
  haveI : CompleteSpace (⊤ : Submodule ℝ X) :=
    (show IsClosed ((⊤ : Submodule ℝ X) : Set X) by simp).completeSpace_coe
  -- the linearisation is an isomorphism `X ≃L Y × X/S`
  set Φ := traceEquiv S (A - fderiv ℝ 𝒩 W) Φ₀ (fun z => by
    rw [hΦ₀]; rfl) with hΦ
  set Φ' : (⊤ : Submodule ℝ X) ≃L[ℝ] Y × (X ⧸ S) := Submodule.topContEquiv.trans Φ with hΦ'
  have hΦ'z : ∀ z : (⊤ : Submodule ℝ X), Φ' z = (A z - fderiv ℝ 𝒩 W z, S.mkQ z) := fun z => rfl
  -- the data on `Y × X/S`
  set Q' : Λ → (Y × (X ⧸ S)) →L[ℝ] (Y × (X ⧸ S)) :=
    fun τ => (Q τ).prodMap (quotMap S (P τ) (hPS τ)) with hQ'
  have hd𝒩'' : HasFDerivAt (fun x => (𝒩 x, (0 : X ⧸ S)))
      ((fderiv ℝ 𝒩 W).prod 0) W := hd𝒩.hasFDerivAt.prodMk (hasFDerivAt_const _ _)
  obtain ⟨V, hV, ρ, hρ, hreg⟩ := exists_contDiffAt_of_natural (⊤ : Submodule ℝ X)
    (A.prod S.mkQL) P Q' W (fun x => (𝒩 x, (0 : X ⧸ S))) (fun q => (𝒩' q, (0 : X ⧸ S))) hk hr
    (h𝒩'.prodMk contDiffOn_const) hPW hP0
    (by
      refine ContinuousLinearMap.ext fun q => Prod.ext ?_ ?_
      · simp [hQ', hQ0]
      · obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective S q.2
        show quotMap S (P 0) (hPS 0) q.2 = q.2
        rw [← hx]
        change quotMap S (P 0) (hPS 0) (S.mkQ x) = S.mkQ x
        rw [quotMap_mk]
        simp [hP0])
    (fun σ z _ => Submodule.mem_top) hρ₀ hPb
    (fun σ x => Prod.ext (hA σ x) (quotMap_mk S (P σ) (hPS σ) x))
    hρ₁ hr₁
    (fun σ hσ u hu => Prod.ext (hnat σ hσ u hu) (by simp [hQ']))
    Φ' (fun z => by
      rw [hΦ'z, hd𝒩''.fderiv]
      ext1
      · simp
      · simp)
  refine ⟨(fun x : X => (⟨x, Submodule.mem_top⟩ : (⊤ : Submodule ℝ X))) ⁻¹' V,
    ?_, ρ, hρ, fun v hv σ hσ hf hmk => ?_⟩
  · refine (Continuous.subtype_mk continuous_id (fun x => Submodule.mem_top)).continuousAt.preimage_mem_nhds ?_
    exact hV
  · refine hreg ⟨v, Submodule.mem_top⟩ hv σ hσ ?_
    have hfun : (fun τ => Q' τ ((A.prod S.mkQL) (W + v) - (𝒩 (W + v), (0 : X ⧸ S)))) =
        fun τ => (Q τ (A (W + v) - 𝒩 (W + v)), S.mkQ (P τ (W + v))) := by
      funext τ
      ext1
      · simp [hQ']
      · show quotMap S (P τ) (hPS τ) (S.mkQ (W + v) - 0) = S.mkQ (P τ (W + v))
        rw [sub_zero, quotMap_mk]
    change ContDiffAt ℝ k (fun τ => Q' τ ((A.prod S.mkQL) (W + v) - (𝒩 (W + v), (0 : X ⧸ S)))) σ
    rw [hfun]
    exact hf.prodMk hmk

end Angenent

end ShortTime
