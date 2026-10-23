import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Jets of a twisted composition: the Euclidean recursion

Paper: Lemma `lem:flows` (d), the formula `j^{2p}(Π_σ u) = Θ_σ (Π_σ j^{2p} u)`, in coordinates.

Let `G j : E → F j` (`j ∈ ℕ`) be functions on an open set `Ω` satisfying the first-order recursion
`D(G j) = ins_j (G (j+1)) + K_j (G j)`: in a chart, these are the readings of the covariant
derivatives `∇^j u` of a tensor field. Let `H k : ℝ × E → F k` satisfy the same recursion in the
second variable, starting from the twisted composition `H 0 (σ, y) = Q(σ, y) G 0 (ψ(σ, y))`. Then
every `H k` is a smooth linear function of the jet `(G j (ψ(σ, y)))_{j ≤ k}`
(`exists_coef`, `exists_jetCoef`): differentiating `A(σ, y) (G_j (ψ(σ,y)))_j` in `y` gives
`∂_y A`, the derivative of `ψ`, and the recursion for `G`. If `ψ(0, ·) = id` and `Q(0, ·) = id`,
the coefficient map is the identity at `σ = 0`.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff

set_option linter.unusedSectionVars false

namespace ShortTime

namespace FlowNat

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : ℕ → Type*} [∀ j, NormedAddCommGroup (F j)] [∀ j, NormedSpace ℝ (F j)]
  [∀ j, FiniteDimensional ℝ (F j)]

variable (F) in
/-- The truncated jet space `Π_{j ≤ k} F j`. -/
abbrev Tr (k : ℕ) : Type _ := ∀ j : Fin (k + 1), F j

/-- Restriction `Π_{j ≤ k+1} F j → Π_{j ≤ k} F j`. -/
def restr (k : ℕ) : Tr F (k + 1) →L[ℝ] Tr F k :=
  ContinuousLinearMap.pi fun j : Fin (k + 1) =>
    ContinuousLinearMap.proj (R := ℝ) (φ := fun i : Fin (k + 1 + 1) => F i) j.castSucc

theorem restr_apply (k : ℕ) (ξ : Tr F (k + 1)) (j : Fin (k + 1)) :
    restr k ξ j = ξ j.castSucc := rfl

/-- The derivative of `y ↦ (G j (ψ y))_{j ≤ k}`, in terms of the jet one order higher `ξ`, the
point `z = ψ y` and the derivative `w` of `ψ`. -/
def dJet (ins : ∀ j, F (j + 1) →L[ℝ] (E →L[ℝ] F j)) (K : ∀ j, E → F j →L[ℝ] (E →L[ℝ] F j))
    (k : ℕ) (z : E) (w : E →L[ℝ] E) (ξ : Tr F (k + 1)) : E →L[ℝ] Tr F k :=
  ContinuousLinearMap.pi fun j : Fin (k + 1) =>
    (ins j (ξ j.succ) + K j z (ξ j.castSucc)).comp w

theorem dJet_apply (ins : ∀ j, F (j + 1) →L[ℝ] (E →L[ℝ] F j))
    (K : ∀ j, E → F j →L[ℝ] (E →L[ℝ] F j)) (k : ℕ) (z : E) (w : E →L[ℝ] E) (ξ : Tr F (k + 1))
    (v : E) (j : Fin (k + 1)) :
    dJet ins K k z w ξ v j = ins j (ξ j.succ) (w v) + K j z (ξ j.castSucc) (w v) := rfl

theorem dJet_add (ins : ∀ j, F (j + 1) →L[ℝ] (E →L[ℝ] F j))
    (K : ∀ j, E → F j →L[ℝ] (E →L[ℝ] F j)) (k : ℕ) (z : E) (w : E →L[ℝ] E)
    (ξ ξ' : Tr F (k + 1)) :
    dJet ins K k z w (ξ + ξ') = dJet ins K k z w ξ + dJet ins K k z w ξ' := by
  ext v j
  simp only [dJet_apply, ContinuousLinearMap.add_apply, Pi.add_apply, map_add]
  abel

theorem dJet_smul (ins : ∀ j, F (j + 1) →L[ℝ] (E →L[ℝ] F j))
    (K : ∀ j, E → F j →L[ℝ] (E →L[ℝ] F j)) (k : ℕ) (z : E) (w : E →L[ℝ] E)
    (c : ℝ) (ξ : Tr F (k + 1)) :
    dJet ins K k z w (c • ξ) = c • dJet ins K k z w ξ := by
  ext v j
  simp only [dJet_apply, ContinuousLinearMap.smul_apply, Pi.smul_apply, map_smul, smul_add]

section Recursion

variable (ins : ∀ j, F (j + 1) →L[ℝ] (E →L[ℝ] F j)) (K : ∀ j, E → F j →L[ℝ] (E →L[ℝ] F j))
  (ψ : ℝ × E → E)

/-- The `y`-derivative of `A`, along `v`. -/
def dA {k : ℕ} (A : ℝ × E → Tr F k →L[ℝ] F k) (q : ℝ × E) : E →L[ℝ] (Tr F k →L[ℝ] F k) :=
  (fderiv ℝ A q).comp (ContinuousLinearMap.inr ℝ ℝ E)

/-- The `y`-derivative of `ψ`. -/
def dψ (q : ℝ × E) : E →L[ℝ] E :=
  (fderiv ℝ ψ q).comp (ContinuousLinearMap.inr ℝ ℝ E)

/-- The next coefficient, before applying `uns`: `ξ ↦ ∂_y A (restr ξ) + A ∘ dJet ξ - K (A (restr ξ))`. -/
def nextV {k : ℕ} (A : ℝ × E → Tr F k →L[ℝ] F k) (q : ℝ × E) (ξ : Tr F (k + 1)) :
    E →L[ℝ] F k :=
  (dA A q).flip (restr k ξ) + (A q).comp (dJet ins K k (ψ q) (dψ ψ q) ξ) -
    K k q.2 (A q (restr k ξ))

theorem nextV_apply {k : ℕ} (A : ℝ × E → Tr F k →L[ℝ] F k) (q : ℝ × E) (ξ : Tr F (k + 1))
    (v : E) :
    nextV ins K ψ A q ξ v = dA A q v (restr k ξ) + A q (dJet ins K k (ψ q) (dψ ψ q) ξ v) -
      K k q.2 (A q (restr k ξ)) v := rfl

/-- `nextV` as a linear map. -/
def nextVL {k : ℕ} (A : ℝ × E → Tr F k →L[ℝ] F k) (q : ℝ × E) :
    Tr F (k + 1) →ₗ[ℝ] (E →L[ℝ] F k) where
  toFun := nextV ins K ψ A q
  map_add' ξ ξ' := by
    ext v
    simp only [nextV_apply, map_add, dJet_add, ContinuousLinearMap.add_apply]
    abel
  map_smul' c ξ := by
    ext v
    simp only [nextV_apply, map_smul, dJet_smul, ContinuousLinearMap.smul_apply,
      RingHom.id_apply, smul_sub, smul_add]

/-- The next coefficient `A_{k+1}`. -/
def nextA (uns : ∀ j, (E →L[ℝ] F j) →L[ℝ] F (j + 1)) {k : ℕ} (A : ℝ × E → Tr F k →L[ℝ] F k)
    (q : ℝ × E) : Tr F (k + 1) →L[ℝ] F (k + 1) :=
  (uns k).comp (LinearMap.toContinuousLinearMap (nextVL ins K ψ A q))

theorem nextA_apply (uns : ∀ j, (E →L[ℝ] F j) →L[ℝ] F (j + 1)) {k : ℕ}
    (A : ℝ × E → Tr F k →L[ℝ] F k) (q : ℝ × E) (ξ : Tr F (k + 1)) :
    nextA ins K ψ uns A q ξ = uns k (nextV ins K ψ A q ξ) := rfl

variable {ins K ψ}
variable {Ω : Set E} {S : Set (ℝ × E)}

theorem contDiffOn_nextA (uns : ∀ j, (E →L[ℝ] F j) →L[ℝ] F (j + 1))
    (hK : ∀ j, ContDiffOn ℝ ∞ (K j) Ω) (hS : IsOpen S) (hSΩ : ∀ q ∈ S, q.2 ∈ Ω)
    (hψ : ContDiffOn ℝ ∞ ψ S) (hψΩ : ∀ q ∈ S, ψ q ∈ Ω) {k : ℕ}
    {A : ℝ × E → Tr F k →L[ℝ] F k} (hA : ContDiffOn ℝ ∞ A S) :
    ContDiffOn ℝ ∞ (nextA ins K ψ uns A) S := by
  have hdA : ContDiffOn ℝ ∞ (fderiv ℝ A) S := hA.fderiv_of_isOpen hS (by simp)
  have hdψ : ContDiffOn ℝ ∞ (fderiv ℝ ψ) S := hψ.fderiv_of_isOpen hS (by simp)
  have hKψ : ∀ j, ContDiffOn ℝ ∞ (fun q => K j (ψ q)) S := fun j =>
    (hK j).comp hψ fun q hq => hψΩ q hq
  have hKs : ContDiffOn ℝ ∞ (fun q : ℝ × E => K k q.2) S :=
    (hK k).comp contDiffOn_snd fun q hq => hSΩ q hq
  rw [contDiffOn_clm_apply]
  intro ξ
  simp only [nextA_apply]
  refine (uns k).contDiff.comp_contDiffOn ?_
  rw [contDiffOn_clm_apply]
  intro v
  simp only [nextV_apply]
  refine ContDiffOn.sub (ContDiffOn.add ?_ ?_) ?_
  · exact (hdA.clm_apply contDiffOn_const).clm_apply contDiffOn_const
  · refine hA.clm_apply ?_
    rw [contDiffOn_pi]
    intro j
    simp only [dJet_apply]
    have hw : ContDiffOn ℝ ∞ (fun q => dψ ψ q v) S := hdψ.clm_apply contDiffOn_const
    exact (contDiffOn_const.clm_apply hw).add
      (((hKψ j).clm_apply contDiffOn_const).clm_apply hw)
  · exact (hKs.clm_apply (hA.clm_apply contDiffOn_const)).clm_apply contDiffOn_const

/-- The partial derivative in `y` of a function differentiable at `q`. -/
theorem hasFDerivAt_slice {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f : ℝ × E → X} {q : ℝ × E} (hf : DifferentiableAt ℝ f q) :
    HasFDerivAt (fun y => f (q.1, y)) ((fderiv ℝ f q).comp (ContinuousLinearMap.inr ℝ ℝ E)) q.2 :=
  hf.hasFDerivAt.comp q.2 (hasFDerivAt_prodMk_right q.1 q.2)

/-- The slice of an open set is a neighbourhood. -/
theorem slice_mem_nhds (hS : IsOpen S) {q : ℝ × E} (hq : q ∈ S) :
    {y : E | (q.1, y) ∈ S} ∈ 𝓝 q.2 :=
  (hS.preimage (Continuous.prodMk continuous_const continuous_id)).mem_nhds hq

/-- **One step of the recursion: representation.** -/
theorem nextA_rep (uns : ∀ j, (E →L[ℝ] F j) →L[ℝ] F (j + 1))
    (huns : ∀ j w, uns j (ins j w) = w)
    (G : ∀ j, E → F j) (hG : ∀ j, ∀ z ∈ Ω, HasFDerivAt (G j) (ins j (G (j + 1) z) + K j z (G j z)) z)
    (hS : IsOpen S) (hψ : ContDiffOn ℝ ∞ ψ S) (hψΩ : ∀ q ∈ S, ψ q ∈ Ω)
    (H : ∀ k, ℝ × E → F k)
    (hH : ∀ k, ∀ q ∈ S,
      HasFDerivAt (fun y => H k (q.1, y)) (ins k (H (k + 1) q) + K k q.2 (H k q)) q.2)
    {k : ℕ} {A : ℝ × E → Tr F k →L[ℝ] F k} (hA : ContDiffOn ℝ ∞ A S)
    (hrep : ∀ q ∈ S, H k q = A q (fun j => G j (ψ q))) :
    ∀ q ∈ S, H (k + 1) q = nextA ins K ψ uns A q (fun j => G j (ψ q)) := by
  intro q hq
  have hAd : DifferentiableAt ℝ A q :=
    (hA.differentiableOn (by simp)).differentiableAt (hS.mem_nhds hq)
  have hψd : DifferentiableAt ℝ ψ q :=
    (hψ.differentiableOn (by simp)).differentiableAt (hS.mem_nhds hq)
  have hAy := hasFDerivAt_slice hAd
  have hψy := hasFDerivAt_slice hψd
  -- the derivative of the truncated jet along `ψ`
  have hJ : HasFDerivAt (fun y => (fun j : Fin (k + 1) => G j (ψ (q.1, y))))
      (dJet ins K k (ψ q) (dψ ψ q) (fun j : Fin (k + 1 + 1) => G j (ψ q))) q.2 := by
    refine hasFDerivAt_pi'' fun j => ?_
    have h1 := (hG j (ψ q) (hψΩ q hq)).comp q.2 hψy
    refine h1.congr_fderiv ?_
    exact ContinuousLinearMap.ext fun v => rfl
  have hprod := hAy.clm_apply hJ
  have hev : (fun y => H k (q.1, y)) =ᶠ[𝓝 q.2]
      (fun y => A (q.1, y) (fun j : Fin (k + 1) => G j (ψ (q.1, y)))) := by
    filter_upwards [slice_mem_nhds hS hq] with y hy
    exact hrep _ hy
  have hprod' := hprod.congr_of_eventuallyEq hev
  have huniq := (hH k q hq).unique (by simpa using hprod')
  rw [nextA_apply]
  rw [← huns k (H (k + 1) q)]
  congr 1
  have hHk : H k q = A q (restr k (fun j : Fin (k + 1 + 1) => G j (ψ q))) := hrep q hq
  have hkey : ins k (H (k + 1) q) = (A q).comp (dJet ins K k (ψ q) (dψ ψ q)
      (fun j : Fin (k + 1 + 1) => G j (ψ q))) +
      (dA A q).flip (restr k (fun j : Fin (k + 1 + 1) => G j (ψ q))) - K k q.2 (H k q) := by
    rw [eq_sub_iff_add_eq, huniq]
    rfl
  rw [hkey, hHk]
  ext v
  simp only [nextV_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.flip_apply]
  abel

/-- **One step of the recursion: the identity at `σ = 0`.** -/
theorem nextA_zero (uns : ∀ j, (E →L[ℝ] F j) →L[ℝ] F (j + 1))
    (huns : ∀ j w, uns j (ins j w) = w)
    (hS : IsOpen S) (hψ : ContDiffOn ℝ ∞ ψ S)
    (hψ0 : ∀ q ∈ S, q.1 = 0 → ψ q = q.2)
    {k : ℕ} {A : ℝ × E → Tr F k →L[ℝ] F k} (hA : ContDiffOn ℝ ∞ A S)
    (h0 : ∀ q ∈ S, q.1 = 0 → ∀ ζ, A q ζ = ζ (Fin.last k)) :
    ∀ q ∈ S, q.1 = 0 → ∀ ζ, nextA ins K ψ uns A q ζ = ζ (Fin.last (k + 1)) := by
  intro q hq hq0 ξ
  -- `A(0, ·)` is constant and `ψ(0, ·) = id` near `q.2`
  have hconst : ∀ q' ∈ S, q'.1 = 0 → A q' = A q := by
    intro q' hq' hq'0
    refine ContinuousLinearMap.ext fun ζ => ?_
    rw [h0 q' hq' hq'0, h0 q hq hq0]
  have hAd : DifferentiableAt ℝ A q :=
    (hA.differentiableOn (by simp)).differentiableAt (hS.mem_nhds hq)
  have hψd : DifferentiableAt ℝ ψ q :=
    (hψ.differentiableOn (by simp)).differentiableAt (hS.mem_nhds hq)
  have hdA0 : dA A q = 0 := by
    have h1 := hasFDerivAt_slice hAd
    have h2 : HasFDerivAt (fun y => A (q.1, y)) (0 : E →L[ℝ] (Tr F k →L[ℝ] F k)) q.2 := by
      refine (hasFDerivAt_const (A q) q.2).congr_of_eventuallyEq ?_
      filter_upwards [slice_mem_nhds hS hq] with y hy
      exact hconst _ hy hq0
    exact h1.unique h2
  have hdψ0 : dψ ψ q = ContinuousLinearMap.id ℝ E := by
    have h1 := hasFDerivAt_slice hψd
    have h2 : HasFDerivAt (fun y => ψ (q.1, y)) (ContinuousLinearMap.id ℝ E) q.2 := by
      refine (hasFDerivAt_id q.2).congr_of_eventuallyEq ?_
      filter_upwards [slice_mem_nhds hS hq] with y hy
      exact hψ0 _ hy hq0
    exact h1.unique h2
  rw [nextA_apply]
  have hV : nextV ins K ψ A q ξ = ins k (ξ (Fin.last (k + 1))) := by
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [nextV_apply, hdA0, h0 q hq hq0, dJet_apply, hdψ0, hψ0 q hq hq0,
      ContinuousLinearMap.zero_apply, zero_add, ContinuousLinearMap.id_apply, restr_apply]
    exact add_sub_cancel_right _ _
  rw [hV, huns]

variable (ins K ψ) in
/-- **The coefficient maps** `A_k(q) : Π_{j ≤ k} F j → F k`. -/
def coefA (uns : ∀ j, (E →L[ℝ] F j) →L[ℝ] F (j + 1)) (Q : ℝ × E → F 0 →L[ℝ] F 0) :
    (k : ℕ) → ℝ × E → Tr F k →L[ℝ] F k
  | 0 => fun q => (Q q).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun j : Fin 1 => F j) 0)
  | k + 1 => nextA ins K ψ uns (coefA uns Q k)

theorem contDiffOn_coefA (uns : ∀ j, (E →L[ℝ] F j) →L[ℝ] F (j + 1))
    (hK : ∀ j, ContDiffOn ℝ ∞ (K j) Ω) (hS : IsOpen S) (hSΩ : ∀ q ∈ S, q.2 ∈ Ω)
    (hψ : ContDiffOn ℝ ∞ ψ S) (hψΩ : ∀ q ∈ S, ψ q ∈ Ω)
    {Q : ℝ × E → F 0 →L[ℝ] F 0} (hQ : ContDiffOn ℝ ∞ Q S) :
    ∀ k, ContDiffOn ℝ ∞ (coefA ins K ψ uns Q k) S
  | 0 => hQ.clm_comp contDiffOn_const
  | k + 1 => contDiffOn_nextA uns hK hS hSΩ hψ hψΩ (contDiffOn_coefA uns hK hS hSΩ hψ hψΩ hQ k)

theorem coefA_zero (uns : ∀ j, (E →L[ℝ] F j) →L[ℝ] F (j + 1))
    (huns : ∀ j w, uns j (ins j w) = w)
    (hK : ∀ j, ContDiffOn ℝ ∞ (K j) Ω) (hS : IsOpen S) (hSΩ : ∀ q ∈ S, q.2 ∈ Ω)
    (hψ : ContDiffOn ℝ ∞ ψ S) (hψΩ : ∀ q ∈ S, ψ q ∈ Ω)
    (hψ0 : ∀ q ∈ S, q.1 = 0 → ψ q = q.2)
    {Q : ℝ × E → F 0 →L[ℝ] F 0} (hQ : ContDiffOn ℝ ∞ Q S)
    (hQ0 : ∀ q ∈ S, q.1 = 0 → Q q = ContinuousLinearMap.id ℝ (F 0)) :
    ∀ k, ∀ q ∈ S, q.1 = 0 → ∀ ζ, coefA ins K ψ uns Q k q ζ = ζ (Fin.last k)
  | 0 => by
    intro q hq hq0 ζ
    change Q q (ζ 0) = ζ 0
    rw [hQ0 q hq hq0]
    rfl
  | k + 1 => nextA_zero uns huns hS hψ hψ0 (contDiffOn_coefA uns hK hS hSΩ hψ hψΩ hQ k)
      (coefA_zero uns huns hK hS hSΩ hψ hψΩ hψ0 hQ hQ0 k)

theorem coefA_rep (uns : ∀ j, (E →L[ℝ] F j) →L[ℝ] F (j + 1))
    (huns : ∀ j w, uns j (ins j w) = w)
    (hK : ∀ j, ContDiffOn ℝ ∞ (K j) Ω)
    (G : ∀ j, E → F j) (hG : ∀ j, ∀ z ∈ Ω, HasFDerivAt (G j) (ins j (G (j + 1) z) + K j z (G j z)) z)
    (hS : IsOpen S) (hSΩ : ∀ q ∈ S, q.2 ∈ Ω)
    (hψ : ContDiffOn ℝ ∞ ψ S) (hψΩ : ∀ q ∈ S, ψ q ∈ Ω)
    {Q : ℝ × E → F 0 →L[ℝ] F 0} (hQ : ContDiffOn ℝ ∞ Q S)
    (H : ∀ k, ℝ × E → F k)
    (hH0 : ∀ q ∈ S, H 0 q = Q q (G 0 (ψ q)))
    (hH : ∀ k, ∀ q ∈ S,
      HasFDerivAt (fun y => H k (q.1, y)) (ins k (H (k + 1) q) + K k q.2 (H k q)) q.2) :
    ∀ k, ∀ q ∈ S, H k q = coefA ins K ψ uns Q k q (fun j => G j (ψ q))
  | 0 => fun q hq => (hH0 q hq).trans rfl
  | k + 1 => nextA_rep uns huns G hG hS hψ hψΩ H hH (contDiffOn_coefA uns hK hS hSΩ hψ hψΩ hQ k)
      (coefA_rep uns huns hK G hG hS hSΩ hψ hψΩ hQ H hH0 hH k)

/-- Truncation `Π_{j ≤ N} F j → Π_{j ≤ k} F j`. -/
def trunc (N : ℕ) (k : Fin (N + 1)) : Tr F N →L[ℝ] Tr F k :=
  ContinuousLinearMap.pi fun j : Fin ((k : ℕ) + 1) =>
    ContinuousLinearMap.proj (R := ℝ) (φ := fun i : Fin (N + 1) => F i) (Fin.castLE k.isLt j)

theorem trunc_apply (N : ℕ) (k : Fin (N + 1)) (ζ : Tr F N) (j : Fin ((k : ℕ) + 1)) :
    trunc N k ζ j = ζ (Fin.castLE k.isLt j) := rfl

variable (ins K ψ) in
/-- **The jet coefficient map** `Ã(q) : Π_{j ≤ N} F j → Π_{k ≤ N} F k`. -/
def jetCoef (uns : ∀ j, (E →L[ℝ] F j) →L[ℝ] F (j + 1)) (Q : ℝ × E → F 0 →L[ℝ] F 0) (N : ℕ)
    (q : ℝ × E) : Tr F N →L[ℝ] Tr F N :=
  ContinuousLinearMap.pi fun k : Fin (N + 1) => (coefA ins K ψ uns Q k q).comp (trunc N k)

theorem jetCoef_apply (uns : ∀ j, (E →L[ℝ] F j) →L[ℝ] F (j + 1)) (Q : ℝ × E → F 0 →L[ℝ] F 0)
    (N : ℕ) (q : ℝ × E) (ζ : Tr F N) (k : Fin (N + 1)) :
    jetCoef ins K ψ uns Q N q ζ k = coefA ins K ψ uns Q k q (trunc N k ζ) := rfl

theorem contDiffOn_jetCoef (uns : ∀ j, (E →L[ℝ] F j) →L[ℝ] F (j + 1))
    (hK : ∀ j, ContDiffOn ℝ ∞ (K j) Ω) (hS : IsOpen S) (hSΩ : ∀ q ∈ S, q.2 ∈ Ω)
    (hψ : ContDiffOn ℝ ∞ ψ S) (hψΩ : ∀ q ∈ S, ψ q ∈ Ω)
    {Q : ℝ × E → F 0 →L[ℝ] F 0} (hQ : ContDiffOn ℝ ∞ Q S) (N : ℕ) :
    ContDiffOn ℝ ∞ (jetCoef ins K ψ uns Q N) S := by
  rw [contDiffOn_clm_apply]
  intro ζ
  rw [contDiffOn_pi]
  intro k
  exact (contDiffOn_coefA uns hK hS hSΩ hψ hψΩ hQ k).clm_apply contDiffOn_const

theorem jetCoef_zero (uns : ∀ j, (E →L[ℝ] F j) →L[ℝ] F (j + 1))
    (huns : ∀ j w, uns j (ins j w) = w)
    (hK : ∀ j, ContDiffOn ℝ ∞ (K j) Ω) (hS : IsOpen S) (hSΩ : ∀ q ∈ S, q.2 ∈ Ω)
    (hψ : ContDiffOn ℝ ∞ ψ S) (hψΩ : ∀ q ∈ S, ψ q ∈ Ω)
    (hψ0 : ∀ q ∈ S, q.1 = 0 → ψ q = q.2)
    {Q : ℝ × E → F 0 →L[ℝ] F 0} (hQ : ContDiffOn ℝ ∞ Q S)
    (hQ0 : ∀ q ∈ S, q.1 = 0 → Q q = ContinuousLinearMap.id ℝ (F 0)) (N : ℕ)
    {q : ℝ × E} (hq : q ∈ S) (hq0 : q.1 = 0) :
    jetCoef ins K ψ uns Q N q = ContinuousLinearMap.id ℝ (Tr F N) := by
  refine ContinuousLinearMap.ext fun ζ => funext fun k => ?_
  rw [jetCoef_apply]
  exact coefA_zero uns huns hK hS hSΩ hψ hψΩ hψ0 hQ hQ0 k q hq hq0 (trunc N k ζ)

/-- **Jets of a twisted composition**: `(H k q)_{k ≤ N} = Ã(q) (G j (ψ q))_{j ≤ N}`. -/
theorem jetCoef_rep (uns : ∀ j, (E →L[ℝ] F j) →L[ℝ] F (j + 1))
    (huns : ∀ j w, uns j (ins j w) = w)
    (hK : ∀ j, ContDiffOn ℝ ∞ (K j) Ω)
    (G : ∀ j, E → F j) (hG : ∀ j, ∀ z ∈ Ω, HasFDerivAt (G j) (ins j (G (j + 1) z) + K j z (G j z)) z)
    (hS : IsOpen S) (hSΩ : ∀ q ∈ S, q.2 ∈ Ω)
    (hψ : ContDiffOn ℝ ∞ ψ S) (hψΩ : ∀ q ∈ S, ψ q ∈ Ω)
    {Q : ℝ × E → F 0 →L[ℝ] F 0} (hQ : ContDiffOn ℝ ∞ Q S)
    (H : ∀ k, ℝ × E → F k)
    (hH0 : ∀ q ∈ S, H 0 q = Q q (G 0 (ψ q)))
    (hH : ∀ k, ∀ q ∈ S,
      HasFDerivAt (fun y => H k (q.1, y)) (ins k (H (k + 1) q) + K k q.2 (H k q)) q.2)
    (N : ℕ) {q : ℝ × E} (hq : q ∈ S) :
    (fun k : Fin (N + 1) => H k q) = jetCoef ins K ψ uns Q N q (fun j => G j (ψ q)) := by
  funext k
  rw [jetCoef_apply]
  exact coefA_rep uns huns hK G hG hS hSΩ hψ hψΩ hQ H hH0 hH k q hq

end Recursion

end FlowNat

end ShortTime
