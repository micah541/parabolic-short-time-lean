import ShortTime.Analysis.JetRecursion
import Mathlib.Data.Finset.Sort
import Mathlib.Analysis.Calculus.TangentCone.Prod

/-!
# Iterated derivatives along structured directions

Bookkeeping for iterated derivatives within `S ×ˢ Ω ⊆ ℝ × E` (time × space):

* `iteratedFDerivWithin_append_const`: if `D_τ f_k = f_{k+1}`, then the derivative along
  `(a, τ, …, τ)` (`j` copies of `τ`) of `f_0` is the derivative along `a` of `f_j`.
* `iteratedFDerivWithin_prod_slice`: derivatives along purely spatial directions `(0, v)` are
  derivatives of the time slice.
* `exists_split_orderEmb`, `sum_range_ite_lt`: sub-blocks of a direction tuple of the form
  `(spatial, …, spatial, time, …, time)` have the same form.
-/

noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace ShortTime.IterDir

open ShortTime.JetRec

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y]

theorem natCast_lt_infty (n : ℕ) : (n : WithTop ℕ∞) < ∞ := by
  exact_mod_cast (ENat.natCast_lt_top n)

theorem append_apply_lt {α : Type*} {n j : ℕ} (a : Fin n → α) (b : Fin j → α) (i : Fin (n + j))
    (hi : (i : ℕ) < n) : Fin.append a b i = a ⟨i, hi⟩ := by
  have : i = Fin.castAdd j ⟨i, hi⟩ := Fin.ext rfl
  conv_lhs => rw [this]
  exact Fin.append_left a b _

theorem append_apply_ge {α : Type*} {n j : ℕ} (a : Fin n → α) (b : Fin j → α) (i : Fin (n + j))
    (hi : n ≤ (i : ℕ)) : Fin.append a b i = b ⟨i - n, by omega⟩ := by
  have : i = Fin.natAdd n ⟨i - n, by omega⟩ := Fin.ext (by simp; omega)
  conv_lhs => rw [this]
  exact Fin.append_right a b _

theorem init_append_const {α : Type*} {n j : ℕ} (a : Fin n → α) (τ : α) :
    Fin.init (n := n + j) (Fin.append a (fun _ : Fin (j + 1) => τ) : Fin (n + (j + 1)) → α) =
      Fin.append a (fun _ : Fin j => τ) := by
  funext i
  simp only [Fin.init]
  rcases Nat.lt_or_ge (i : ℕ) n with h | h
  · rw [append_apply_lt _ _ _ (by simpa using h), append_apply_lt _ _ _ h]
    rfl
  · rw [append_apply_ge _ _ _ (by simpa using h), append_apply_ge _ _ _ h]

/-- **Iterated derivatives along a constant direction.** -/
theorem iteratedFDerivWithin_append_const {s : Set X} (hs : UniqueDiffOn ℝ s) (τ : X) (n : ℕ)
    (a : Fin n → X) (j : ℕ) :
    ∀ f : ℕ → X → Y, (∀ k, ContDiffOn ℝ ∞ (f k) s) →
      (∀ k, ∀ x ∈ s, fderivWithin ℝ (f k) s x τ = f (k + 1) x) →
      ∀ x ∈ s, iteratedFDerivWithin ℝ (n + j) (f 0) s x (Fin.append a (fun _ : Fin j => τ)) =
        iteratedFDerivWithin ℝ n (f j) s x a := by
  induction j with
  | zero =>
    intro f _ _ x _
    rw [Fin.append_right_nil a _ rfl]
    rfl
  | succ j ih =>
    intro f hf hτ x hx
    show iteratedFDerivWithin ℝ (n + j + 1) (f 0) s x
      (Fin.append a (fun _ : Fin (j + 1) => τ) : Fin (n + (j + 1)) → X) = _
    rw [iteratedFDerivWithin_succ_apply_right hs hx, init_append_const,
      append_apply_ge _ _ _ (by simp)]
    have hD : ContDiffOn ℝ ∞ (fun y => fderivWithin ℝ (f 0) s y) s :=
      ((contDiffOn_infty_iff_fderivWithin hs).1 (hf 0)).2
    rw [← iteratedFDerivWithin_clm_apply_const_apply hs hD (natCast_le_infty _) hx,
      iteratedFDerivWithin_congr (f := f 1) (fun y hy => hτ 0 y hy) hx]
    exact ih (fun k => f (k + 1)) (fun k => hf (k + 1)) (fun k => hτ (k + 1)) x hx

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The derivative within a product set along a spatial direction is the derivative of the time
slice. -/
theorem fderivWithin_prod_slice {h : ℝ × E → Y} {S : Set ℝ} {Ω : Set E} (hΩ : IsOpen Ω)
    {q : ℝ × E} (hq : q ∈ S ×ˢ Ω) (hh : DifferentiableWithinAt ℝ h (S ×ˢ Ω) q) (e : E) :
    fderivWithin ℝ h (S ×ˢ Ω) q ((0 : ℝ), e) = fderivWithin ℝ (fun y => h (q.1, y)) Ω q.2 e := by
  have hin : HasFDerivAt (fun y : E => (q.1, y)) (ContinuousLinearMap.inr ℝ ℝ E) q.2 :=
    (hasFDerivAt_const q.1 q.2).prodMk (hasFDerivAt_id q.2)
  have h1 : HasFDerivWithinAt (fun y => h (q.1, y))
      ((fderivWithin ℝ h (S ×ˢ Ω) q).comp (ContinuousLinearMap.inr ℝ ℝ E)) Ω q.2 :=
    hh.hasFDerivWithinAt.comp q.2 hin.hasFDerivWithinAt
      (fun y hy => (⟨hq.1, hy⟩ : (q.1, y) ∈ S ×ˢ Ω))
  rw [h1.fderivWithin (hΩ.uniqueDiffWithinAt hq.2)]
  rfl

/-- **Spatial derivatives are derivatives of the time slice.** -/
theorem iteratedFDerivWithin_prod_slice {f : ℝ × E → Y} {S : Set ℝ} {Ω : Set E}
    (hS : UniqueDiffOn ℝ S) (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ f (S ×ˢ Ω)) (n : ℕ) :
    ∀ (v : Fin n → E), ∀ q ∈ S ×ˢ Ω,
      iteratedFDerivWithin ℝ n f (S ×ˢ Ω) q (fun m => ((0 : ℝ), v m)) =
        iteratedFDerivWithin ℝ n (fun y => f (q.1, y)) Ω q.2 v := by
  have hs : UniqueDiffOn ℝ (S ×ˢ Ω) := UniqueDiffOn.prod hS hΩ.uniqueDiffOn
  have hslice : ∀ t ∈ S, ContDiffOn ℝ ∞ (fun y => f (t, y)) Ω := fun t ht =>
    hf.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun y hy => (⟨ht, hy⟩ : (t, y) ∈ S ×ˢ Ω))
  induction n with
  | zero =>
    intro v q _
    rfl
  | succ n ih =>
    intro v q hq
    rw [iteratedFDerivWithin_succ_apply_left, iteratedFDerivWithin_succ_apply_left]
    have hd : DifferentiableWithinAt ℝ (iteratedFDerivWithin ℝ n f (S ×ˢ Ω)) (S ×ˢ Ω) q :=
      (hf.differentiableOn_iteratedFDerivWithin (natCast_lt_infty n) hs) q hq
    have hd' : DifferentiableWithinAt ℝ (iteratedFDerivWithin ℝ n (fun y => f (q.1, y)) Ω) Ω q.2 :=
      ((hslice q.1 hq.1).differentiableOn_iteratedFDerivWithin (natCast_lt_infty n)
        hΩ.uniqueDiffOn) q.2 hq.2
    rw [← fderivWithin_continuousMultilinear_apply_const_apply (hs q hq) hd,
      ← fderivWithin_continuousMultilinear_apply_const_apply (hΩ.uniqueDiffWithinAt hq.2) hd']
    have hdu : DifferentiableWithinAt ℝ
        (fun q' => iteratedFDerivWithin ℝ n f (S ×ˢ Ω) q' (Fin.tail fun m => ((0 : ℝ), v m)))
        (S ×ˢ Ω) q := by
      have := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => ℝ × E) Y
        (Fin.tail fun m => ((0 : ℝ), v m))).differentiableAt.comp_differentiableWithinAt q hd
      exact this
    rw [fderivWithin_prod_slice hΩ hq hdu]
    refine congrArg (fun L : E →L[ℝ] Y => L (v 0)) (fderivWithin_congr (fun y hy => ?_) ?_)
    · exact ih (Fin.tail v) (q.1, y) ⟨hq.1, hy⟩
    · exact ih (Fin.tail v) (q.1, q.2) ⟨hq.1, hq.2⟩

/-! ### Sorted direction tuples -/

/-- The sub-tuple of a sorted tuple along a finite set of indices is again sorted. -/
theorem exists_split_orderEmb {N : ℕ} (i' : ℕ) (B : Finset (Fin N)) :
    ∃ sB, sB ≤ B.card ∧ sB ≤ i' ∧ B.card - sB ≤ N - i' ∧
      (∀ m : Fin B.card, (m : ℕ) < sB → ((B.orderEmbOfFin rfl m : Fin N) : ℕ) < i') ∧
      (∀ m : Fin B.card, sB ≤ (m : ℕ) → i' ≤ ((B.orderEmbOfFin rfl m : Fin N) : ℕ)) := by
  classical
  set emb := B.orderEmbOfFin rfl with hemb
  have hex : ∃ s, s ≤ B.card ∧ ∀ m : Fin B.card, s ≤ (m : ℕ) → i' ≤ ((emb m : Fin N) : ℕ) :=
    ⟨B.card, le_rfl, fun m hm => absurd m.isLt (by omega)⟩
  set sB := Nat.find hex with hsB
  have hspec : sB ≤ B.card ∧ ∀ m : Fin B.card, sB ≤ (m : ℕ) → i' ≤ ((emb m : Fin N) : ℕ) :=
    Nat.find_spec hex
  have hsp : ∀ m : Fin B.card, (m : ℕ) < sB → ((emb m : Fin N) : ℕ) < i' := by
    intro m hm
    by_contra hcon
    replace hcon := not_lt.mp hcon
    refine Nat.find_min hex hm ⟨m.isLt.le, fun m' hm' => ?_⟩
    have : emb m ≤ emb m' := emb.monotone (Fin.le_iff_val_le_val.mpr hm')
    exact hcon.trans (Fin.le_iff_val_le_val.mp this)
  refine ⟨sB, hspec.1, ?_, ?_, hsp, hspec.2⟩
  · have hinj : Function.Injective (fun m : Fin sB =>
        (⟨(emb ⟨m, by have := hspec.1; omega⟩ : Fin N), hsp _ m.isLt⟩ : Fin i')) := by
      intro a b hab
      simp only [Fin.mk.injEq] at hab
      have := emb.injective (Fin.ext hab)
      exact Fin.ext (by simpa using congrArg Fin.val this)
    simpa using Fintype.card_le_of_injective _ hinj
  · have hlt : ∀ m : Fin (B.card - sB), sB + (m : ℕ) < B.card := fun m => by
      have := m.isLt; omega
    have hge : ∀ m : Fin (B.card - sB), i' ≤ ((emb ⟨sB + m, hlt m⟩ : Fin N) : ℕ) := fun m =>
      hspec.2 _ (show sB ≤ sB + (m : ℕ) from Nat.le_add_right _ _)
    have hinj : Function.Injective (fun m : Fin (B.card - sB) =>
        (⟨((emb ⟨sB + m, hlt m⟩ : Fin N) : ℕ) - i', by
          have := (emb ⟨sB + m, hlt m⟩).isLt; have := hge m; omega⟩ : Fin (N - i'))) := by
      intro a b hab
      simp only [Fin.mk.injEq] at hab
      have ha := hge a
      have hb := hge b
      have key : ((emb ⟨sB + a, hlt a⟩ : Fin N) : ℕ) = ((emb ⟨sB + b, hlt b⟩ : Fin N) : ℕ) := by
        omega
      have := emb.injective (Fin.ext key)
      exact Fin.ext (by simpa using congrArg Fin.val this)
    simpa using Fintype.card_le_of_injective _ hinj

theorem sum_range_ite_lt (a b : ℕ) (s : ℕ) :
    ∀ N, ∑ m ∈ Finset.range N, (if m < s then a else b) = min s N * a + (N - s) * b
  | 0 => by simp
  | N + 1 => by
    rw [Finset.sum_range_succ, sum_range_ite_lt a b s N]
    rcases Nat.lt_or_ge N s with h | h
    · rw [if_pos h, show min s (N + 1) = min s N + 1 by omega, show N + 1 - s = N - s by omega]
      ring
    · rw [if_neg (by omega), show min s (N + 1) = min s N by omega,
        show N + 1 - s = N - s + 1 by omega]
      ring

theorem sum_orderEmb {N : ℕ} (B : Finset (Fin N)) (f : Fin N → ℕ) :
    ∑ b ∈ B, f b = ∑ m : Fin B.card, f (B.orderEmbOfFin rfl m) := by
  classical
  conv_lhs => rw [← B.image_orderEmbOfFin_univ rfl]
  rw [Finset.sum_image fun a _ b _ h => (B.orderEmbOfFin rfl).injective h]

end ShortTime.IterDir
