import ShortTime.Linear.DiffOp

/-!
# Differentiating a linear operator (`lem:commute`)

For `L = ∑_k A_k ∇^k` of order `2p` on `T⁰_s`, there are an operator `L̃` of order `2p` on
`T⁰_{s+1}` and a zeroth-order field `S₀` with

  `∇(L u) = L̃(∇u) + S₀ u`        (`LinearOp.covGrad_comm`).

The principal coefficient of `L̃` is `P^{(1)} = P_• ∘ γ`: the slot permutation `γ` moves the slot
of `∇u` in front of the `2p` derivative slots, and `P_•` (`slotExtend`) applies `P` to the
remaining slots. Commuting `γ` past `∇^{2p+1}u` costs an operator of order `2p - 1`, by the Ricci
identity (`isDiffOp_cycle_defect`).
-/

noncomputable section

open Bundle Manifold Set MeasureTheory
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open scoped Manifold ContDiff BigOperators

set_option linter.unusedSectionVars false

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

variable {g : SmoothRiemannianMetric I M}

/-! ### Cyclic permutations as products of adjacent transpositions -/

theorem cycleRange_succ_eq {n j : ℕ} (hj : j + 1 < n) :
    Fin.cycleRange (⟨j + 1, hj⟩ : Fin n) =
      Fin.cycleRange (⟨j, by omega⟩ : Fin n) * Equiv.swap (⟨j, by omega⟩ : Fin n) ⟨j + 1, hj⟩ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  ext x
  rw [Equiv.Perm.mul_apply]
  rcases lt_trichotomy (x : ℕ) j with h | h | h
  · have hx1 : x ≠ ⟨j, by omega⟩ := fun e => by have := congrArg Fin.val e; simp at this; omega
    have hx2 : x ≠ ⟨j + 1, hj⟩ := fun e => by have := congrArg Fin.val e; simp at this; omega
    rw [Equiv.swap_apply_of_ne_of_ne hx1 hx2,
      Fin.coe_cycleRange_of_lt (Fin.lt_def.mpr (by simp; omega)),
      Fin.coe_cycleRange_of_lt (Fin.lt_def.mpr (by simp; omega))]
  · have hx : x = ⟨j, by omega⟩ := Fin.ext h
    rw [hx, Equiv.swap_apply_left, Fin.coe_cycleRange_of_lt (Fin.lt_def.mpr (by simp)),
      Fin.cycleRange_of_gt (Fin.lt_def.mpr (by simp))]
  · rcases (Nat.lt_or_ge (j + 1) x) with h' | h'
    · have hx1 : x ≠ ⟨j, by omega⟩ := fun e => by have := congrArg Fin.val e; simp at this; omega
      have hx2 : x ≠ ⟨j + 1, hj⟩ := fun e => by have := congrArg Fin.val e; simp at this; omega
      rw [Equiv.swap_apply_of_ne_of_ne hx1 hx2,
        Fin.cycleRange_of_gt (Fin.lt_def.mpr (by simp; omega)),
        Fin.cycleRange_of_gt (Fin.lt_def.mpr (by simp; omega))]
    · have hx : x = ⟨j + 1, hj⟩ := Fin.ext (by simp; omega)
      rw [hx, Equiv.swap_apply_right, Fin.cycleRange_self, Fin.cycleRange_self]

/-! ### Commuting derivative slots -/

theorem iteratedCovGrad_heq_congr {n n' : ℕ} (h : n = n') {Y : SmoothCcTensor g 0 n}
    {Y' : SmoothCcTensor g 0 n'} (hY : HEq Y Y') (i : ℕ) :
    HEq (iteratedCovGrad g 0 n i Y) (iteratedCovGrad g 0 n' i Y') := by
  subst h
  cases eq_of_heq hY
  rfl

theorem cast_sub_swap {n n' : ℕ} (h : n = n') (i : ℕ) (hi : i + 1 < n) (hi' : i + 1 < n')
    (Y : SmoothCcTensor g 0 n) (X : SmoothCcTensor g 0 n') (hXY : HEq Y X) :
    castCcTensorRank g 0 h (Y - domDomCongrSection (I := I) g
        (Equiv.swap (⟨i, by omega⟩ : Fin n) ⟨i + 1, hi⟩) Y) =
      X - domDomCongrSection (I := I) g (Equiv.swap (⟨i, by omega⟩ : Fin n') ⟨i + 1, hi'⟩) X := by
  subst h
  cases eq_of_heq hXY
  rfl

/-- **Ricci identity**: swapping the adjacent derivative slots `i, i + 1` of `∇^N u` changes it by
an operator of order `N - 2` in `u`. -/
theorem isDiffOp_swap_defect (S : Set ℝ) (s : ℕ) {N i : ℕ} (hi : i + 2 ≤ N) :
    IsDiffOp (g := g) S (N - 2) (fun (_ : ℝ) (u : SmoothCcTensor g 0 s) =>
      iteratedCovGrad g 0 s N u - domDomCongrSection (I := I) g
        (Equiv.swap (⟨i, by omega⟩ : Fin (s + N)) ⟨i + 1, by omega⟩) (iteratedCovGrad g 0 s N u)) := by
  obtain ⟨b, rfl⟩ : ∃ b, N = i + 2 + b := ⟨N - (i + 2), by omega⟩
  obtain ⟨R, hR⟩ := exists_swap_field (g := g) (s + b) i
  -- `∇^i(R ∇^b u)` is an operator of order `b + i`
  have hD := (IsDiffOp.field_grad (S := S) (a := s) b
    (jointlySmoothOn_const g S (homField g R))).iterGrad i
  have hD' := hD.cast_target (by omega : s + b + 2 + i = s + (i + 2 + b))
  refine (hD'.mono (by omega)).congr' fun t u => ?_
  have hY : HEq (iteratedCovGrad g 0 (s + b + 2) i (iteratedCovGrad g 0 (s + b) 2
      (iteratedCovGrad g 0 s b u))) (iteratedCovGrad g 0 s (i + 2 + b) u) :=
    ((iteratedCovGrad_heq_congr (by omega) (iteratedCovGrad_comp_heq 0 s b u 2) i).trans
      (iteratedCovGrad_comp_heq 0 s (b + 2) u i)).trans (iteratedCovGrad_heq_of_eq (by omega) u)
  rw [← cast_sub_swap (by omega : s + b + 2 + i = s + (i + 2 + b)) i (by omega) (by omega) _ _ hY,
    hR, sub_sub_cancel, operatorFieldApply_homField]

/-- Moving slot `j` of `∇^N u` to the front (`Fin.cycleRange j`) changes it by an operator of
order `N - 2` in `u`: telescope over adjacent transpositions. -/
theorem isDiffOp_cycle_defect (S : Set ℝ) (s N : ℕ) :
    ∀ (j : ℕ) (hj : j < N), IsDiffOp (g := g) S (N - 2) (fun (_ : ℝ) (u : SmoothCcTensor g 0 s) =>
      iteratedCovGrad g 0 s N u - domDomCongrSection (I := I) g
        (Fin.cycleRange (⟨j, by omega⟩ : Fin (s + N))) (iteratedCovGrad g 0 s N u))
  | 0, hj => by
    refine (IsDiffOp.zero (N - 2)).congr' fun t u => ?_
    have h1 : Fin.cycleRange (⟨0, by omega⟩ : Fin (s + N)) = 1 := by
      have : NeZero (s + N) := ⟨by omega⟩
      rw [show (⟨0, by omega⟩ : Fin (s + N)) = 0 from Fin.ext (by simp)]
      exact Fin.cycleRange_zero _
    rw [h1, domDomCongrSection_one, sub_self]
  | j + 1, hj => by
    have ih := isDiffOp_cycle_defect S s N j (by omega)
    have hsw := (isDiffOp_swap_defect (g := g) S s (i := j) (N := N) (by omega)).perm
      (Fin.cycleRange (⟨j, by omega⟩ : Fin (s + N)))
    refine (ih.add hsw).congr' fun t u => ?_
    rw [cycleRange_succ_eq (by omega), domDomCongrSection_mul, domDomCongrSection_sub]
    abel

/-- **Commuting covariant derivatives** (`lem:ricci`): for a permutation `σ` of the derivative slots
of `∇^N u`, `σ(∇^N u) = ∇^N u + Q_σ u` with `Q_σ` an operator of order `N - 2`. Adjacent
transpositions are the Ricci identity (`isDiffOp_swap_defect`), and they generate. -/
theorem permute_iteratedCovGrad (S : Set ℝ) (s N : ℕ) (σ : Equiv.Perm (Fin N)) :
    IsDiffOp (g := g) S (N - 2) (fun (_ : ℝ) (u : SmoothCcTensor g 0 s) =>
      domDomCongrSection (I := I) g (extPerm s N σ) (iteratedCovGrad g 0 s N u) -
        iteratedCovGrad g 0 s N u) := by
  let Pr : Equiv.Perm (Fin (s + N)) → Prop := fun τ =>
    IsDiffOp (g := g) S (N - 2) (fun (_ : ℝ) (u : SmoothCcTensor g 0 s) =>
      domDomCongrSection (I := I) g τ (iteratedCovGrad g 0 s N u) - iteratedCovGrad g 0 s N u)
  have hone : Pr 1 := (IsDiffOp.zero (N - 2)).congr' fun t u => by
    rw [domDomCongrSection_one, sub_self]
  have hmul : ∀ τ₁ τ₂, Pr τ₁ → Pr τ₂ → Pr (τ₁ * τ₂) := fun τ₁ τ₂ h₁ h₂ =>
    ((h₂.perm τ₁).add h₁).congr' fun t u => by
      rw [domDomCongrSection_mul, domDomCongrSection_sub]
      abel
  rcases N with _ | n
  · rw [show σ = 1 from Subsingleton.elim _ _, map_one]
    exact hone
  · have hmem : σ ∈ Submonoid.closure (Set.range fun i : Fin n => Equiv.swap i.castSucc i.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]
      exact Submonoid.mem_top σ
    induction hmem using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [extPerm_swap]
      exact (isDiffOp_swap_defect (g := g) S s (N := n + 1) (i := i) (by omega)).neg.congr'
        fun t u => by rw [neg_sub]
    | one => rw [map_one]; exact hone
    | mul x y _ _ hx hy => rw [map_mul]; exact hmul _ _ hx hy

/-! ### The differentiated operator -/

/-- The slot relabelling `γ` of `P^{(1)} = P_• ∘ γ`: on `∇^{2p}(∇u)`, it moves the slot of `∇u`
(position `2p`) to the front. -/
def gammaEquiv (s p : ℕ) : Fin (s + 1 + 2 * p) ≃ Fin (s + 2 * p + 1) :=
  (finCongr (by omega)).trans (Fin.cycleRange (⟨2 * p, by omega⟩ : Fin (s + 2 * p + 1)))

theorem operatorFieldApply_permField_cast {n n' : ℕ} (h : n = n') (σ : Equiv.Perm (Fin n'))
    (Y : SmoothCcTensor g 0 n) (X : SmoothCcTensor g 0 n') (hXY : HEq Y X) :
    operatorFieldApply (I := I) (M := M) g n n' (permField g ((finCongr h).trans σ)) Y =
      domDomCongrSection (I := I) g σ X := by
  subst h
  cases eq_of_heq hXY
  rw [← operatorFieldApply_permField]
  rfl

namespace LinearOp

variable {s p : ℕ} {T : ℝ}

/-- The principal coefficient `P^{(1)} = P_• ∘ γ` of the differentiated operator. -/
def commTop (L : LinearOp g s p T) (t : ℝ) : SmoothCcTensor g (s + 1 + 2 * p) (s + 1) :=
  ccOperatorFieldComp (I := I) (M := M) g (s + 1 + 2 * p) (s + 2 * p + 1) (s + 1)
    (slotExtend (I := I) (M := M) g (s + 2 * p) s (L.coeff (Fin.last (2 * p)) t))
    (permField g (gammaEquiv s p))

theorem jointlySmoothOn_commTop (L : LinearOp g s p T) :
    JointlySmoothOn g (s + 1 + 2 * p) (s + 1) (Icc 0 T) L.commTop :=
  jointlySmoothOn_comp g (jointlySmoothOn_slotExtend (L.smooth (Fin.last (2 * p))))
    (jointlySmoothOn_const g _ _)

/-- **Differentiating an operator** (`lem:commute`): `∇(L u) = L̃(∇u) + S₀ u`, where the principal
coefficient of `L̃` is `P^{(1)}` (`commTop`). -/
theorem exists_covGrad_comm (L : LinearOp g s p T) :
    ∃ (L' : LinearOp g (s + 1) p T) (S₀ : ℝ → SmoothCcTensor g s (s + 1)),
      JointlySmoothOn g s (s + 1) (Icc 0 T) S₀ ∧
      (∀ t, L'.coeff (Fin.last (2 * p)) t = L.commTop t) ∧
      ∀ t u, covGrad (I := I) (M := M) g 0 s (L.apply t u) =
        L'.apply t (covGrad (I := I) (M := M) g 0 s u) +
          operatorFieldApply (I := I) (M := M) g s (s + 1) (S₀ t) u := by
  classical
  set S : Set ℝ := Icc 0 T
  set σ : Equiv.Perm (Fin (s + (2 * p + 1))) := Fin.cycleRange (⟨2 * p, by omega⟩ : Fin (s + (2 * p + 1)))
  -- the lower-order part `R`
  have hlow : IsDiffOp S (2 * p) (fun t u => ∑ k : Fin (2 * p), covGrad (I := I) (M := M) g 0 s
      (operatorFieldApply (I := I) (M := M) g (s + k) s (L.coeff k.castSucc t)
        (iteratedCovGrad g 0 s k u))) :=
    IsDiffOp.sum _ fun k _ =>
      ((IsDiffOp.field_grad (S := S) (a := s) (k : ℕ) (L.smooth k.castSucc)).grad).mono (by omega)
  have hP : IsDiffOp S (2 * p) (fun t u => operatorFieldApply (I := I) (M := M) g (s + 2 * p) (s + 1)
      (covGrad (I := I) (M := M) g (s + 2 * p) s (L.coeff (Fin.last (2 * p)) t))
      (iteratedCovGrad g 0 s (2 * p) u)) :=
    IsDiffOp.field_grad (S := S) (a := s) (2 * p) (jointlySmoothOn_covGrad (L.smooth (Fin.last _)))
  have hcyc : IsDiffOp S (2 * p) (fun t u => operatorFieldApply (I := I) (M := M) g (s + 2 * p + 1)
      (s + 1) (slotExtend (I := I) (M := M) g (s + 2 * p) s (L.coeff (Fin.last (2 * p)) t))
      (iteratedCovGrad g 0 s (2 * p + 1) u -
        domDomCongrSection (I := I) g σ (iteratedCovGrad g 0 s (2 * p + 1) u))) :=
    ((isDiffOp_cycle_defect (g := g) S s (2 * p + 1) (2 * p) (by omega)).comp_field
      (jointlySmoothOn_slotExtend (L.smooth (Fin.last (2 * p))))).mono (by omega)
  obtain ⟨S₀, hS₀, F', hF', hsplit⟩ := ((hlow.add hP).add hcyc).split
  refine ⟨⟨Fin.lastCases (motive := fun k => ℝ → SmoothCcTensor g (s + 1 + k) (s + 1))
    L.commTop (fun i => F' i), fun k => ?_⟩, S₀, hS₀, fun t => ?_, fun t u => ?_⟩
  · induction k using Fin.lastCases with
    | last => rw [Fin.lastCases_last]; exact L.jointlySmoothOn_commTop
    | cast i => rw [Fin.lastCases_castSucc]; exact hF' i
  · simp only [Fin.lastCases_last]
  · -- the two operators, with the top terms split off
    have hL : L.apply t u = ∑ k : Fin (2 * p), operatorFieldApply (I := I) (M := M) g (s + k) s
        (L.coeff k.castSucc t) (iteratedCovGrad g 0 s k u) +
        operatorFieldApply (I := I) (M := M) g (s + 2 * p) s (L.coeff (Fin.last (2 * p)) t)
          (iteratedCovGrad g 0 s (2 * p) u) := by
      unfold LinearOp.apply
      rw [Fin.sum_univ_castSucc]
      rfl
    rw [hL, covGrad_add, covGrad_finset_sum, covGrad_operatorFieldApply_eq, ← iteratedCovGrad_succ]
    unfold LinearOp.apply
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.lastCases_last, Fin.lastCases_castSucc, Fin.val_castSucc, Fin.val_last]
    -- the top term: `P_•(∇^{2p+1}u) = P^{(1)}(∇^{2p}(∇u)) + P_•(∇^{2p+1}u - γ∇^{2p+1}u)`
    have htop : operatorFieldApply (I := I) (M := M) g (s + 1 + 2 * p) (s + 1) (L.commTop t)
        (iteratedCovGrad g 0 (s + 1) (2 * p) (covGrad (I := I) (M := M) g 0 s u)) =
        operatorFieldApply (I := I) (M := M) g (s + 2 * p + 1) (s + 1)
          (slotExtend (I := I) (M := M) g (s + 2 * p) s (L.coeff (Fin.last (2 * p)) t))
          (domDomCongrSection (I := I) g σ (iteratedCovGrad g 0 s (2 * p + 1) u)) := by
      rw [commTop, ← operatorFieldApply_assoc]
      congr 1
      exact operatorFieldApply_permField_cast _ _ _ _ (iteratedCovGrad_covGrad_comm_heq g 0 s (2 * p) u)
    have hX := hsplit t u
    rw [operatorFieldApplication_sub_right, ← htop, Finset.sum_range] at hX
    generalize operatorFieldApply (I := I) (M := M) g (s + 1 + 2 * p) (s + 1) (L.commTop t)
      (iteratedCovGrad g 0 (s + 1) (2 * p) (covGrad (I := I) (M := M) g 0 s u)) = C at hX ⊢
    rw [show ∀ A B X F S0 : SmoothCcTensor g 0 (s + 1), A + B + (X - C) = S0 + F →
        A + (B + X) = F + C + S0 from fun A B X F S0 h => by
          rw [show A + (B + X) = A + B + (X - C) + C by abel, h]; abel] 
    exact hX

end LinearOp

end ShortTime
