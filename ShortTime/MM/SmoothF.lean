import ShortTime.MM.SmoothCoords

/-!
# Smoothness of the MM right side

`MMData.smooth_F`: `F = (-1)^{p+1} Σ_{K,K'} (∏ E_ℓ(e^{K_ℓ}, e^{K'_ℓ})) · z(e_{K₀}, e_{K'₀}, …) + b`
is smooth in the local coordinates at `x₀`, because by `frameSum_eq_frameSum` it may be computed in the
coordinate frame.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Analysis.Sobolev
open scoped Manifold ContDiff BigOperators

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

theorem tangent_mem_of_trivAt (x₀ y : M) (r s : ℕ) (h : y ∈ (trivAt I M r s x₀).baseSet) :
    y ∈ (trivializationAt E (TangentSpace I) x₀).baseSet :=
  h.1

theorem trivAt_mem_of_tangent (x₀ y : M) (r s : ℕ)
    (h : y ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    y ∈ (trivAt I M r s x₀).baseSet :=
  ⟨h, h⟩

/-- `z ↦ (β ↦ z β u)`, from `(0,n)`-model tensors to scalars (as `(0,0)`-model tensors). -/
def evalModelCLM (n : ℕ) (u : Fin n → E) : TensorRSModel 0 n ℝ E →L[ℝ] TensorRSModel 0 0 ℝ E :=
  ContinuousLinearMap.compL ℝ (Tensor0SModel 0 ℝ E) (Tensor0SModel n ℝ E)
      (Tensor0SModel 0 ℝ E)
    ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
        (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ))).comp
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E) ℝ u))

theorem evalModelCLM_apply (n : ℕ) (u : Fin n → E) (z : TensorRSModel 0 n ℝ E)
    (β : Tensor0SModel 0 ℝ E) (v : Fin 0 → E) :
    evalModelCLM n u z β v = z β u := by
  simp [evalModelCLM]

/-- The model vector `(e_{K₀}, e_{K'₀}, e_{K₁}, …)` in the standard basis of `E`. -/
def coordTop (p : ℕ) (K K' : Fin p → Fin (Module.finrank ℝ E)) : Fin (0 + 2 * p) → E :=
  appendIdx (s := 0) (interleave (fun i => Module.finBasis ℝ E (K i))
    (fun i => Module.finBasis ℝ E (K' i))) (fun i => i.elim0)

theorem interleave_map {A B : Type*} {p : ℕ} (f : A → B) (K K' : Fin p → A) :
    interleave (fun i => f (K i)) (fun i => f (K' i)) = fun m => f (interleave K K' m) := by
  funext m
  unfold interleave
  split_ifs <;> rfl

variable {p : ℕ} (d : MMData I M p)

/-- The right side, in the local coordinates at `x₀`. -/
theorem localRep_F_eq (x₀ : M) (q : ℝ × M × JetModel E 0 0 (2 * p))
    (hq : q ∈ localDom (I := I) 0 0 (2 * p) d.T₀ d.dom x₀) :
    localRep 0 0 (2 * p) d.F x₀ q =
      (-1 : ℝ) ^ (p + 1) • ∑ K : Fin p → Fin (Module.finrank ℝ E),
        ∑ K' : Fin p → Fin (Module.finrank ℝ E),
          (∏ l, d.Ef l q.1 q.2.1 (jetOfModel 0 0 (2 * p) x₀ q.2.1 q.2.2)
              (coordCoframe (I := I) x₀ q.2.1 (K l)) (coordCoframe (I := I) x₀ q.2.1 (K' l))) •
            evalModelCLM (0 + 2 * p) (coordTop p K K') (q.2.2 (Fin.last (2 * p))) +
        localRep 0 0 (2 * p) d.b x₀ q := by
  obtain ⟨t, y, z⟩ := q
  have hy : y ∈ jetBase (I := I) 0 0 (2 * p) x₀ := hq.1.2
  have hyT : y ∈ (trivializationAt E (TangentSpace I) x₀).baseSet :=
    tangent_mem_of_trivAt x₀ y 0 0 hy.1
  have hy0 : y ∈ (trivAt I M 0 0 x₀).baseSet := hy.1
  have hyq : y ∈ (trivAt I M 0 (0 + 2 * p) x₀).baseSet := mem_iInter.1 hy.2 (Fin.last (2 * p))
  have hF := frameSum_eq_frameSum p y
    (fun l => d.Ef l t y (jetOfModel 0 0 (2 * p) x₀ y z)) (stdFrame (I := I) y)
    (coordFrame (I := I) x₀ y)
    (stdCoframe (I := I) y) (coordCoframe (I := I) x₀ y) (stdCoframe_stdFrame (I := I) y)
    (coordCoframe_coordFrame (I := I) x₀ y hyT) (jetOfModel 0 0 (2 * p) x₀ y z (Fin.last (2 * p)))
  unfold localRep
  dsimp only
  rw [MMData.F, hF, map_add]
  unfold frameSum
  rw [map_smul, map_sum]
  congr 1
  congr 1
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun K' _ => ?_
  rw [map_smul]
  congr 1
  ext β v
  rw [evalModelCLM_apply]
  have h := evalFirst_inCoords (I := I) x₀ y (2 * p) hyT hy0 hyq
    (interleave (fun i => Module.finBasis ℝ E (K i)) (fun i => Module.finBasis ℝ E (K' i)))
    (z (Fin.last (2 * p))) β v
  have hi := interleave_map ((trivializationAt E (TangentSpace I) x₀).symmL ℝ y)
    (fun i => Module.finBasis ℝ E (K i)) (fun i => Module.finBasis ℝ E (K' i))
  have hv : v = fun i => i.elim0 := funext fun i => i.elim0
  subst hv
  have e : evalFirst (r := 0) (s := 0) (2 * p)
      (interleave (fun i => coordFrame (I := I) x₀ y (K i)) fun i => coordFrame (I := I) x₀ y (K' i))
      (jetOfModel 0 0 (2 * p) x₀ y z (Fin.last (2 * p))) =
    evalFirst (r := 0) (s := 0) (2 * p)
      (fun i => (trivializationAt E (TangentSpace I) x₀).symmL ℝ y
        (interleave (fun i => Module.finBasis ℝ E (K i)) (fun i => Module.finBasis ℝ E (K' i)) i))
      ((trivAt I M 0 (0 + 2 * p) x₀).symmL ℝ y (z (Fin.last (2 * p)))) := by
    show evalFirst (r := 0) (s := 0) (2 * p) (interleave
      (fun i => (trivializationAt E (TangentSpace I) x₀).symmL ℝ y (Module.finBasis ℝ E (K i)))
      (fun i => (trivializationAt E (TangentSpace I) x₀).symmL ℝ y (Module.finBasis ℝ E (K' i)))) _ = _
    rw [hi]
    rfl
  rw [e]
  exact h

/-- **Smoothness of the MM right side** in the local coordinates at `x₀`. -/
theorem smooth_F (x₀ : M) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, JetModel E 0 0 (2 * p)))) 𝓘(ℝ, TensorRSModel 0 0 ℝ E) ∞
      (localRep 0 0 (2 * p) d.F x₀) (localDom (I := I) 0 0 (2 * p) d.T₀ d.dom x₀) := by
  let projTop : JetModel E 0 0 (2 * p) →L[ℝ] TensorRSModel 0 (0 + 2 * p) ℝ E :=
    ContinuousLinearMap.proj (R := ℝ)
      (φ := fun k : Fin (2 * p + 1) => TensorRSModel 0 (0 + k) ℝ E) (Fin.last (2 * p))
  have hproj : ContMDiff (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, JetModel E 0 0 (2 * p))))
      𝓘(ℝ, TensorRSModel 0 (0 + 2 * p) ℝ E) ∞
      (fun q : ℝ × M × JetModel E 0 0 (2 * p) => projTop q.2.2) :=
    projTop.contMDiff.comp (contMDiff_snd.comp contMDiff_snd)
  refine ContMDiffOn.congr ?_ (fun q hq => localRep_F_eq d x₀ q hq)
  refine ContMDiffOn.add ?_ (d.b_smooth x₀)
  have hsum : ContMDiffOn (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, JetModel E 0 0 (2 * p))))
      𝓘(ℝ, TensorRSModel 0 0 ℝ E) ∞
      (fun q : ℝ × M × JetModel E 0 0 (2 * p) => ∑ K : Fin p → Fin (Module.finrank ℝ E),
        ∑ K' : Fin p → Fin (Module.finrank ℝ E),
          (∏ l, d.Ef l q.1 q.2.1 (jetOfModel 0 0 (2 * p) x₀ q.2.1 q.2.2)
              (coordCoframe (I := I) x₀ q.2.1 (K l)) (coordCoframe (I := I) x₀ q.2.1 (K' l))) •
            evalModelCLM (0 + 2 * p) (coordTop p K K') (projTop q.2.2))
      (localDom (I := I) 0 0 (2 * p) d.T₀ d.dom x₀) := by
    refine contMDiffOn_finsetSum fun K _ => contMDiffOn_finsetSum fun K' _ => ?_
    have h1 := ContMDiffOn.smul (contMDiffOn_finsetProd fun l (_ : l ∈ Finset.univ) =>
      d.Ef_smooth x₀ l (K l) (K' l))
      (((evalModelCLM (0 + 2 * p) (coordTop p K K')).contMDiff.comp hproj).contMDiffOn
        (s := localDom (I := I) 0 0 (2 * p) d.T₀ d.dom x₀))
    exact h1
  have hc : ContMDiffOn (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, JetModel E 0 0 (2 * p)))) 𝓘(ℝ, ℝ) ∞
      (fun _ : ℝ × M × JetModel E 0 0 (2 * p) => (-1 : ℝ) ^ (p + 1))
      (localDom (I := I) 0 0 (2 * p) d.T₀ d.dom x₀) := contMDiffOn_const
  have h2 := ContMDiffOn.smul hc hsum
  exact h2

end ShortTime
