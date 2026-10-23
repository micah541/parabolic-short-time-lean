import ShortTime.MM.RearrangedDef

/-!
# Smoothness of the rearranged right side

`MMData.smooth_Frearr`: `F'` is smooth in the local coordinates at `x₀`. The split contraction is
computed in the coordinate frame (`splitFrameSum_eq_splitFrameSum`), and the Ricci correction `Q` is a
smooth jet map (`ricciQ_smooth`).
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Spectral DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Elliptic DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff BigOperators

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

theorem evalFirst_inCoords_of (x₀ y : M) (q : ℕ)
    (hy : y ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (hx0 : y ∈ (trivAt I M 0 0 x₀).baseSet) (hxq : y ∈ (trivAt I M 0 (0 + q) x₀).baseSet)
    (w : Fin q → E) (A : TensorRSSpace 0 (0 + q) I y) (β : Tensor0SModel 0 ℝ E) (v : Fin 0 → E) :
    ((trivAt I M 0 0 x₀).continuousLinearMapAt ℝ y
      (evalFirst (r := 0) (s := 0) q
        (fun i => (trivializationAt E (TangentSpace I) x₀).symmL ℝ y (w i)) A)) β v =
      ((trivAt I M 0 (0 + q) x₀).continuousLinearMapAt ℝ y A) β (appendIdx w v) := by
  have h := evalFirst_inCoords (I := I) x₀ y q hy hx0 hxq w
    ((trivAt I M 0 (0 + q) x₀).continuousLinearMapAt ℝ y A) β v
  rwa [Trivialization.symmL_continuousLinearMapAt _ hxq] at h

theorem splitVec_map {A B : Type*} {p : ℕ} (f : A → B) (K K' : Fin p → A) :
    splitVec (fun i => f (K i)) (fun i => f (K' i)) = fun m => f (splitVec K K' m) := by
  funext m
  unfold splitVec
  split_ifs <;> rfl

/-- The model vector `(e_{K₀}, …, e_{K_{p-1}}, e_{K'₀}, …)` in the standard basis of `E`. -/
def coordTopSplit (p : ℕ) (K K' : Fin p → Fin (Module.finrank ℝ E)) : Fin (0 + 2 * p) → E :=
  appendIdx (s := 0) (splitVec (fun i => Module.finBasis ℝ E (K i))
    (fun i => Module.finBasis ℝ E (K' i))) (fun i => i.elim0)

/-- The top component of a model `2p`-jet. -/
def ztop (p : ℕ) (z : JetModel E 0 0 (2 * p)) : TensorRSModel 0 (0 + 2 * p) ℝ E :=
  z (Fin.last (2 * p))

/-- Forget the top component of a model `2p`-jet. -/
def truncModel (p : ℕ) : JetModel E 0 0 (2 * p) →L[ℝ] JetModel E 0 0 (2 * p - 1) :=
  ContinuousLinearMap.pi fun k : Fin (2 * p - 1 + 1) =>
    ContinuousLinearMap.proj (R := ℝ)
      (φ := fun k : Fin (2 * p + 1) => TensorRSModel 0 (0 + k) ℝ E)
      (⟨k.val, by have := k.isLt; omega⟩ : Fin (2 * p + 1))

variable (g : SmoothRiemannianMetric I M) {p : ℕ} (d : MMData I M p)

/-- The Ricci correction in the trivialisation at `x₀`. -/
def Qloc (x₀ : M) (q : ℝ × M × JetModel E 0 0 (2 * p)) : TensorRSModel 0 (0 + 2 * p) ℝ E :=
  (trivAt I M 0 (0 + 2 * p) x₀).continuousLinearMapAt ℝ q.2.1
    (ricciQ g p q.2.1 (truncJet q.2.1 (jetOfModel 0 0 (2 * p) x₀ q.2.1 q.2.2)))

/-- The rearranged right side, in the local coordinates at `x₀`. -/
theorem localRep_Frearr_eq (x₀ : M) (q : ℝ × M × JetModel E 0 0 (2 * p))
    (hq : q ∈ localDom (I := I) 0 0 (2 * p) d.T₀ d.dom x₀) :
    localRep 0 0 (2 * p) (d.Frearr g) x₀ q =
      (-1 : ℝ) ^ (p + 1) • ∑ K : Fin p → Fin (Module.finrank ℝ E),
        ∑ K' : Fin p → Fin (Module.finrank ℝ E),
          (∏ l, d.Ef l q.1 q.2.1 (jetOfModel 0 0 (2 * p) x₀ q.2.1 q.2.2)
              (coordCoframe (I := I) x₀ q.2.1 (K l)) (coordCoframe (I := I) x₀ q.2.1 (K' l))) •
            evalModelCLM (0 + 2 * p) (coordTopSplit p K K')
              (ztop p q.2.2 + Qloc g x₀ q) +
        localRep 0 0 (2 * p) d.b x₀ q := by
  obtain ⟨t, y, z⟩ := q
  have hy : y ∈ jetBase (I := I) 0 0 (2 * p) x₀ := hq.1.2
  have hyT : y ∈ (trivializationAt E (TangentSpace I) x₀).baseSet :=
    tangent_mem_of_trivAt x₀ y 0 0 hy.1
  have hy0 : y ∈ (trivAt I M 0 0 x₀).baseSet := hy.1
  have hyq : y ∈ (trivAt I M 0 (0 + 2 * p) x₀).baseSet := mem_iInter.1 hy.2 (Fin.last (2 * p))
  have hF := splitFrameSum_eq_splitFrameSum p y
    (fun l => d.Ef l t y (jetOfModel 0 0 (2 * p) x₀ y z)) (tangentFrame g y)
    (coordFrame (I := I) x₀ y) (coframe g y) (coordCoframe (I := I) x₀ y)
    (fun i j => coframe_apply g y i j) (coordCoframe_coordFrame (I := I) x₀ y hyT)
    (jtop p (jetOfModel 0 0 (2 * p) x₀ y z) +
      ricciQ g p y (truncJet y (jetOfModel 0 0 (2 * p) x₀ y z)))
  unfold localRep
  dsimp only
  rw [MMData.Frearr, map_add, productCLM_castIdx_eq_splitFrameSum, hF]
  congr 1
  unfold splitFrameSum
  rw [map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun K' _ => ?_
  rw [map_smul]
  congr 1
  ext β v
  have hv : v = fun i => i.elim0 := funext fun i => i.elim0
  subst hv
  rw [evalModelCLM_apply]
  have hadd : ∀ A B : TensorRSSpace 0 (0 + 2 * p) I y, ∀ w : Fin (2 * p) → TangentSpace I y,
      evalFirst (r := 0) (s := 0) (2 * p) w (A + B) =
        evalFirst (r := 0) (s := 0) (2 * p) w A + evalFirst (r := 0) (s := 0) (2 * p) w B :=
    fun A B w => by simp only [← evalFirstCLM_apply, map_add]
  have hw : (splitVec (fun i => coordFrame (I := I) x₀ y (K i)) fun i => coordFrame (I := I) x₀ y (K' i)) =
      fun i => (trivializationAt E (TangentSpace I) x₀).symmL ℝ y
        (splitVec (fun i => Module.finBasis ℝ E (K i)) (fun i => Module.finBasis ℝ E (K' i)) i) := by
    show splitVec (fun i => (trivializationAt E (TangentSpace I) x₀).symmL ℝ y (Module.finBasis ℝ E (K i)))
      (fun i => (trivializationAt E (TangentSpace I) x₀).symmL ℝ y (Module.finBasis ℝ E (K' i))) = _
    exact splitVec_map ((trivializationAt E (TangentSpace I) x₀).symmL ℝ y) _ _
  rw [hw, hadd, map_add, add_apply, add_apply,
    add_apply, add_apply,
    evalFirst_inCoords_of x₀ y (2 * p) hyT hy0 hyq _ (jtop p (jetOfModel 0 0 (2 * p) x₀ y z)),
    evalFirst_inCoords_of x₀ y (2 * p) hyT hy0 hyq _
      (ricciQ g p y (truncJet y (jetOfModel 0 0 (2 * p) x₀ y z)))]
  congr 1
  · have : (trivAt I M 0 (0 + 2 * p) x₀).continuousLinearMapAt ℝ y
        (jtop p (jetOfModel 0 0 (2 * p) x₀ y z)) = ztop p z :=
      Trivialization.continuousLinearMapAt_symmL _ hyq _
    rw [this]
    rfl

theorem smooth_Qloc (x₀ : M) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, JetModel E 0 0 (2 * p))))
      𝓘(ℝ, TensorRSModel 0 (0 + 2 * p) ℝ E) ∞ (Qloc g x₀)
      (localDom (I := I) 0 0 (2 * p) d.T₀ d.dom x₀) := by
  have hz : ContMDiff (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, JetModel E 0 0 (2 * p))))
      𝓘(ℝ, JetModel E 0 0 (2 * p)) ∞ (fun q : ℝ × M × JetModel E 0 0 (2 * p) => q.2.2) :=
    contMDiff_snd.comp contMDiff_snd
  have hπ : ContMDiff (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, JetModel E 0 0 (2 * p))))
      (I.prod 𝓘(ℝ, JetModel E 0 0 (2 * p - 1))) ∞
      (fun q : ℝ × M × JetModel E 0 0 (2 * p) => (q.2.1, truncModel p q.2.2)) :=
    (contMDiff_fst.comp contMDiff_snd).prodMk
      ((truncModel p).contMDiff.comp hz)
  refine ((ricciQ_smooth g p x₀).comp hπ.contMDiffOn ?_).congr (fun q _ => rfl)
  rintro ⟨t, y, z⟩ hq
  have hy : y ∈ jetBase (I := I) 0 0 (2 * p) x₀ := hq.1.2
  refine ⟨⟨hy.1, ?_⟩, mem_iInter.1 hy.2 (Fin.last (2 * p))⟩
  refine mem_iInter.2 fun k => ?_
  exact mem_iInter.1 hy.2 ⟨k.val, by have := k.isLt; omega⟩

/-- **Smoothness of the rearranged right side** in the local coordinates at `x₀`. -/
theorem smooth_Frearr (x₀ : M) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, JetModel E 0 0 (2 * p)))) 𝓘(ℝ, TensorRSModel 0 0 ℝ E) ∞
      (localRep 0 0 (2 * p) (d.Frearr g) x₀) (localDom (I := I) 0 0 (2 * p) d.T₀ d.dom x₀) := by
  let projTop : JetModel E 0 0 (2 * p) →L[ℝ] TensorRSModel 0 (0 + 2 * p) ℝ E :=
    ContinuousLinearMap.proj (R := ℝ)
      (φ := fun k : Fin (2 * p + 1) => TensorRSModel 0 (0 + k) ℝ E) (Fin.last (2 * p))
  have hproj : ContMDiff (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, JetModel E 0 0 (2 * p))))
      𝓘(ℝ, TensorRSModel 0 (0 + 2 * p) ℝ E) ∞
      (fun q : ℝ × M × JetModel E 0 0 (2 * p) => projTop q.2.2) :=
    projTop.contMDiff.comp (contMDiff_snd.comp contMDiff_snd)
  refine ContMDiffOn.congr ?_ (fun q hq => localRep_Frearr_eq g d x₀ q hq)
  refine ContMDiffOn.add ?_ (d.b_smooth x₀)
  have hsum : ContMDiffOn (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, JetModel E 0 0 (2 * p))))
      𝓘(ℝ, TensorRSModel 0 0 ℝ E) ∞
      (fun q : ℝ × M × JetModel E 0 0 (2 * p) => ∑ K : Fin p → Fin (Module.finrank ℝ E),
        ∑ K' : Fin p → Fin (Module.finrank ℝ E),
          (∏ l, d.Ef l q.1 q.2.1 (jetOfModel 0 0 (2 * p) x₀ q.2.1 q.2.2)
              (coordCoframe (I := I) x₀ q.2.1 (K l)) (coordCoframe (I := I) x₀ q.2.1 (K' l))) •
            evalModelCLM (0 + 2 * p) (coordTopSplit p K K') (ztop p q.2.2 + Qloc g x₀ q))
      (localDom (I := I) 0 0 (2 * p) d.T₀ d.dom x₀) := by
    refine contMDiffOn_finsetSum fun K _ => contMDiffOn_finsetSum fun K' _ => ?_
    have h1 := ContMDiffOn.smul (contMDiffOn_finsetProd fun l (_ : l ∈ Finset.univ) =>
      d.Ef_smooth x₀ l (K l) (K' l))
      (((evalModelCLM (0 + 2 * p) (coordTopSplit p K K')).contMDiff.comp_contMDiffOn
        ((hproj.contMDiffOn (s := localDom (I := I) 0 0 (2 * p) d.T₀ d.dom x₀)).add
          (smooth_Qloc g d x₀))))
    exact h1
  have hc : ContMDiffOn (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, JetModel E 0 0 (2 * p)))) 𝓘(ℝ, ℝ) ∞
      (fun _ : ℝ × M × JetModel E 0 0 (2 * p) => (-1 : ℝ) ^ (p + 1))
      (localDom (I := I) 0 0 (2 * p) d.T₀ d.dom x₀) := contMDiffOn_const
  have h2 := ContMDiffOn.smul hc hsum
  exact h2

end ShortTime
