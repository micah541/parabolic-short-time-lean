# Design decisions

A log of judgment calls in the formal statements. Every change to a pinned declaration must be
recorded here.

## 2026-09-29: initial statements pinned

The main theorems (`ShortTime/MainTheorems.lean`) and all definitions they use
(`ShortTime/Setting/*.lean`) were pinned with these choices.

1. **Bundles.**
   - The bundle `V` of the paper is a tensor bundle `T^r_s M` (the library's `TensorRSSpace r s`),
     for arbitrary `r, s`.
   - This covers scalar equations (`r = s = 0`) and flows of metrics (`r = 0, s = 2`).
   - The family is closed under `W ↦ T*M ⊗ W`, which is the only operation the linear theory needs.
   - General vector bundles with a connection are deferred.
2. **The nonlinearity.**
   - `F` is given fibre by fibre on a fibrewise domain `dom t x ⊆ J^{2p}_x`.
   - "Open domain" and "smooth `F`" are required in the library's local trivializations of the
     tensor bundles, at every base point, jointly in `(t, x, jet)`.
   - Relative openness is taken in `[0, T₀] × J^{2p}`.
3. **Legendre condition.**
   - It uses the frame formula `B_P(ξ, ξ) = Σ_I ⟨ξ_I, P(e^I ⊗ ξ)⟩` in a `g`-orthonormal frame, with
     sign `(-1)^{p+1}`.
   - It uses the library's slot convention: `∇` adds the first slot. This matches the paper.
   - Parabolicity at a jet means that the Legendre condition holds with *some* constant `λ > 0`.
4. **Solutions.**
   - A solution is jointly smooth on `M × [0,T]`, in the same sense as the library's Ricci-flow
     statements (`ContMDiffOn` on `M × ℝ`).
   - The equation is `HasDerivWithinAt` in `t` on `[0,T]` at every point, endpoints included.
5. **Theorem C.**
   - It is stated sequentially: if all covariant derivatives of the data converge uniformly, then
     all covariant derivatives of the solutions converge uniformly on `M × [0,T]`.
   - Time derivatives then converge by the equation. This keeps parabolic Sobolev spaces out of the
     trusted statements.

## 2026-09-29: `IsSolution.eqn` re-pinned (meaning unchanged)

**What was wrong.** The time derivative in `IsSolution.eqn` was stated directly on the tensor fibre
`TensorRSSpace r s I x`. The library gives that fibre two topologies that are equal mathematically
but not definitionally equal:

- the strong topology on continuous linear maps, `tensorRSSpaceTopologicalSpace`;
- the topology induced by its norm, `tensorRSSpaceNormedAddCommGroup`.

`HasDerivWithinAt` picked the first, while all of Mathlib's derivative lemmas require the second.
T0 exposed this: even `hasDerivWithinAt_const` did not apply. Every future proof about solutions
would have needed an instance bridge.

**Fix.** The derivative is now taken in the normed model fibre `TensorRSModel r s ℝ E`, through the
canonical linear identification `TensorRSSpace.toModel`. For a curve in a fixed finite-dimensional
fibre, the derivative does not depend on which linear identification is used, so the meaning of the
definition is unchanged. No theorem statement changed.

## T0 status

Done (all `sorry`-free, standard axioms only):

- `ShortTime/Sanity/LegendreTrace.lean`: the trace of the first two slots, the principal part of the
  heat equation, satisfies `LegendreAt` with constant `1` on `(0,s)`-tensors.
- `ShortTime/Sanity/ZeroEquation.lean`: `∂ₜu = 0` is a valid `EquationData`, and constant fields
  solve it.
- `ShortTime/Setting/LinearData.lean`: every linear equation `∂ₜu = P(∇^{2p}u)` with `P` a smooth
  section of the hom bundle is a valid `EquationData`, with principal coefficient `P`.
- `ShortTime/Sanity/HeatEquation.lean`: the heat equation is parabolic at every jet, and `u ≡ 0` is
  an `IsParabolicSolution`, given `TraceSmooth g`.
- `ShortTime/Sanity/TraceSmooth.lean`: `traceSmooth g : TraceSmooth g`. Hence
  `heatData_zero_isParabolicSolution'` holds unconditionally.

**T0 is complete.** Every pinned definition entering Theorems A–C has a genuine instance, so the
main theorems cannot be vacuously true.

## 2026-09-29: linear theory on covariant tensor bundles

1. **Bundles.** The linear theory (`ShortTime/Linear/`) works on `V = T⁰_s M`.
   - The energy method only needs `W ↦ T*M ⊗ W`, and `T⁰_s` is closed under it.
   - The library's calculus of operator fields lives on these bundles: Leibniz rule
     (`covGrad_operatorFieldApply_eq`), integration by parts, parametric joint smoothness
     (`covGrad_iter_joint`, `joint_jet_bdd`).
   - General `T^r_s` will reduce to this case by lowering indices with `g` (parallel and
     isometric), at the interface with the nonlinear theorems.
2. **Operators.** `LinearOp g s p T` has coefficients `A_k(t)`, operator fields `T⁰_{s+k} → T⁰_s`
   (`SmoothCcTensor g (s+k) s`), jointly smooth on `M × [0,T]` (`JointlySmoothOn`).
   - `L.apply t u = Σ_k A_k(t) (∇^k u)`.
   - `L.IsParabolic lam` is the pinned `LegendreAt` for the principal coefficient, viewed as a map
     of the nonlinear setting's fibres through `opFieldHom`.
3. **Moving derivatives across coefficients** uses the *flip* `Ǎ(w)(v,·) = A(v♭ ⊗ w)`, not a
   pointwise adjoint.
   - `tr₁₂ ∘ slotExtend Ǎ = A`, so one integration by parts is
     `⟨T, A∇W⟩ = -⟨∇T, ǍW⟩ - ⟨T, R_A W⟩` (`inner_apply_covGrad`).
   - For `p = 1` the Legendre form is `⟨ξ, Ǎξ⟩` (`legendreForm_one_eq`). Gårding's inequality is
     proved from the flip-coercivity `LinearOp.FlipCoercive`, which follows from `IsParabolic`.
   - The paper's `lem:ibp` was rewritten to follow this route (new `def:flip`, `lem:ibp-one`).
4. **Library modules re-proved or vendored locally,** to keep the first build small.
   - `div V = tr₁₂ ∇V` (`ShortTime/Linear/Divergence.lean`) repeats a short DG proof whose
     module transitively imports about 650 otherwise unneeded modules.
   - `Family.lean` proves the parametric uncurrying lemma that DG only has without parameters.
   - `ShortTime/Vendor/ParametricJets.lean` copies three DG files verbatim, plus two lemmas of a
     fourth: joint smoothness of `∇` for time-dependent families, and uniform jet bounds. Only the
     imports were trimmed. The library versions import two modules they do not use, which cost
     about 400 extra modules (over an hour of compilation and roughly 3 GB of RAM per worker).

## 2026-10-01: Gårding's inequality and uniqueness for every order

1. **Norms.** The estimates use `N_k(u) = Σ_{i ≤ k} ‖∇^i u‖` (`jetSum`), which satisfies
   `‖u‖_{H^k} ≤ N_k(u) ≤ √(k+1) ‖u‖_{H^k}`. The paper's `lem:ibp`, `lem:garding` and `lem:interp`
   now state their error terms with `N_k`. Interpolation is stated for norms rather than squared
   norms (`jetNorm_le_interp`); the squared forms are its consequences.
2. **The reversal.** After `p` flips, `P^{(p)}(ξ)(v₁, …, v_p, ·) = P(v_p♭ ⊗ ⋯ ⊗ v₁♭ ⊗ ξ)`
   (`evalFirst_flipIter`): the covectors come out in reverse order. Hence the Legendre form is
   `B_P(ξ, η) = ⟨ρξ, P^{(p)} η⟩`, with `ρ` the reversal of the first `p` slots
   (`legendreForm_eq_fiberInner_flipIter`). For `ξ = ∇^p u`, `ρ` is the slot permutation
   `extPerm s p Fin.revPerm`, and `‖ρ∇^p u − ∇^p u‖ ≤ C N_{p−2}(u)` (`exists_perm_bound`).
3. **Permuting derivatives.** The paper's `lem:ricci` (σ∇^r u = ∇^r u + Q_σ u with
   `Q_σ ∈ Diff^{r−2}`) is not formalized as stated. What the linear theory needs is its `L²`
   consequence, now a separate item `lem:ricci-l2`, proved directly:
   - one adjacent transposition, from DG's Ricci identity, transported through `∇^k` by the
     naturality of `∇` under slot permutations (`exists_swap_defect`,
     `toModel_iteratedCovGrad_domDomCongr`);
   - all permutations, by closure under products (`exists_perm_bound`).
4. **Uniqueness from an energy bound.** `LinearOp.unique_of_energy` needs only
   `⟨u, L(t) u⟩ ≤ C ‖u‖²`. Gårding's inequality gives this for every parabolic `L`
   (`LinearOp.energy_bound`), so `LinearOp.unique_of_isParabolic` now holds for every order. The
   earlier `p = 1` route (`garding_one`, `FlipCoercive`) is kept as a worked special case; the
   paper no longer cites it.

## 2026-10-02: Theorem B skeleton and honest status

1. **Reduction to covariant bundles, at the level of the equation.** Each main theorem on `T^r_s`
   follows from its case on covariant bundles `T⁰_{s'}` (`lem:lowering`;
   `solution_unique_of_covariant` for Theorem B). Lowering indices transforms the equation data, the
   solutions and the Legendre condition. The nonlinear proofs therefore only meet `r = 0`, where
   the linear theory lives.
2. **Theorem B is proved from two lemmas still marked `sorry`.** These are `lem:lowering` and local
   uniqueness (`lem:local-unique`, `EquationData.local_unique`). The step from local to global uniqueness is
   proved (`EquationData.solution_unique_cov`, via `IsClosed.Icc_subset_of_forall_mem_nhdsWithin`).
   The paper's proof of Theorem B was split the same way.
3. **`blueprint.py` status `conditional`.** An item used to show `proved` as soon as its own
   declarations had no `sorry`, even if they used declarations with `sorry`. The map now propagates
   `sorry` through references between project declarations. References are found textually by the
   last component of the name, so the check errs toward reporting a dependence. Items whose
   proofs are written but rest on a `sorry` are `conditional`.

## 2026-10-02: Fibre topologies, model coordinates, and the linearized difference equation

1. **Two topologies on a tensor fibre.** DG gives `TensorRSSpace r s I x` the bundle topology
   (`tensorRSSpaceTopologicalSpace`, the operator topology of `T⁰_r →L T⁰_s`) and, separately, a
   norm transported from the model space (`tensorRSSpaceNormedAddCommGroup`). The two topologies are
   equal (`tensorRSSpace_topology_eq`) but not definitionally. Consequences:
   - Mathlib's `fderiv` is defined for topological vector spaces. The pinned
     `EquationData.partialDeriv` is therefore a derivative for the *bundle* topology.
   - Maps between fibres (`TensorRSSpace a →L TensorRSSpace b`) have no usable norm, so they cannot
     be integrated directly.
2. **Model coordinates.** All analysis on `F` is done in the model spaces.
   - `fibIso` and `jetIso` are linear isometries from the (normed) fibres to the model spaces.
   - `Fmod` is `F` read in these coordinates.
   - `partialDeriv_eq_fderivN` and `fibIso_partialDeriv` connect the pinned partial derivatives
     with the derivative of `Fmod` (via `fderiv_congr_top`).
   - Averages of fibre maps are computed in the model (`avgFib`).
3. **The linearized difference equation** (`lem:difference`, `ShortTime/Nonlinear/Linearize.lean`).
   Proved, with no `sorry`. Smoothness of the equation data and of the averaged coefficients is
   read in the trivializations at a point `x₀` (`contDiffAt_Fmod`, `trivAt_partialDeriv`,
   `coordP_avg`). There the coefficients are integrals `∫₀¹ f(q, σ) dσ` of a smooth integrand, smooth
   up to the boundary of the convex time interval (`ShortTime/Analysis/ParamIntegral.lean` and
   `ParamIntegralManifold.lean`). Operator fields are built from fibre maps by `opFieldOf`
   (`ShortTime/Nonlinear/OpField.lean`).

## 2026-10-02: The tube lemma through local frames

1. **Theorem B on covariant bundles is proved.** `EquationData.solution_unique_cov` depends only on
   `propext`, `Classical.choice` and `Quot.sound`. Theorem B for general bundles still rests on
   `solution_unique_of_covariant` (lowering indices).
2. **The segment between two nearby jets stays parabolic** (`exists_parabolic_segment`,
   `ShortTime/Nonlinear/Tube.lean`). The paper's earlier proof went through the general tube lemma
   `lem:legendre-basic` (iii). The Lean proof, and now the paper (`lem:local-unique`), argue directly:
   - in coordinates at each `x₀`, the gap `(-1)^{p+1} B_P(ξ, ξ) - (λ₀/2)|ξ|²` along the segment is
     continuous, and positive at `t = t*` on `[0, 1]` times the unit sphere;
   - compactness, homogeneity in `ξ`, and a finite cover of `M` give the uniform constant.
   `lem:legendre-basic` (ii), (iii) are still needed for Theorem A and remain planned.
3. **Continuity of the Legendre form in the base point** (`lem:legendre-coord`). The Legendre form is
   defined with a pointwise orthonormal frame, which is not continuous in the point. It is trilinear,
   so in coordinates it is a polynomial whose coefficients are Legendre forms of smooth sections with
   constant coordinates near `x₀`. By `legendreForm_eq_fiberInner_flipIter` these coefficients are
   pointwise inner products of smooth sections, hence continuous.


## 2026-10-14: Lowering indices; Theorem B proved

1. **Theorem B is proved for all tensor bundles.** `solution_unique_of_covariant`
   (`lem:lowering`, `ShortTime/Nonlinear/Lowering.lean`) has no `sorry`, so `solution_unique`
   depends only on `propext`, `Classical.choice` and `Quot.sound`. No pinned declaration changed.
2. **Lowering is built from the library's metric-compatibility layer, not from `lowerCc`.**
   `DifferentialGeometry`'s `LoweringJetTower` (`lowerCc`) is unbuilt, assumes
   `[InnerProductSpace ℝ E]`, and only treats jets of order `≤ 2`. Instead:
   - the fibre map `flat` comes from `lowerAllUpperIndicesEquiv`, and is an isometry because the
     library defines `tensorInnerPointwise` through lowering (`Flat.lean`);
   - `∇^k(♭u) = σ_k ♭(∇^k u)` follows from `loweringIntertwinerRS_holds` by induction
     (`FlatGrad.lean`). `σ_k = jetPerm r s k : Fin (r + (s + k)) ≃ Fin ((r + s) + k)` moves the `k`
     derivative slots in front of the `r` lowered ones. Slot relabellings are taken along any
     `Fin a ≃ Fin b`, which absorbs the non-definitional `r + (s + k) = (r + s) + k`.
3. **The lowered equation** `D^♭` (`EquationData.flatData`, `FlatData.lean`) has domain `♭_J(𝒟)` and
   `F^♭ = ♭ ∘ F ∘ ♭_J⁻¹`. Its openness and smoothness are read in the trivializations at `x₀`:
   `♭` is a smooth bundle map (`contMDiffOn_clm_section_of_apply`), its coordinate matrix and the
   inverse (`contDiffAt_map_inverse`) are smooth in the base point, and slot permutations have
   constant coordinates (`trivAt_slotPerm`, `FlatCoord.lean`).
4. **The Legendre condition** transfers with the same constant (`legendreAt_flatData`,
   `FlatLegendre.lean`). The two compatibilities of the paper's proof (first-slot evaluation and
   prepending covectors commute with `σ_p ♭`) are checked on explicit model-coordinate formulas
   (`FlatAlgebra.lean`).

## 2026-10-14: Statement audit; Theorem C split

1. **Independent audit of the 26 pinned declarations** against the paper: no serious discrepancy.
   Slot conventions, the Legendre sign and frame, `fiberInner`, the time derivative, and the
   openness/smoothness requirements of `EquationData` all match. The library's `LeviCivita g` is
   proved to be the Levi-Civita connection (`leviCivitaConnectionOfMetric_isLeviCivita`).
2. **Theorem C is split** so that the blueprint cannot overclaim. `thm:C` is the paper's smooth
   dependence theorem (a `C^∞` solution map on an `H^{2pm}`-ball); its Lean name
   `solution_smooth_dependence` is reserved, not stated. The pinned
   `solution_continuous_dependence` now formalizes the new `cor:C` (sequential form), whose proof is
   the former Step 3 of the proof of `thm:C`. The Lean statement is unchanged.
3. **Paper remark on bundles corrected**: the formal statements cover `T^r_s M` with the Levi-Civita
   connection, not `⊗^r T^*M ⊗ ℝ^K`.
4. **Non-vacuity in every order**: `legendreAt_polyTrace` (`Sanity/PolyTrace.lean`) shows that the
   polyharmonic principal coefficient `P₀(X) = (-1)^{p+1} Σ_I X(e_I, e_I, ·)` satisfies `LegendreAt`
   with constant `1` on `T⁰_s`, for every `p`. Previously only `p = 1` was machine-checked. The
   paper's identity `-(Δ)^p u = P₀(∇^{2p}u) + Q₀u` (`legendre_polyharmonic`) is still planned.

## 2026-10-17: Differentiating an operator; higher energy estimates

1. **`lem:commute` follows the paper's exact identity** `∇(Lu) = L̃(∇u) + S₀u`
   (`LinearOp.exists_covGrad_comm`, `Commute.lean`). The plan of 2026-10-15 to replace it by commutator
   estimates was dropped: a small calculus of operators with jointly smooth coefficients
   (`IsDiffOp`, `DiffOp.lean`) makes the exact identity cheap. It is closed under sums, coefficient
   fields, slot permutations, `∇` (Leibniz) and precomposition with `∇`, and splits as
   `D W = S₀ W + D'(∇W)` (`IsDiffOp.split`).
2. **The principal coefficient of `L̃` is `P^{(1)} = P_• ∘ γ`** (`commTop`). `slotExtend P` alone is
   not parabolic. `γ` moves the slot of `∇u` (position `2p` of `∇^{2p}(∇u)`) to the front; commuting it
   past `∇^{2p+1}u` costs an operator of order `2p - 1` (`isDiffOp_cycle_defect`, by telescoping the
   library's exact Ricci identity over adjacent transpositions). The Legendre condition for
   `P^{(1)}` holds with the constant of `P` (`isParabolic_comm`, `LegendreComm.lean`): the Legendre
   form splits as a sum over a frame of the extra slot.
3. **Operator fields for slot permutations and Hom-fields** (`PermField.lean`): `permField e`
   (`D ↦ D(· ∘ e)` for `e : Fin a ≃ Fin b`, constant coordinates) and `homField Q` (the library's
   Ricci identity is stated with Hom-fields). Rank casts are relabellings along `finCongr`.
4. **Energy estimates along segments** (`energy_estimate`, `EnergyHigher.lean`). The constant is
   uniform for `L_θ = (1-θ)L₀ + θL₁`, `θ ∈ [0,1]`, rather than over the class `𝓛(λ, K, Λ)`; this is
   what the continuity method (`thm:linear`) needs. The base case now depends only on the Gårding
   constants (`energy_estimate_zero_of_garding`), and Gårding's inequality is uniform along a segment
   (`garding_lerp`). A remark in the paper records this.
5. **`∂ₜ∇u = ∇∂ₜu`** for jointly smooth families (`hasDerivWithinAt_covGrad`) is proved weakly: the
   pairings with test fields agree after one integration by parts, and a smooth field with zero
   `L²` norm vanishes.

## 2026-10-19: The model operator and `thm:linear` (i)

1. **`∂ₜ - L` on parabolic spaces** (`LinearTheorem.lean`). `heatExt` is the continuous extension of
   `heatOp` from smooth families (`ContinuousLinearMap.extend` along the completion map), using
   `parabolicInner_heatOp_le`. The a priori estimate passes to `𝒫^m_0` by closure
   (`norm_le_heatExt_lerp`), uniformly along segments, and `isomorphism_of_base` is the method of
   continuity. `LinearOp.isomorphism` moved from `Parabolic.lean` to `ModelSolve.lean`; its
   statement is unchanged (it is not pinned).
2. **`prop:model` is used in dense-range form** (`LinearOp.exists_model`): `∂ₜ - L₀` has dense range on
   smooth families vanishing at `t = 0`. Surjectivity on `𝒫^m_0` then follows from closed range
   (`surjective_heatExt_of_approx`). The paper's proof was rewritten accordingly: the Cauchy-sequence
   argument for `u_N` is replaced by density of the range plus closed range.
3. **The model operator is `L₀ = (-1)^{p+1} Δ_raw^p`**, with `Δ_raw = tr₁₂ ∇²` the library's rough
   Laplacian (`rawTensorConnLapSmooth`, negative semidefinite), so `L₀ = -(Δ)^p` with `Δ ≥ 0`.
   `Δ_raw^k u = Φ_k(∇^{2k}u) + (order ≤ 2k-1)` with `Φ_k` the composite of the metric double traces
   (`isDiffOp_lapIter_sub`). `Φ_k` pairs the derivative slots `(1,2), (3,4), …`, which does **not**
   satisfy the Legendre condition (for `p = 2` it fails on trace-free `ξ`); the slots are reordered by
   the riffle permutation and `lem:ricci` (`isDiffOp_lapIter_sub_modelTop`), after which the
   principal coefficient evaluates like `polyTrace` (`modelTop_prepend`, `legendreAt_modelTop`).
   This proves `lem:legendre-examples` (b).
4. **Eigenfunction expansions** (`ModelSpectral.lean`): the library's smooth eigenfunctions, the
   coefficient identity `rawLap_coeff` (all ranks), and the spectral/jet norm comparisons
   `hsJet_le`, `hs_le_jet` (all ranks). Truncations converge in `L²(0,T; H^n)` by dominated
   convergence over the filter of finite sets of modes (countable index set). Each mode is solved by
   the library's Duhamel integral, clamped to `[0,T]` (`modeSol`, `IccCalculus.lean`).
5. The library module `Analysis/Elliptic/ConnectionLaplacian/Commutation/OperatorFieldApplication`
   (one module, not in the user-built closure) was compiled directly with `lake env lean -o`.

## 2026-10-19: `thm:linear` (ii), smooth solutions

1. **Limits of good sequences** (`GoodSeq.lean`, `InsField.lean`, `LimitSmooth.lean`,
   `LimitFamily.lean`). A sequence of jointly smooth families is *good* if every jet
   `∇^i ∂ₜ^j wₘ` is uniformly Cauchy in the fibre norm. In the chart and trivialization at a point,
   with vector fields `B_k` of constant coordinates (`exists_chart_patch`), the coordinate derivative
   of the reading of `wₘ` along `e_k` is the reading of `(insField B_k)(∇wₘ)` plus a Christoffel term
   (`fderiv_chartRd`). Good sequences are closed under `∂ₜ` and `w ↦ Φ(∇w)`, so the readings converge
   in `C^n` for every `n` (`contDiffOn_limChart`, using `Analysis/UniformLimit.lean`). The limit is
   jointly smooth (`rawJoint_limSec`, packaged as `limFam`), and `∂ₜ`, `∇` commute with the limit
   (`timeDeriv_limFam`, `covGrad_limFam`: compare at the chart centre, then separate by the frame
   `B_k`), hence so do all `∇^i ∂ₜ^j` (`jet_limFam`).
2. **Smooth solutions** (`SmoothSolve.lean`). `LinearOp.exists_approx` gives smooth zero-start `uₙ`
   with `‖(∂ₜ - L)uₙ - f‖²_{𝒫^n} < 1/(n+1)` (from `isomorphism` at level `n+1` and density). The a
   priori estimate makes `(uₙ)` Cauchy in every `𝒫^q`, the embedding makes it good
   (`good_of_parabolic`), and the equation passes to the pointwise limit. The initial datum is
   handled by subtracting the constant family `u₀`. `LinearOp.exists_smooth` moved from
   `Parabolic.lean` to `SmoothSolve.lean`; its statement is unchanged (it is not pinned).
3. The paper's proof of (ii) is rewritten to this approximation argument, and `lem:embedding` now
   states the sequence version (Cauchy in every `𝒫^m` ⇒ smooth limit with limit derivatives).

## 2026-10-20: plan for Theorem A (existence)

1. **Reduction to covariant bundles**, as for Theorem B: `exists_solution_of_covariant`
   (`Raising.lean`) lowers the equation, solves on `T⁰_{r+s}`, and raises indices back.
2. **Composition estimates** (`prop:nemytskii`, `cor:N`) are split so that the geometry and the
   analysis are separate:
   - *Euclidean core* (`Analysis/FaaDiBruno.lean`): a tame weighted Faà di Bruno bound. For
     `Φ ∘ (id, u)` and directions `v` with weights (time `2p`, space `1`), `|D^n(Φ∘U)[v]|` is at most
     `C(1 + Σ_B |D^{|B|}u[v_B]|)`, provided all sub-derivatives of weight at most half the total are
     bounded. In each Faà di Bruno term at most one block has more than half the weight.
   - *Jet comparison in charts*: in the chart and trivialization at a point, `∂ₜ^j∇^iu` and the
     coordinate derivatives `∂ₜ^j∂_x^{i'}ũ`, `i' ≤ i`, bound each other on compact subsets, with
     smooth coefficients (induction on `fderiv_chartRd`).
   - *Pointwise tame lemma* on `M`: if the jets of `u` of weight at most `W/2` are bounded by `R`,
     then `|∂ₜ^j∇^iΦ(u)| ≤ C(1 + Σ_{weight ≤ 2pj+i}|∂ₜ^{j'}∇^{i'}u|)` pointwise.
   - *Integral lemma*: with the embedding (`exists_fiberNormSq_le_parabolicInner`) for the low
     jets, `‖Φ(u)‖_{𝒫^N} ≤ C(R)(1 + ‖u‖_{𝒫^N})`.
   - *Multilinear maps* `G(ζ; η₁,…,η_k)` reduce to the nonlinear case by scaling the `η_l`, giving
     `‖G(u; h)‖ ≤ C(R)(1 + ‖u‖) Π‖h_l‖`. The remainders `Φ(u+h) - Φ(u) - DΦ(u)h` and
     `Φ(u) - Φ(u')` are multilinear maps of this kind (Taylor's formula at fibre level), which gives
     the Lipschitz and differentiability estimates. Differentiability of every order follows by
     induction over all multilinear `G` at once (`contDiff_succ_iff_fderiv`).
   - The operators are defined on smooth families and extended to the completions by continuity
     (the domain is open by the embedding).
3. **Implicit function theorem**: Mathlib's `ImplicitFunctionData` and
   `contDiffAt_implicitFunction` (`Analysis/Calculus/ImplicitContDiff.lean`), and the inverse
   function theorem through `HasStrictFDerivAt`.
4. **Regularity (`prop:regularity`) without weak derivatives.** Angenent's trick gives that
   `s ↦ Π_s v` is `C^∞` from a neighbourhood of `0 ∈ ℝ^n` into `𝒫^m`, where `Π_s` is the
   composite of the horizontal pullbacks along the flows of vector fields `B_1, …, B_n` that form a
   frame near a point `x₀` (`exists_chart_patch`). Instead of `fact:weak` (weak derivatives and
   mollifiers), use the embedding:
   - For `m ≥ N₀`, evaluation of the low jets at `(x, t)` extends to a bounded functional on `𝒫^m`,
     continuous in `(x, t)`: the continuous representative.
   - `ev_{x₀,t}(Π_s v) = P_s(x₀)^{-1} v̂(φ_s(x₀), t)`. The left side is `C^∞` in `s`, and
     `s ↦ φ_s(x₀)` is a local diffeomorphism at `0` (its derivative is the frame). Hence `v̂(·, t)` is
     smooth near `x₀`, with spatial derivatives continuous in `(y, t)`.
   - Time derivatives then come from the equation `∂ₜu = F[u]`, which holds pointwise on `[0, ε]`.
   The library supplies the flows (`contMDiff_curveAt`) and smooth parallel transport along a
   smooth family of curves (`CovariantDerivative.exists_parallel_transport_on_interval`), behind
   about 64 library modules that are not yet compiled.
5. **Extension to the completions** (`Analysis/SmoothExtension.lean`,
   `exists_contDiffOn_extension`): Taylor bounds (M), (T) for the would-be derivatives on a dense
   normed subspace give a `C^∞` extension. The source must be *normed*, so apply it with `X₀` the
   image of the smooth families in `𝒫^m` (a normed subspace of the completion), not `ParabolicPre`
   itself, which is only seminormed: families may differ outside `[0,T]`.
6. **Regularity pipeline** (after `prop:existence` in `Existence.lean`, `lem:flows` (a),(d) for one
   vector field in `Flows*.lean`):
   - Frame `B_1, …, B_n` with constant chart coordinates near `x₀`. Their flows are translations in
     the chart, so `Π_s = Π^{B_1}_{s_1} ∘ ⋯ ∘ Π^{B_n}_{s_n}` and `s ↦ φ_s(x₀)` is a chart
     translation near `0`.
   - Naturality must be iterated, so it must hold for fibre maps with parameters: `natFibreMap` for
     a general `FibreMap` with parameter `Λ`, giving parameter `Λ × ℝ`.
   - The parametric composition operator: `FibreMap.exists_nonlinOp_param`, `C^∞` at `(0, w)`
     jointly in `(λ, u)`.
   - The pullback on `𝒫^m`: uniform bounds, `C^∞` in `σ` for smooth data, continuity in `σ` for all
     `v`, and commutation with `∂ₜ`.
   - Angenent: `H(s, v) = ∂ₜ(Π_s w + v) - 𝒩_s(Π_s w + v)`; the implicit function theorem
     (`contDiffAt_implicitFunction`) gives `Π_s v = Ψ(s, Π_s f_ε)`, which is `C^∞` in `s`.
   - Spatial smoothness from `evalJet`, then time derivatives from the equation (item 4).
   - The paper's (d) is rewritten: there is no global inverse `Θ_s^{-1}` on jets, because covariant
     jets satisfy curvature constraints. It uses `Υ_s(x)`, which carries the jet of `v` at `x` to the
     jet of `Π_{-s} v` at `φ_s x`.
7. **Open issue (2026-10-22): `C^∞` on a ball, not only at a point.** Angenent's argument
   (`Angenent.exists_contDiffAt_of_natural`) needs the parametric composition operator to be `C^k`
   on a *fixed* neighbourhood of `(0, w)` for every `k`. `exists_nonlinOp(_param)` give only
   `ContDiffAt ∞` at the point, because the tube radius in `exists_derivFam_bound` /
   `exists_taylor_bound` depends on the derivative order (through `blkRanks … k` and the domain of the
   k-th fibre derivative). Mathematically the radius can be chosen uniformly: one compact tube
   around the jets of `w` inside the domain bounds all fibre derivatives. Fix: refactor the
   Nemytskii chain so that the tube radius is chosen once, from the base domain, giving
   `ContDiffOn ℝ ∞ 𝒩' (ball (0, W) r)`.

## 2026-10-22: Theorem A fully proved; regularity assembled

1. **Item 7 resolved (uniform ball).** `FibreMap.exists_nonlinOp_param_ball` (`UniformTube*.lean`)
   gives `ContDiffOn ∞` on a fixed ball. The tube radius was k-dependent only through arbitrary
   choices inside `patch_tame`; `patch_tame_gen` takes them as inputs, so one radius serves all
   fibre derivatives and Taylor remainders.
2. **`V` depends on the frame.** `exists_iterPull_contDiffOn` (`RegularityAngenent.lean`) gives `V_B`
   for a fixed frame `B`. `exists_spatialSmooth` now chooses its radius before `v`, and
   `rawJoint_of_chart_cover` lets a finite cover of `M` by chart balls suffice, so
   `V := ⋂ V_{α_i}` (`regularity_of_time`, `RegularityFinal.lean`).
3. **Time bootstrap** (`SmoothRepTime*.lean`, `smoothRep_time`): the representative's chart readings
   `jetChart j i` are limits of smooth ones; `∂ₜ v̂ = G` with `G` a smooth Euclidean function of the
   jets (`htime_core`), via `SpC.comp_rel` (relatively open domains) and the pointwise tube lemma
   `exists_euclTube`. The old `htime` interface was unprovable (it quantified over all `ε` and had no
   equation hypothesis); it is replaced by the per-frame `εt ≤ r` form.
4. `parabolicSpace_solution_smooth` is proved (axioms clean). The only `sorry` left in the project is
   `solution_continuous_dependence` (cor:C). Its proof needs the parametric version of regularity
   (paper, proof of thm:C, Step 2): `V` must be uniform in the datum `a`.

## 2026-10-22: Corollary C proved; all three trusted theorems sorry-free

1. **No parametric Angenent.** The paper's proof of thm:C (IFT in `H^{2pm} × 𝒫^m_0`, then regularity
   with the datum as parameter) is replaced by: fix the base solution `u`, perturb by the
   time-independent family `ζ = a − u₀`, and solve for `v ∈ 𝒫^m_0` by an IFT with parameter `ζ ∈ 𝒫^m`
   (`Analysis/IFTParam.lean`, `ContIFT.lean`). Smoothness of `U = u + ζ + v` comes from regularity
   in *trace form* at the fixed smooth base `u` (`regularity_of_time_trace`,
   `RegularityTrace*.lean`): Angenent's argument for `U ↦ (∂ₜU − 𝒩U, [U])` into
   `𝒫^{m-1} × 𝒫^m/𝒫^m_0` (an isomorphism at `u`), so the neighbourhood is uniform in the datum.
2. **Convergence in every level** by consistency: the level-`m'` solutions agree with the level-`m₀`
   solution by Theorem B; closeness in `𝒫^{m'}` controls `∇^j(w_n − u)` (`exists_jetSq_close`).
3. **General bundles** via `ContinuousDependenceLower.lean` (♭/♯ as for Theorems A, B).
4. `exists_solution`, `solution_unique`, `solution_continuous_dependence` all depend only on
   `propext`, `Classical.choice`, `Quot.sound`. `blueprint.py check`: 0 declarations with sorry.
   Theorem C proper (`solution_smooth_dependence`, smooth map `𝒮`) remains `planned`; it is not
   among the trusted statements.

## 2026-10-23: Corollaries cor:maximal and cor:MM proved

- `cor:maximal` (`ShortTime/Maximal.lean`): solutions on different intervals glue by Theorem B and
  restriction (`isParabolicSolution_of_le`). Stated as: a section `u` that is a parabolic solution on
  every `[0,T]` carrying one, unique on their union.
- `cor:MM` (`ShortTime/MM/*`, `mantegazza_martinazzi`): formal MM data `MMData` (scalar, `E_ℓ`
  symmetric positive definite *pointwise*; locally uniform positivity follows by continuity, so this
  is slightly more general than the paper). The MM equation `toEquationData` has the interleaved
  pairing; `rearranged` has the split pairing plus a Ricci correction (`exists_ricci_jetMap`), the
  same solutions (`rearranged_isSolution_iff`) and is parabolic on the whole domain
  (`rearranged_isParabolicAt`, via `legendre_product`). Theorems A, B and the sequential cor:C then
  transfer to the MM equation as written. No pinned declaration was changed.
- Theorem C proper (smooth map `𝒮` on `H^{2pm}`) is not pinned and remains unformalized.
