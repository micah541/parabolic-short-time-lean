# Working on this repository

This project formalizes, in Lean 4, the short-time existence / uniqueness / smooth-dependence
theorem for nonlinear parabolic equations of even order on tensor bundles over closed manifolds.

## Sources of truth

- **`paper/main.tex`** is the mathematical blueprint. Every numbered item has `\lean{...}` (the Lean
  declarations formalizing it) and `\uses{...}` (its dependencies). Proofs follow the paper.
- **`blueprint/map.md`** is generated from the paper and `ShortTime/`. Regenerate it; never edit it
  by hand.
- **`blueprint/pinned.json`** freezes the *trusted* statements: the main theorems and every
  definition they depend on. Intermediate lemma statements (e.g. `ShortTime/Linear/Basic.lean`) are
  not pinned and may be refined while proving; keep them faithful to the paper.

## Hard rules

1. **Never change a pinned declaration.** `python scripts/blueprint.py check` fails if you do.
   - The only exception: a pinned definition is shown to be *wrong*, for example a non-vacuity test
     fails because of it.
   - In that case, fix the definition and re-pin it with `python scripts/blueprint.py pin <Decl>`.
   - Record what was wrong and why the fix is right in `blueprint/DECISIONS.md`, and call it out
     explicitly in your summary to the user.
   - Never weaken a theorem statement to make it provable.
2. **No new axioms.** No `axiom`, no `native_decide`, no `implemented_by` tricks, no
   `set_option maxHeartbeats 0`. `#print axioms` of anything you call proved must list only
   `propext`, `Classical.choice`, `Quot.sound`.
3. **Keep the paper and Lean in sync.**
   - When you add a Lean declaration for a blueprint item, use the name given in `\lean{}`, or
     update the paper's `\lean{}` if a different name is clearly better.
   - If a proof in the paper is wrong or incomplete, fix the paper too, with its `\uses{}`.
   - Run `python scripts/blueprint.py map` afterwards.
4. **Before finishing any unit of work:** the touched files compile, and
   `python scripts/blueprint.py check` passes.

## Building on this machine (16 GB RAM, Windows)

- Always cap parallelism: `LEAN_NUM_THREADS=4`. With more, Lean runs out of memory and fails with
  spurious "failed to read file …olean" errors.
- Run **at most one Lean build or check at a time.** The user also works on this machine.
- **Checking a chain of project files in the REPL:** `bash scripts/chaincheck.sh <env> a.lean b.lean …`
  checks each file in the environment produced by the previous one, stopping at the first error.
  - The starting environment must import exactly the union of those files' imports.
  - A larger environment hides missing `import`s and `open`s, which then fail in `lake build`.
  - `open` commands of earlier files in the chain also stay active in later ones.
  - The REPL keeps every environment in memory. After two or three large imports, restart it, or
    imports silently come back empty.
- **Reliable per-file check: `bash scripts/compile1.sh A.lean B.lean …`.**
  - It compiles each file with `lake env lean -o …olean`, exactly as `lake build` does (about 40
    seconds per file), and stops at the first error.
  - It needs the `.olean`s of the project files each one imports.
  - Use the REPL for fast iteration and `compile1.sh` to confirm before declaring a file done.
- **Fastest: the persistent REPL.** `scripts/leanrepl.py` keeps the imports loaded, so each check
  takes about a second instead of about 3 minutes:
  - `python scripts/leanrepl.py serve` (run in the background);
  - `python scripts/leanrepl.py import <Module> ...` prints an env id;
  - `python scripts/leanrepl.py check <file> --env <id>`, or `cmd '<lean>' --env <id>`;
  - `python scripts/leanrepl.py stop`.

  The REPL binary lives in `../tools/repl` (leanprover-community/repl, tag v4.33.0, rebuilt with
  Lean v4.33.1). Stop the REPL before any `lake build` that compiles many library modules; the two
  together can exhaust memory.
- **Single-file check without the REPL:** `LEAN_NUM_THREADS=4 lake env lean ShortTime/Foo.lean`.
  Loading the imports takes about 3 minutes.
- **Checking a file that imports other project files:** first compile each imported project file
  to its `.olean` with `-o .lake/build/lib/lean/<path>.olean -i .lake/build/lib/lean/<path>.ilean`.
- **Full check:** `LEAN_NUM_THREADS=4 lake build`. Lake spends about 8 minutes checking traces
  before compiling.
- Library API: the dependency `DifferentialGeometry` (v0.1.3) is checked out under
  `.lake/packages/DifferentialGeometry`. Search it with ripgrep; it is large.
  - Useful entry points: `SmoothCcTensor`, `iteratedCovGrad`, `covGrad`, `covGradBundleEquiv`,
    `TensorRSSpace`, `Tensor.TensorRSRiemannianBundle.tensorRSRiemannianMetric`,
    `riemannianFiberNormSq`, `riemannianVolumeMeasure`.
  - Library theorem names can oversell their content. Read the statement before relying on a
    result.

## Order of work

Pick the first open task below. Otherwise pick an item of `blueprint/map.md` whose dependencies are
all `defined` or `proved`.

### T0: non-vacuity of the pinned definitions — done

See `blueprint/DECISIONS.md` and `ShortTime/Sanity/`. `ShortTime.Sanity.TraceSmooth` shows how to
prove that a natural tensor operation is a smooth bundle map: read it in the trivializations at
`x₀` via `TensorRSSpace.trivializationAt_apply`, then use coordinate frames and
`gInvComp_contMDiffAt`. Reuse this for the coefficients of the model operator.

### T1 onwards: follow the layers

Work through L1 → L4 of `blueprint/map.md`. Layers L3 (linear theory) and L4 (nonlinear theory) meet
only at `thm:linear`, so they can proceed in parallel once its statement exists. Prefer stating an
item in Lean, with `sorry`, before proving the items that use it.

### L3 (linear theory): current plan

The linear theory lives on covariant tensor bundles `T⁰_s` (see `DECISIONS.md`). Files in
`ShortTime/Linear/`, in dependency order:

1. `Flip`, `Divergence`, `PrincipalIBP` (done): flip of a coefficient, `div = tr₁₂ ∇`, one
   integration by parts `⟨T, A∇W⟩ = -⟨∇T, ǍW⟩ - ⟨T, R_A W⟩`.
2. `Family` (parametric smoothness of flips and compositions), `Bounds` (L² bounds from pointwise
   bounds), `Operator` (`LinearOp`, `IsParabolic`, `FlipCoercive`) — done.
3. `GardingOne` (`p = 1`), `Energy` (energy identity, Grönwall), `Uniqueness` (`p = 1`),
   `LegendreOne` (`IsParabolic → FlipCoercive` for `p = 1`) — all done.
4. General `p` (done):
   - `Interp` (interpolation), `Balance` (balanced pairings `⟨∇^a u, B ∇^b u⟩ ≤ C N_p N_{p-1}`),
     `PrincipalIter` (iterated flips `flipIter`, `p` integrations by parts);
   - `RicciPerm`, `RicciSwap`, `RicciEstimate` (`‖σ∇^p u − ∇^p u‖ ≤ C N_{p-2}`);
   - `LegendreGeneral` (Legendre form through `flipIter`, slot reversal);
   - `Garding` (`principal_ibp`, `LinearOp.garding`, `LinearOp.unique_of_isParabolic`).
5. Next: higher energy estimates (`lem:commute`, `prop:energy`), the model operator via DG's
   tensor heat semigroup and spectral Sobolev scale (`TensorHs`), and the continuity method in
   completed parabolic spaces.

### L4: Theorem B (current task)

On covariant bundles Theorem B is proved without `sorry` (`EquationData.solution_unique_cov`):
`lem:difference` (`Linearize.lean`) and the tube lemma `exists_parabolic_segment` (`Tube.lean`) are
done. One `sorry` remains for general bundles:

1. `solution_unique_of_covariant` (`Lowering.lean`): lowering indices, `T^r_s ≅ T⁰_{r+s}`.
   - DG's `covGrad` on `T^r_s` is the Hom-bundle connection (`tensorRSCovariantDerivative_apply`).
   - `♭h(…) = h(v₁♭ ⊗ ⋯ ⊗ v_r♭)(…)` is an iterated flip of `h`.

**Fibre topologies (important).** A tensor fibre has the bundle topology and a norm-induced
topology. They are equal but not definitionally (`tensorRSSpace_topology_eq`).
- Mathlib's `fderiv` works for any topological vector space, so the pinned `partialDeriv` is taken in
  the bundle topology.
- Maps between fibres have no norm instance, so they cannot be integrated.
- Do analysis in the model spaces: `fibIso`, `jetIso`, `EquationData.Fmod`, `fibIso_partialDeriv`,
  `avgFib` in `Linearize.lean`.
- Joint smoothness in `(x, t)` is read in the trivializations at `x₀`: `trivJet`, `localRep`,
  `trivAt_partialDeriv`, `trivAt_opFieldOf`, `contMDiffOn_integral_Icc` (see `coordP_avg`).

**Continuity of the Legendre form in the base point** (`Tube.lean`). The frame `tangentFrame` is not
continuous in `x`. Instead use `exists_legendre_coord`: near `x₀`, in the trivializations at `x₀`, the
Legendre form and `fiberInner` agree with jointly continuous functions of `(x, coordinates)`. The proof
uses smooth sections with constant coordinates (`exists_opField_frame`, `exists_tensor_frame`), so
`lem:legendre-basic` (ii), (iii) can be proved the same way.

**Elaboration timeouts.**
- `h.comp hf` against a goal `fun σ => heavyDef … σ` makes the unifier unfold `heavyDef` (it has the
  larger definitional height) and times out. Instead take `have h := hg.comp hf _`, then
  `simp only [Function.comp_def] at h; exact h`, or hide the heavy function behind an opaque
  variable: `obtain ⟨A, hA⟩ : ∃ A, ∀ m, A m = heavyDef … m := ⟨_, fun _ => rfl⟩`.
- State `rfl` lemmas such as `avgIntegrand_apply` instead of closing goals by `rfl` through a heavy
  definition.
- `linarith`/`nlinarith` use every hypothesis in context, and time out when the context has large
  terms. Move the arithmetic into a standalone lemma (as `mul_le_mul_of_lt_aux`).
- Facts extracted from `∀ᶠ q in 𝓝 (x₀, 0), P q` mention `(y, τ).1`; `dsimp only at h` before
  rewriting with them.

Useful DG entry points for this layer:

- **Operator fields:** `operatorFieldApply`, `ccOperatorFieldComp`, `slotExtend`,
  `covGrad_operatorFieldApply_eq`, `cometricDoubleTraceField`.
- **Integration by parts:** `tensorL2Inner_covGrad_eq_neg_tensorL2Inner_covDivergence`.
- **Pointwise and L² bounds:** `riemannianFiberNormSq_comp_le_mul`, `abs_tensorL2Inner_le`,
  `riemannianFiberNormSq_eq_tensorInnerPointwise`.
- **Parameters:** `Vendor.covGrad_iter_joint`, `Vendor.joint_jet_bdd`,
  `contMDiffOn_clm_section_of_apply`, `Vendor.joint_rs_add`. Import `ShortTime.Vendor.ParametricJets`,
  not the library's `Parametric.*` modules.
- **Pre-Hilbert structure on `SmoothCcTensor`:** `SmoothCcTensor.inner_def`, `toL2`,
  `smoothCcTensor_eq_of_toL2_eq`.

Many useful DG modules sit behind hundreds of unbuilt imports. Before importing one, count its
unbuilt closure. If it is large, prefer re-proving the short lemma locally (as in
`Divergence.lean`). Big library builds need about 2 GB of RAM per Lean worker; with the user's
other applications open, use `LEAN_NUM_THREADS=2`.
