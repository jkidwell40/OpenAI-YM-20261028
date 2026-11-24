import HierarchyBridge
import YM.OS.Core
import YM.Phase.Mixture
import YM.EveryPhase.Extension
import MassGapBridgeSpec_v4

/-!
# Bridge: internal phasewise OS reconstruction → `PhasewiseDiagonal`

STATUS
* Part 1 (OS level, one chamber): proof terms written, UNCOMPILED.
* Part 2 (public ↔ OS identification): v3 proof terms, UNCOMPILED, no `sorry`.
  `public_word_realization` removed (subsumed by the coupled theorem).
* Part 3 (assembly for the concrete `hierarchy F Q`): candidate proof term,
  UNCOMPILED; its elaboration has not been checked.

Uses only existing source objects:
`Chamber.atBirth`, `Kernel.Gram.measure`, `Semigroup.emerges` / `orth`,
`Chamber.UniqueHeat`, `Chamber.omega0`, `OS.nil_norm`, `Table.gram`,
`Table.at_project`, `Table.readAt`, `OS.invariance`, `place_exists`,
`EveryPhase.all_characters`.

Mathlib names flagged as likely to need adjustment:
`Filter.Tendsto.inner`, `Submodule.starProjection_singleton`.
-/

set_option autoImplicit false
noncomputable section

/-! ## Part 1: one chamber, pointwise positive-time words (UNCOMPILED) -/

namespace YM.OS.Chamber
open Filter
open scoped NNReal Topology InnerProductSpace

variable {G : Gauge} {L : Register G} {S : Table L} {a : Axis} (C : Chamber S a)

/-- Contraction bound for the diagonal OS pairing. -/
theorem pair_bound (t : ℝ≥0) (ψ : C.H) :
    ‖inner ℂ ψ (C.flow.E t ψ)‖ ≤ ‖ψ‖ ^ 2 := by
  calc ‖inner ℂ ψ (C.flow.E t ψ)‖ ≤ ‖ψ‖ * ‖C.flow.E t ψ‖ := norm_inner_le_norm _ _
    _ ≤ ‖ψ‖ * ‖ψ‖ := by
        gcongr
        exact ((C.flow.E t).le_opNorm ψ).trans
          (mul_le_of_le_one_left (norm_nonneg _) (C.flow.shrinks t))
    _ = ‖ψ‖ ^ 2 := (sq _).symm

/-- The diagonal pairing converges to the ground-state pairing. -/
theorem pair_tendsto (ψ : C.H) :
    Tendsto (fun t : ℝ≥0 => inner ℂ ψ (C.flow.E t ψ)) atTop
      (𝓝 (inner ℂ ψ (C.flow.orth ψ))) :=
  tendsto_const_nhds.inner (C.flow.emerges ψ)

/-- `UniqueHeat` plus `omega0 ∈ ground`: the ground space is the vacuum line. -/
theorem ground_eq_span (hU : C.UniqueHeat) :
    C.flow.ground = Submodule.span ℂ {C.omega} := by
  apply le_antisymm
  · intro x hx
    obtain ⟨z, hz⟩ := hU ⟨x, hx⟩
    rw [Submodule.mem_span_singleton]
    exact ⟨z, congrArg Subtype.val hz⟩
  · rw [Submodule.span_singleton_le_iff_mem]
    exact C.omega0.2

/-- Ground projection of a vector, for a normalized vacuum.
Flagged: depends on the current Mathlib name for the projection onto a line. -/
theorem orth_eq (hU : C.UniqueHeat) (hΩ : ‖C.omega‖ = 1) (ψ : C.H) :
    C.flow.orth ψ = inner ℂ C.omega ψ • C.omega := by
  have hg := C.ground_eq_span hU
  unfold Semigroup.orth
  -- Rewriting the submodule inside `starProjection` needs `subst`-style care
  -- because of the `HasOrthogonalProjection` instance; done via `congr`.
  have : (C.flow.ground).starProjection ψ =
      (Submodule.span ℂ {C.omega}).starProjection ψ := by
    congr 1 <;> simp [hg]
  rw [this, Submodule.starProjection_singleton, hΩ]
  simp

/-- Vacuum expectation in the OS space is the table expectation. -/
theorem omega_pair (v : Future L a) :
    inner ℂ C.omega (C.GNS.plant v) = S.expect v.val := by
  unfold Chamber.omega
  rw [C.GNS.measure]
  simp [Table.gram, air, Word.reflectedPoint]  -- CI fix: qualified name

/-- The vacuum limit of the diagonal pairing, for a normalized table. -/
theorem pair_limit (hU : C.UniqueHeat) (hB : S.Basic) (v : Future L a) :
    Tendsto (fun t : ℝ≥0 =>
        inner ℂ (C.GNS.plant v) (C.flow.E t (C.GNS.plant v))) atTop
      (𝓝 (star (S.expect v.val) * S.expect v.val)) := by
  have hΩ : ‖C.omega‖ = 1 := OS.nil_norm C.GNS hB
  have h := C.pair_tendsto (C.GNS.plant v)
  rw [C.orth_eq hU hΩ, inner_smul_right, C.omega_pair, ← inner_conj_symm,
    C.omega_pair] at h
  simpa [mul_comm] using h

/-- Time evolution in the OS space is translation of the word
(`atBirth` plus the Gram identity): the diagonal pairing *is* a table expectation. -/
theorem pair_eq_gram (v : Future L a) (t : ℝ≥0) :
    inner ℂ (C.GNS.plant v) (C.flow.E t (C.GNS.plant v)) =
      S.gram a v.val (travel v t).val := by
  rw [← C.atBirth, C.GNS.measure]

end YM.OS.Chamber

/-! ## Part 2: public correlations ↔ internal words (v3: PROOF TERMS, UNCOMPILED)

Construction (τ = 0):
* lift tags to tokens, `tok j = quoteTag (a j)`; `v = realize tok x`;
* `place_exists` gives `s` with `w := carry v s` in the positive-time slab;
* reflected companion: tokens `rtok j = reflectedToken timeAxis (tok j)`,
  tags `b = classTokens ∘ rtok`, positions `y j = timeFlip (x j + s) - s`.

Only phase-table facts are used, never `Reconstructed`:
`spectate F (some i) : (F.α.ensemble i).Hierarchy` (laws, spin, translations)
and `F.phase.phase.retains i` (quotient compatibility).

Fragile points, in order of risk: the `simp` normal forms in `e_reflect`,
`e_carry`, `e_R` (coercion `x j` vs `x.ofLp j`, `List.map_ofFn`,
`List.map_reverse`), `theta_time`, and the `change` to `YM.OPE.observe`.
The `cross` step assumes `x j` and `x.ofLp j` are the same term (the
`WithLp` coercion to functions is `ofLp`); if not, add `PiLp.ofLp_apply`. -/

namespace YangMills
open YM YM.Spec YM.OPE YM.OPE.Orbits YM.Nonperturbative YM.Boundary YM.OS
open Function Set MeasureTheory Filter
open scoped BigOperators Classical Topology NNReal

variable {g : GaugeGroup} {C : Family g.core} {p : Extraction.Order} {S : Table C.book}
variable (F : Final C p S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

section CoupledPair

/-- Reflection through the Euclidean time-zero plane, as used by `reflect`. -/
abbrev timeFlip (z : E4) : E4 := Ortho.move (Signed.reflect timeAxis) z

lemma theta_injective : Injective timeFlip := Ortho.move_injective _

/-- Flagged: relies on the simp lemma used in `Word.strictly`. -/
lemma theta_time (z : E4) : (timeFlip z) timeAxis = - z timeAxis := by simp [timeFlip]

lemma shift_eq (t : ℝ) : euclideanTimeShift t = t • basis timeAxis := by
  ext i; by_cases h : i = timeAxis <;> simp [euclideanTimeShift, h]

/-- `quoteTag` is a section of `classTokens` (same argument as in
`publicReconstruction`, field `represents`). -/
lemma classTokens_quote (a : S.Tag) : S.classTokens (quoteTag a) = a := by
  change Sigma.mk a.1 (S.project _ (S.representative _ a.2)) = a
  rw [S.rep]

/-- The coupled public-to-OS identity, with τ = 0. UNCOMPILED. -/
theorem coupled_pair {n : ℕ}
    (a : Fin n → (hierarchy F Q).Tag)
    (x : Points n) (hx : x ∈ WilsonFamily.separated n) :
    ∃ (b : Fin n → (hierarchy F Q).Tag) (y : Fin n → Spacetime)
      (w : Future C.book timeAxis),
      (∀ i : (hierarchy F Q).Character,
        (hierarchy F Q).correlation (some i) a x = (F.α.ensemble i).expect w.val) ∧
      (∀ i : (hierarchy F Q).Character,
        (hierarchy F Q).correlation (some i) b (WithLp.toLp 2 y) =
          (starRingEnd ℂ) ((hierarchy F Q).correlation (some i) a x)) ∧
      (∀ t : ℝ, 0 ≤ t →
        Injective (Sum.elim y (fun j : Fin n => x.ofLp j + euclideanTimeShift t))) ∧
      (∀ (i : (hierarchy F Q).Character) (t : ℝ), 0 ≤ t →
        (hierarchy F Q).phasePairAt (some i) b y a x.ofLp t =
          (F.α.ensemble i).gram timeAxis w.val (travel w t.toNNReal).val) := by
  classical
  have hxinj : Injective x.ofLp := hx
  -- the word, its positive-time translate, and the reflected companion
  set tok : Fin n → C.book.Token := fun j => quoteTag (a j) with htok
  set v : C.book.Word := Word.realize tok x with hv
  have hd : Word.distinct v := (Word.realized ..).mpr hx
  obtain ⟨s, d, hs⟩ := OS.Spread.Resolution.place_exists hd
  have hpos : Word.Positive (Word.carry v s) timeAxis := hs.2.1
  set w : Future C.book timeAxis := ⟨Word.carry v s, hpos⟩ with hw
  have hpt : ∀ j, 0 < (x j + s) timeAxis := fun j =>
    hpos.2 (x j + s, tok j) (by
      simp only [Word.carry, hv, Word.realize, List.mem_map, List.mem_ofFn, Set.mem_range]
      exact ⟨(x j, tok j), ⟨j, rfl⟩, rfl⟩)
  set rtok : Fin n → C.book.Token := fun j => C.book.reflectedToken timeAxis (tok j)
    with hrtok
  set b : Fin n → (hierarchy F Q).Tag := fun j => S.classTokens (rtok j) with hb
  set y : Fin n → Spacetime := fun j => timeFlip (x j + s) - s with hy
  -- per-phase facts
  have hH : ∀ i, (F.α.ensemble i).Hierarchy := fun i => spectate F (some i)
  have hr : ∀ i, (F.α.ensemble i).respects S := fun i => spectate_respects F (some i)
  -- (geometry) injectivity of the two-block configuration for t ≥ 0
  have hinj : ∀ t : ℝ, 0 ≤ t →
      Injective (Sum.elim y (fun j : Fin n => x.ofLp j + euclideanTimeShift t)) := by
    intro t ht
    have cross : ∀ j k, y j ≠ x.ofLp k + euclideanTimeShift t := by
      intro j k h
      have h' := congrArg (fun z : E4 => z timeAxis) h
      have hj := hpt j
      have hk := hpt k
      simp [hy, theta_time, shift_eq, basis_eq] at h' hj hk
      linarith
    rintro (j | j) (k | k) h
    · simp only [Sum.elim_inl, hy] at h
      exact congrArg Sum.inl
        (hxinj (add_right_cancel (theta_injective (sub_left_injective h))))
    · exact absurd h (cross j k)
    · exact absurd h.symm (cross k j)
    · simp only [Sum.elim_inr] at h
      exact congrArg Sum.inr (hxinj (add_right_cancel h))
  -- (c1) one-word identity. Same route as the source's own proof of this
  -- identity in `publicReconstruction` (HierarchyBridge.lean, field `mixture`):
  -- `quoteTag` lifts by `representative`, which is what `useAt` applies, so
  -- `readAt` + `rfl` suffices; `at_project` is needed only for
  -- `classTokens ∘ v` (used in c2 and c4).
  have h1 : ∀ i, (hierarchy F Q).correlation (some i) a x =
      (F.α.ensemble i).expect w.val := by
    intro i
    rw [show w.val = Word.carry v s from rfl,
      OS.invariance (hH i).translations hd s, hv, Table.readAt]
    rfl
  refine ⟨b, y, w, h1, ?_, hinj, ?_⟩
  -- (c2) reflected one-word identity
  · intro i
    have hyinj : Injective y := fun j k h =>
      Sum.inl_injective (hinj 0 le_rfl (a₁ := Sum.inl j) (a₂ := Sum.inl k) (by simpa using h))
    have hyc : WithLp.toLp 2 y ∈ conf n := hyinj
    refine (Table.at_project S (F.α.ensemble i) (hH i).laws.toSymmetric (hr i) hyc rtok).trans ?_
    rw [← Table.readAt, h1 i, starRingEnd_apply, show w.val = Word.carry v s from rfl,
      ← OS.twice_expect (hH i).laws (hH i).spin timeAxis _ hpos.1,
      ← OS.invariance (hH i).translations ((Word.realized ..).mpr hyc) s]
    have e_reflect : Word.reflect (Word.carry v s) timeAxis =
        (List.ofFn fun j => (timeFlip (x j + s), rtok j)).reverse := by
      rw [Word.reflectedPoint]
      simp [Word.carry, hv, Word.realize, List.map_ofFn, List.map_reverse, hrtok]
      -- CI fix: remaining goal is a definitional function equality
      funext j; rfl
    have e_carry : Word.carry (Word.realize rtok (WithLp.toLp 2 y)) s =
        List.ofFn fun j => (timeFlip (x j + s), rtok j) := by
      simp [Word.carry, Word.realize, List.map_ofFn, hy]
      -- CI fix: remaining goal needs `sub_add_cancel` pointwise
      funext j; simp
    refine (Table.order (F.α.ensemble i) (hH i).laws.toSymmetric
      (Word.reflects timeAxis hpos.1) ?_)
    rw [e_reflect, e_carry]
    exact List.reverse_perm _
  -- (c4) pair identity
  · intro i t ht
    set X : Fin n ⊕ Fin n → E4 := Sum.elim y (fun j : Fin n => x.ofLp j + euclideanTimeShift t)
      with hX
    set V : Fin n ⊕ Fin n → C.book.Token := Sum.elim rtok tok with hV
    have hXinj : Injective X := hinj t ht
    have htag : (Sum.elim b a : Fin n ⊕ Fin n → S.Tag) = S.classTokens ∘ V := by
      funext q
      cases q with
      | inl j => rfl
      | inr j => exact (classTokens_quote (a j)).symm
    dsimp only [Hierarchy.phasePairAt, Hierarchy.grouped]
    have hconf : WithLp.toLp 2 (X ∘ (Fintype.equivFin (Fin n ⊕ Fin n)).symm) ∈ conf _ :=
      hXinj.comp (Fintype.equivFin (Fin n ⊕ Fin n)).symm.injective
    -- CI fix: `rw [htag]` failed (motive not type-correct at instance
    -- transparency: `(hierarchy F Q).Character` vs `F.α.space.X`). Rewrite
    -- the tag list by `congrArg` instead, elaborated at default transparency.
    refine (congrArg (fun z : Fin n ⊕ Fin n → (hierarchy F Q).Tag =>
        (hierarchy F Q).correlation (some i) (z ∘ ⇑(Fintype.equivFin (Fin n ⊕ Fin n)).symm)
          (WithLp.toLp 2 (X ∘ ⇑(Fintype.equivFin (Fin n ⊕ Fin n)).symm))) htag).trans ?_
    refine (Table.at_project S (F.α.ensemble i) (hH i).laws.toSymmetric (hr i) hconf
      (V ∘ (Fintype.equivFin (Fin n ⊕ Fin n)).symm)).trans ?_
    rw [← Table.readAt]
    change YM.OPE.observe (F.α.ensemble i) X V = _
    rw [← YM.OPE.observe_carry (F.α.ensemble i) (hH i).translations V hXinj s]
    -- right side: `gram w (travel w t) = expect (reflect w ++ carry w (t • e))`
    set R : C.book.Word := Word.reflect w.val timeAxis ++ (travel w t.toNNReal).val with hR
    have hdR : Word.distinct R := Word.twoSides hpos (travel w t.toNNReal).property
    change (F.α.ensemble i).expect (YM.OPE.worded (fun k => X k + s) V) =
      (F.α.ensemble i).expect R
    refine Table.order (F.α.ensemble i) (hH i).laws.toSymmetric hdR ?_
    have hX's : Injective (fun k => X k + s) := (add_left_injective s).comp hXinj
    have e_R : R = (List.ofFn fun j => (timeFlip (x j + s), rtok j)).reverse ++
        List.ofFn fun j => (x j + s + t • basis timeAxis, tok j) := by
      simp [hR, hw, travel, Word.reflectedPoint, Word.carry, hv, Word.realize, List.map_ofFn,
        List.map_reverse, Function.comp, hrtok, Real.coe_toNNReal t ht]
      -- CI fix: remaining goal holds by definition (same shape as `e_reflect`)
      rfl
    rw [List.perm_ext_iff_of_nodup
      (List.nodup_iff_injective_get.mpr (Word.plantInj hdR))
      (YM.OPE.worded_nodup V hX's)]
    intro q
    rw [e_R, YM.OPE.worded_get]
    simp only [List.mem_append, List.mem_reverse, List.mem_ofFn, Set.mem_range]
    constructor
    · rintro (⟨j, rfl⟩ | ⟨j, rfl⟩)
      · exact ⟨Sum.inl j, by simp [hX, hV, hy]⟩
      · exact ⟨Sum.inr j, by simp [hX, hV, shift_eq, add_right_comm]⟩
    · rintro ⟨(j | j), rfl⟩
      · exact Or.inl ⟨j, by simp [hX, hV, hy]⟩
      · exact Or.inr ⟨j, by simp [hX, hV, shift_eq, add_right_comm]⟩

/-- v2's statement, recovered with `τ = 0` (UNCOMPILED). -/
theorem public_pair_eq_gram {n : ℕ}
    (a : Fin n → (hierarchy F Q).Tag)
    (x : Points n) (hx : x ∈ WilsonFamily.separated n) :
    ∃ (b : Fin n → (hierarchy F Q).Tag)
      (y : Fin n → Spacetime)
      (w : Future C.book timeAxis) (τ : ℝ),
      0 ≤ τ ∧
      (∀ i : (hierarchy F Q).Character,
        (hierarchy F Q).correlation (some i) a x =
          (F.α.ensemble i).expect w.val) ∧
      (∀ i : (hierarchy F Q).Character,
        (hierarchy F Q).correlation (some i) b (WithLp.toLp 2 y) =
          (starRingEnd ℂ) ((hierarchy F Q).correlation (some i) a x)) ∧
      (∀ t : ℝ, τ ≤ t →
        Injective (Sum.elim y (fun j : Fin n => x.ofLp j + euclideanTimeShift t))) ∧
      (∀ (i : (hierarchy F Q).Character) (t : ℝ), τ ≤ t →
        (hierarchy F Q).phasePairAt (some i) b y a x.ofLp t =
          (F.α.ensemble i).gram timeAxis w.val
            (travel w (t - τ).toNNReal).val) := by
  obtain ⟨b, y, w, h1, h2, h3, h4⟩ := coupled_pair F Q a x hx
  refine ⟨b, y, w, 0, le_rfl, h1, h2, h3, fun i t ht => ?_⟩
  rw [sub_zero]
  exact h4 i t ht

end CoupledPair

/-! ## Part 3: assembly (UNCOMPILED PROOF ATTEMPT) -/

/-- Target. Proof plan, all ingredients located in the source:
1. `EveryPhase.all_characters F` gives `L` with `Completed F L`;
   `L.chambers i : Chamber (F.α.ensemble i) timeAxis`.
2. Coupled `public_pair_eq_gram` gives one shared positive-time word,
   its reflected public companion, and an injective two-block configuration.
   `Chamber.pair_eq_gram` identifies the pair with OS evolution.
3. Limit: `Chamber.pair_limit` with `(Completed.euclid i)` and
   `(F.phase.phase.states i).laws`; use the **same** `w` supplied
   by the coupled pair theorem to rewrite `expect w` as the public correlation.
4. Conjugation field: supplied by the coupled theorem (proved using
   `OS.twice_expect`).
5. Injectivity for `t ≥ τ`: supplied by the coupled theorem.
6. Bound: `Chamber.pair_bound`; `‖plant w‖²` is a public correlation at a
   separated configuration, continuous in `i` (`characterContinuity`),
   hence bounded on the compact character space. -/
theorem phasewiseDiagonal_hierarchy : (hierarchy F Q).PhasewiseDiagonal := by
  classical
  -- Internal phasewise reconstruction, available for every `Final`.
  obtain ⟨L, hCompleted⟩ := EveryPhase.all_characters F
  have hReconstructed : (hierarchy F Q).Reconstructed :=
    publicReconstruction F Q L hCompleted
  refine ⟨?_⟩
  intro n a x hx
  obtain ⟨b, y, w, hWord, hConj, hSep, hPair⟩ := coupled_pair F Q a x hx
  -- Continuity at time zero, through the public reconstruction of this same hierarchy.
  have hSep0 : Function.Injective
      (Sum.elim y (fun j : Fin n => x.ofLp j + euclideanTimeShift 0)) :=
    hSep 0 le_rfl
  have hContinuous0 : Continuous (fun ξ : (hierarchy F Q).Character =>
      (hierarchy F Q).phasePairAt (some ξ) b y a x.ofLp 0) := by
    dsimp only [Hierarchy.phasePairAt, Hierarchy.grouped]
    exact hReconstructed.characterContinuity _ _
      (Hierarchy.grouped_config_separated y _ hSep0)
  let f₀ : C((hierarchy F Q).Character, ℂ) :=
    ⟨(fun ξ => (hierarchy F Q).phasePairAt (some ξ) b y a x.ofLp 0),
      hContinuous0⟩
  let K : ℝ := ‖f₀‖
  have hKnonneg : 0 ≤ K := norm_nonneg _
  have hKbound (ξ : (hierarchy F Q).Character) :
      ‖(hierarchy F Q).phasePairAt (some ξ) b y a x.ofLp 0‖ ≤ K :=
    ContinuousMap.norm_coe_le_norm f₀ ξ
  refine ⟨b, y, 0, K, le_rfl, hKnonneg, hConj, hSep, ?_, ?_⟩
  · -- Semigroup contraction plus the time-zero OS Gram identity.
    intro ξ t ht
    let V := L.chambers ξ
    let ψ := V.GNS.plant w
    have hPairEq : (hierarchy F Q).phasePairAt (some ξ) b y a x.ofLp t =
        inner ℂ ψ (V.flow.E t.toNNReal ψ) := by
      rw [hPair ξ t ht]
      exact (V.pair_eq_gram w t.toNNReal).symm
    have hAtZero : (hierarchy F Q).phasePairAt (some ξ) b y a x.ofLp 0 =
        (F.α.ensemble ξ).gram timeAxis w.val w.val := by
      simpa using hPair ξ 0 le_rfl
    have hNormSq : ‖ψ‖ ^ 2 =
        ‖(hierarchy F Q).phasePairAt (some ξ) b y a x.ofLp 0‖ := by
      rw [hAtZero, ← V.GNS.measure w w]
      simp [ψ, inner_self_eq_norm_sq_to_K]
    rw [hPairEq]
    exact (V.pair_bound t.toNNReal ψ).trans (hNormSq.le.trans (hKbound ξ))
  · -- Passage from the nonnegative-time semigroup limit to real `atTop`.
    intro ξ
    let V := L.chambers ξ
    let ψ := V.GNS.plant w
    have hToNNReal : Filter.Tendsto (fun t : ℝ => t.toNNReal)
        Filter.atTop Filter.atTop := by
      apply Filter.tendsto_atTop.2
      intro z
      filter_upwards [Filter.eventually_ge_atTop (z : ℝ)] with t ht
      apply NNReal.coe_le_coe.mp
      rw [Real.coe_toNNReal t (le_trans z.property ht)]  -- CI fix: explicit `t`
      exact ht
    have hLimit :=
      (V.pair_limit (hCompleted.euclid ξ) (F.phase.phase.states ξ).laws w).comp hToNNReal
    have hEq : (fun t : ℝ => (hierarchy F Q).phasePairAt
          (some ξ) b y a x.ofLp t) =ᶠ[Filter.atTop]
        (fun t : ℝ => inner ℂ ψ (V.flow.E t.toNNReal ψ)) := by
      filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
      exact hPair ξ t ht |>.trans (V.pair_eq_gram w t.toNNReal).symm
    have hResult := hLimit.congr' hEq.symm
    simpa only [hWord ξ, starRingEnd_apply] using hResult

end YangMills
