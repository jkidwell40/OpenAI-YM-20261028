import Construction
import PhasewiseDiagonalBridge_v3

/-!
# Track A, step 1: uniform mixed clustering ⇒ energy gap (constructed hierarchy)

STATUS: UNCOMPILED. No `sorry`. Existing definitions (`UniformMixedClustering`,
`HasEnergyGap`, `SpectralEnergyObligation`) are used unchanged.

Route (all in the selected phase's OS space, then transported by `J`):
1. `laplace_exclusion` (general measure theory): a Laplace bound
   `∫_{p₀>0} e^{-s p₀} dμ ≤ K e^{-m s}` forces `μ {0 < p₀ < m/2} = 0`.
2. `clm_eq_zero_of_dense` (general Hilbert space): an operator vanishing on a
   set with dense span is zero.
3. `internal_pair` (reverse correspondence): every positive-time internal word
   has public tags/positions whose correlations, reflected companion and pair
   correlation are the OS quantities. Mirrors the compiled `coupled_pair`
   with no translation step.
4. Zero-energy term identified explicitly: `reflection_projection`
   (`orth = region zeroE`), `at_pair`, then `orth_eq` + `omega_pair`.
5. Transport to Wightman space by `Attachment.projections` and the isometry
   `Attachment.acts.scale`; selected phase via `Almanac.baseR`.

Upstream lemmas used: `EveryPhase.boltzmann`, `EveryPhase.residual`,
`EveryPhase.boltz_int`, `EveryPhase.reflection_projection`, `Semigroup.bright`,
`PVM.at_pair`, `PVM.null_pair`, `Kernel.Gram.dense`, `Attachment.projections`,
`EveryPhase.all_characters`, `Almanac.baseR`.

Not used, by design: any Lorentz boost argument.
-/

set_option autoImplicit false
noncomputable section

namespace YangMills
open YM YM.Spec YM.OPE YM.OPE.Orbits YM.Nonperturbative YM.Boundary YM.OS
open Function Set MeasureTheory Filter
open scoped BigOperators Classical Topology NNReal InnerProductSpace

/-! ## 1. General measure-theoretic lemma -/

/-- Laplace-transform exclusion. Independent of Yang–Mills. -/
theorem laplace_exclusion (μ : Measure E4) [IsFiniteMeasure μ]
    (hpos : ∀ᵐ p ∂μ, 0 ≤ p timeAxis)
    {m K : ℝ} (hm : 0 < m) (s₀ : ℝ≥0)
    (hdecay : ∀ s : ℝ≥0, s₀ ≤ s →
      (∫ p in EveryPhase.aboveE, EveryPhase.boltz s p ∂μ) ≤ K * Real.exp (-m * s)) :
    μ {p : E4 | 0 < p timeAxis ∧ p timeAxis < m / 2} = 0 := by
  set R : Set E4 := {p : E4 | 0 < p timeAxis ∧ p timeAxis < m / 2} with hRdef
  have hRm : MeasurableSet R :=
    (isOpen_lt continuous_const Mink.clock_cont).measurableSet.inter
      (isOpen_lt Mink.clock_cont continuous_const).measurableSet
  have hRsub : R ⊆ EveryPhase.aboveE := fun p hp => hp.1
  have hint := EveryPhase.boltz_int μ hpos
  have hbound : ∀ s : ℝ≥0, s₀ ≤ s →
      μ.real R * Real.exp (-(m / 2) * s) ≤ K * Real.exp (-m * s) := by
    intro s hs
    calc μ.real R * Real.exp (-(m / 2) * s)
        = ∫ _ in R, Real.exp (-(m / 2) * s) ∂μ := by
          rw [setIntegral_const, smul_eq_mul]
      _ ≤ ∫ p in R, EveryPhase.boltz s p ∂μ := by
          refine setIntegral_mono_on (integrable_const _).integrableOn
            (hint s).integrableOn hRm (fun p hp => ?_)
          unfold EveryPhase.boltz
          apply Real.exp_le_exp.mpr
          have hp2 : p timeAxis < m / 2 := hp.2
          have hs0 : (0 : ℝ) ≤ s := NNReal.coe_nonneg s
          have := mul_le_mul_of_nonneg_left hp2.le hs0
          linarith
      _ ≤ ∫ p in EveryPhase.aboveE, EveryPhase.boltz s p ∂μ := by
          refine setIntegral_mono_set (hint s).integrableOn ?_ ?_
          · exact Eventually.of_forall fun p => (Real.exp_pos _).le
          · exact Eventually.of_forall fun p hp => hRsub hp
      _ ≤ K * Real.exp (-m * s) := hdecay s hs
  have hreal : ∀ s : ℝ≥0, s₀ ≤ s → μ.real R ≤ K * Real.exp (-(m / 2) * s) := by
    intro s hs
    have h := hbound s hs
    have he : Real.exp (-m * s) = Real.exp (-(m / 2) * s) * Real.exp (-(m / 2) * s) := by
      rw [← Real.exp_add]; ring_nf
    rw [he, ← mul_assoc] at h
    exact le_of_mul_le_mul_right h (Real.exp_pos _)
  have hlim : Tendsto (fun s : ℝ≥0 => K * Real.exp (-(m / 2) * s)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun s : ℝ≥0 => (m / 2) * (s : ℝ)) atTop atTop :=
      (NNReal.tendsto_coe_atTop.mpr tendsto_id).const_mul_atTop (by linarith)
    have h2 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul K
    simpa [Function.comp, neg_mul] using h2
  have hle : μ.real R ≤ 0 :=
    ge_of_tendsto hlim (eventually_atTop.mpr ⟨s₀, fun s hs => hreal s hs⟩)
  have hzero : μ.real R = 0 := le_antisymm hle measureReal_nonneg
  exact (measureReal_eq_zero_iff (measure_ne_top μ R)).mp hzero

/-! ## 2. General Hilbert-space lemma -/

/-- An operator that kills every vector of a family with dense span is zero. -/
theorem clm_eq_zero_of_dense {H : Hilbert} (P : H.Op) {ι : Type*} (f : ι → H)
    (hd : Dense ((Submodule.span ℂ (Set.range f)) : Set H))
    (h : ∀ i, P (f i) = 0) : P = 0 :=
  ContinuousLinearMap.ext_on hd (fun x hx => by
    obtain ⟨i, rfl⟩ := hx
    rw [h i, ContinuousLinearMap.zero_apply])

/-! ## 3. Reverse correspondence: internal positive-time words → public data -/

section Reverse
variable {g : GaugeGroup} {C : Family g.core} {p : Extraction.Order} {S : Table C.book}
variable (F : Final C p S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

/-- Every positive-time internal word is represented, in every phase, by
public tags at its own positions; its reflection and its pair correlation
match the OS quantities. UNCOMPILED. -/
theorem internal_pair (v : Future C.book timeAxis) :
    ∃ (a b : Fin v.val.length → (hierarchy F Q).Tag) (y : Fin v.val.length → Spacetime),
      Word.positions v.val ∈ WilsonFamily.separated v.val.length ∧
      (∀ i : (hierarchy F Q).Character,
        (hierarchy F Q).correlation (some i) a (Word.positions v.val) =
          (F.α.ensemble i).expect v.val) ∧
      (∀ i : (hierarchy F Q).Character,
        (hierarchy F Q).correlation (some i) b (WithLp.toLp 2 y) =
          (starRingEnd ℂ) ((hierarchy F Q).correlation (some i) a (Word.positions v.val))) ∧
      (∀ t : ℝ, 0 ≤ t →
        Injective (Sum.elim y (fun j => (Word.positions v.val).ofLp j + euclideanTimeShift t))) ∧
      (∀ (i : (hierarchy F Q).Character) (t : ℝ), 0 ≤ t →
        (hierarchy F Q).phasePairAt (some i) b y a (Word.positions v.val).ofLp t =
          (F.α.ensemble i).gram timeAxis v.val (travel v t.toNNReal).val) := by
  classical
  set x := Word.positions v.val with hxdef
  set tok := Word.tokens v.val with htok
  have hd : Word.distinct v.val := v.property.1
  have hxc : x ∈ conf v.val.length := hd
  have hxinj : Injective x.ofLp := hd
  have hpt : ∀ j, 0 < (x.ofLp j) timeAxis := fun j =>
    v.property.2 (v.val.get j) (List.get_mem v.val j)
  set rtok : Fin v.val.length → C.book.Token :=
    fun j => C.book.reflectedToken timeAxis (tok j) with hrtok
  set a : Fin v.val.length → (hierarchy F Q).Tag := fun j => S.classTokens (tok j) with ha
  set b : Fin v.val.length → (hierarchy F Q).Tag := fun j => S.classTokens (rtok j) with hb
  set y : Fin v.val.length → Spacetime := fun j => timeFlip (x.ofLp j) with hy
  have hH : ∀ i, (F.α.ensemble i).Hierarchy := fun i => spectate F (some i)
  have hr : ∀ i, (F.α.ensemble i).respects S := fun i => spectate_respects F (some i)
  -- one-word identity
  have h1 : ∀ i, (hierarchy F Q).correlation (some i) a x = (F.α.ensemble i).expect v.val := by
    intro i
    refine (Table.at_project S (F.α.ensemble i) (hH i).laws.toSymmetric (hr i) hxc tok).trans ?_
    rw [← Table.readAt]
    exact congrArg (F.α.ensemble i).expect (Word.rebuilt v.val)
  -- separation for t ≥ 0
  have hinj : ∀ t : ℝ, 0 ≤ t →
      Injective (Sum.elim y (fun j => x.ofLp j + euclideanTimeShift t)) := by
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
      exact congrArg Sum.inl (hxinj (theta_injective h))
    · exact absurd h (cross j k)
    · exact absurd h.symm (cross k j)
    · simp only [Sum.elim_inr] at h
      exact congrArg Sum.inr (hxinj (add_right_cancel h))
  have hyinj : Injective y := fun j k h => hxinj (theta_injective h)
  -- reflected one-word identity
  have hP : ∀ i, (hierarchy F Q).correlation (some i) b (WithLp.toLp 2 y) =
      (starRingEnd ℂ) ((hierarchy F Q).correlation (some i) a x) := by
    intro i
    have hyc : WithLp.toLp 2 y ∈ conf v.val.length := hyinj
    refine (Table.at_project S (F.α.ensemble i) (hH i).laws.toSymmetric (hr i) hyc rtok).trans ?_
    rw [← Table.readAt, h1 i, starRingEnd_apply,
      ← OS.twice_expect (hH i).laws (hH i).spin timeAxis _ v.property.1]
    refine Table.order (F.α.ensemble i) (hH i).laws.toSymmetric
      (Word.reflects timeAxis v.property.1) ?_
    have e1 : Word.realize rtok (WithLp.toLp 2 y) =
        v.val.map (fun p : C.book.Plant =>
          (Ortho.move (Signed.reflect timeAxis) p.1, C.book.reflectedToken timeAxis p.2)) := by
      calc Word.realize rtok (WithLp.toLp 2 y)
          = List.ofFn ((fun p : C.book.Plant =>
              (Ortho.move (Signed.reflect timeAxis) p.1, C.book.reflectedToken timeAxis p.2))
                ∘ v.val.get) := rfl
        _ = (List.ofFn v.val.get).map (fun p : C.book.Plant =>
              (Ortho.move (Signed.reflect timeAxis) p.1, C.book.reflectedToken timeAxis p.2)) := by
          rw [List.map_ofFn]
        _ = _ := by rw [List.ofFn_get]
    rw [Word.reflectedPoint, e1]
    exact (List.reverse_perm v.val).map _
  refine ⟨a, b, y, hd, h1, hP, hinj, ?_⟩
  -- pair identity
  intro i t ht
  set X : Fin v.val.length ⊕ Fin v.val.length → E4 :=
    Sum.elim y (fun j => x.ofLp j + euclideanTimeShift t) with hX
  set V : Fin v.val.length ⊕ Fin v.val.length → C.book.Token := Sum.elim rtok tok with hV
  have hXinj : Injective X := hinj t ht
  have htag : (Sum.elim b a : Fin v.val.length ⊕ Fin v.val.length → S.Tag) = S.classTokens ∘ V := by
    funext q
    cases q with
    | inl j => rfl
    | inr j => rfl
  dsimp only [Hierarchy.phasePairAt, Hierarchy.grouped]
  have hconf : WithLp.toLp 2
      (X ∘ (Fintype.equivFin (Fin v.val.length ⊕ Fin v.val.length)).symm) ∈ conf _ :=
    hXinj.comp (Fintype.equivFin (Fin v.val.length ⊕ Fin v.val.length)).symm.injective
  refine (congrArg (fun z : Fin v.val.length ⊕ Fin v.val.length → (hierarchy F Q).Tag =>
      (hierarchy F Q).correlation (some i)
        (z ∘ ⇑(Fintype.equivFin (Fin v.val.length ⊕ Fin v.val.length)).symm)
        (WithLp.toLp 2 (X ∘ ⇑(Fintype.equivFin (Fin v.val.length ⊕ Fin v.val.length)).symm)))
      htag).trans ?_
  refine (Table.at_project S (F.α.ensemble i) (hH i).laws.toSymmetric (hr i) hconf
    (V ∘ (Fintype.equivFin (Fin v.val.length ⊕ Fin v.val.length)).symm)).trans ?_
  rw [← Table.readAt]
  change YM.OPE.observe (F.α.ensemble i) X V = _
  have hdR : Word.distinct (Word.reflect v.val timeAxis ++ (travel v t.toNNReal).val) :=
    Word.twoSides v.property (travel v t.toNNReal).property
  change (F.α.ensemble i).expect (YM.OPE.worded X V) =
    (F.α.ensemble i).expect (Word.reflect v.val timeAxis ++ (travel v t.toNNReal).val)
  refine Table.order (F.α.ensemble i) (hH i).laws.toSymmetric hdR ?_
  rw [List.perm_ext_iff_of_nodup
    (List.nodup_iff_injective_get.mpr (Word.plantInj hdR))
    (YM.OPE.worded_nodup V hXinj)]
  intro q
  rw [YM.OPE.worded_get]
  simp only [List.mem_append, Word.reflectedPoint, List.mem_map, List.mem_reverse, travel,
    Word.carry]
  have hcarry : ∀ j, ((v.val.get j).1 + ((t.toNNReal : ℝ≥0) : ℝ) • basis timeAxis, (v.val.get j).2)
      = (X (Sum.inr j), V (Sum.inr j)) := by
    intro j
    refine Prod.ext ?_ rfl
    show (v.val.get j).1 + ((t.toNNReal : ℝ≥0) : ℝ) • basis timeAxis =
      x.ofLp j + euclideanTimeShift t
    rw [Real.coe_toNNReal t ht, shift_eq]
    rfl
  constructor
  · rintro (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩)
    · obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hp
      exact ⟨Sum.inl j, rfl⟩
    · obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hp
      exact ⟨Sum.inr j, hcarry j⟩
  · rintro ⟨(j | j), rfl⟩
    · exact Or.inl ⟨v.val.get j, List.get_mem _ _, rfl⟩
    · exact Or.inr ⟨v.val.get j, List.get_mem _ _, hcarry j⟩

/-! ## 4. The energy gap for the constructed hierarchy -/

/-- Conditional on `UniformMixedClustering` (and `Properties`, which the public
witnesses satisfy). UNCOMPILED. -/
theorem constructed_hasEnergyGap_of_uniformMixedClustering (order : ℕ → ℕ)
    (hProps : (hierarchy F Q).Properties order)
    (hMix : (hierarchy F Q).UniformMixedClustering) :
    (hierarchy F Q).HasEnergyGap := by
  classical
  obtain ⟨L, hCompleted⟩ := EveryPhase.all_characters F
  have hAgree : (hierarchy F Q).PhasesAgreeOnSeparated :=
    Hierarchy.phaseCollapseObligation_holds (hierarchy F Q) order hProps
      (phasewiseDiagonal_hierarchy F Q) hMix
  obtain ⟨m, hm, hclust⟩ := hMix
  have hRm : MeasurableSet {p : E4 | 0 < p timeAxis ∧ p timeAxis < m / 2} :=
    (isOpen_lt continuous_const Mink.clock_cont).measurableSet.inter
      (isOpen_lt Mink.clock_cont continuous_const).measurableSet
  have hU := hCompleted.euclid F.α.atPoint
  have hB : (F.α.ensemble F.α.atPoint).Basic := (spectate F (some F.α.atPoint)).laws
  have hΩ : ‖(L.chambers F.α.atPoint).omega‖ = 1 :=
    show ‖(L.chambers F.α.atPoint).omega‖ = 1 from OS.nil_norm (L.chambers F.α.atPoint).GNS hB
  -- Step A: spectral exclusion for each OS generating vector
  have hvec : ∀ v : Future C.book timeAxis,
      (L.chambers F.α.atPoint).flow.ℚmeasure.diagonal ((L.chambers F.α.atPoint).GNS.plant v)
        {p : E4 | 0 < p timeAxis ∧ p timeAxis < m / 2} = 0 := by
    intro v
    obtain ⟨a, b, y, hsep, h1, hconj, hinj, hpair⟩ := internal_pair F Q v
    have hxinj : Injective (Word.positions v.val).ofLp := hsep
    have hyinj : Injective y := fun j k h =>
      Sum.inl_injective (hinj 0 le_rfl
        (show Sum.elim y (fun j => (Word.positions v.val).ofLp j + euclideanTimeShift 0) (Sum.inl j) =
          Sum.elim y (fun j => (Word.positions v.val).ofLp j + euclideanTimeShift 0) (Sum.inl k) from h))
    have hysep : WithLp.toLp 2 y ∈ WilsonFamily.separated v.val.length := by
      change Injective (WithLp.ofLp (WithLp.toLp 2 y)); exact hyinj
    -- clustering constants for this word
    obtain ⟨ηx, hηx, hsepx⟩ := Hierarchy.exists_pos_sep (Word.positions v.val).ofLp hxinj
    obtain ⟨ηy, hηy, hsepy⟩ := Hierarchy.exists_pos_sep y hyinj
    have hR0 : 0 ≤ (∑ j, ‖(Word.positions v.val).ofLp j‖) + ∑ j, ‖y j‖ :=
      add_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)
        (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    obtain ⟨K', t₁, _hK', _ht₁, hdecay⟩ :=
      hclust _ _ a b ((∑ j, ‖(Word.positions v.val).ofLp j‖) + ∑ j, ‖y j‖)
        (min ηx ηy) hR0 (lt_min hηx hηy)
    have hxR : ∀ j, ‖(Word.positions v.val).ofLp j‖ ≤
        (∑ j, ‖(Word.positions v.val).ofLp j‖) + ∑ j, ‖y j‖ := fun j =>
      le_add_of_le_of_nonneg (Hierarchy.norm_le_sum_norms _ j)
        (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    have hyR : ∀ j, ‖y j‖ ≤ (∑ j, ‖(Word.positions v.val).ofLp j‖) + ∑ j, ‖y j‖ := fun j =>
      le_add_of_nonneg_of_le (Finset.sum_nonneg fun _ _ => norm_nonneg _)
        (Hierarchy.norm_le_sum_norms _ j)
    have hxη : ∀ i j, i ≠ j → min ηx ηy ≤ ‖(Word.positions v.val).ofLp i - (Word.positions v.val).ofLp j‖ :=
      fun i j h => (min_le_left _ _).trans (hsepx i j h)
    have hyη : ∀ i j, i ≠ j → min ηx ηy ≤ ‖y i - y j‖ :=
      fun i j h => (min_le_right _ _).trans (hsepy i j h)
    -- zero-energy term, identified explicitly
    have horth : inner ℂ ((L.chambers F.α.atPoint).GNS.plant v)
        ((L.chambers F.α.atPoint).flow.orth ((L.chambers F.α.atPoint).GNS.plant v)) =
        star ((F.α.ensemble F.α.atPoint).expect v.val) * (F.α.ensemble F.α.atPoint).expect v.val := by
      rw [(L.chambers F.α.atPoint).orth_eq hU hΩ, inner_smul_right,
        (L.chambers F.α.atPoint).omega_pair, ← inner_conj_symm,
        (L.chambers F.α.atPoint).omega_pair, starRingEnd_apply, mul_comm]
    have hzero : (((L.chambers F.α.atPoint).flow.ℚmeasure.diagonal
          ((L.chambers F.α.atPoint).GNS.plant v)).real EveryPhase.zeroE : ℂ) =
        inner ℂ ((L.chambers F.α.atPoint).GNS.plant v)
          ((L.chambers F.α.atPoint).flow.orth ((L.chambers F.α.atPoint).GNS.plant v)) := by
      rw [EveryPhase.reflection_projection]
      exact (L.chambers F.α.atPoint).flow.ℚmeasure.at_pair EveryPhase.zeroE_m _
    -- the connected spectral integral is the mixed connected correlation
    have hconn : ∀ s : ℝ≥0,
        (((∫ p in EveryPhase.aboveE, EveryPhase.boltz s p ∂((L.chambers F.α.atPoint).flow.ℚmeasure.diagonal
            ((L.chambers F.α.atPoint).GNS.plant v))) : ℝ) : ℂ) =
          (hierarchy F Q).mixedConnected b y a (Word.positions v.val).ofLp s := by
      intro s
      have h2 : inner ℂ ((L.chambers F.α.atPoint).GNS.plant v)
          ((L.chambers F.α.atPoint).flow.E s ((L.chambers F.α.atPoint).GNS.plant v)) =
          (((L.chambers F.α.atPoint).flow.ℚmeasure.diagonal
              ((L.chambers F.α.atPoint).GNS.plant v)).real EveryPhase.zeroE : ℂ) +
            (((∫ p in EveryPhase.aboveE, EveryPhase.boltz s p ∂((L.chambers F.α.atPoint).flow.ℚmeasure.diagonal
              ((L.chambers F.α.atPoint).GNS.plant v))) : ℝ) : ℂ) := by
        rw [EveryPhase.boltzmann, EveryPhase.residual _ ((L.chambers F.α.atPoint).flow.bright _),
          Complex.ofReal_add]
      rw [hzero, horth, (L.chambers F.α.atPoint).pair_eq_gram v s] at h2
      have hpairS := hpair F.α.atPoint s (NNReal.coe_nonneg s)
      rw [Real.toNNReal_coe] at hpairS
      have hagreePair : (hierarchy F Q).phasePairAt (some F.α.atPoint) b y a
            (Word.positions v.val).ofLp s =
          (hierarchy F Q).phasePairAt none b y a (Word.positions v.val).ofLp s := by
        dsimp only [Hierarchy.phasePairAt, Hierarchy.grouped]
        exact hAgree _ _
          (Hierarchy.grouped_config_separated y _ (hinj s (NNReal.coe_nonneg s))) F.α.atPoint
      have he1 : (F.α.ensemble F.α.atPoint).expect v.val =
          (hierarchy F Q).correlation none a (Word.positions v.val) :=
        (h1 F.α.atPoint).symm.trans (hAgree a _ hsep F.α.atPoint)
      have he2 : star ((F.α.ensemble F.α.atPoint).expect v.val) =
          (hierarchy F Q).correlation none b (WithLp.toLp 2 y) := by
        rw [← hAgree b _ hysep F.α.atPoint, hconj F.α.atPoint, h1 F.α.atPoint, starRingEnd_apply]
      unfold Hierarchy.mixedConnected
      rw [← hagreePair, hpairS, h2, WithLp.toLp_ofLp, ← he1, ← he2]
      ring
    -- Laplace bound from clustering, then exclusion
    refine laplace_exclusion (K := K') _ ((L.chambers F.α.atPoint).flow.bright _) hm (max t₁ 0).toNNReal
      (fun s hs => ?_)
    have hts : t₁ ≤ (s : ℝ) :=
      le_trans (le_max_left _ _) (Real.toNNReal_le_iff_le_coe.mp hs)
    have hn : (∫ p in EveryPhase.aboveE, EveryPhase.boltz s p ∂((L.chambers F.α.atPoint).flow.ℚmeasure.diagonal
          ((L.chambers F.α.atPoint).GNS.plant v))) ≤
        ‖(((∫ p in EveryPhase.aboveE, EveryPhase.boltz s p ∂((L.chambers F.α.atPoint).flow.ℚmeasure.diagonal
          ((L.chambers F.α.atPoint).GNS.plant v))) : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact le_abs_self _
    rw [hconn s] at hn
    exact hn.trans (hdecay (Word.positions v.val).ofLp y s hxR hyR hxη hyη hts)
  -- Step B: the OS spectral projection vanishes (dense span of generating vectors)
  have hOS : (L.chambers F.α.atPoint).flow.ℚmeasure.region
      {p : E4 | 0 < p timeAxis ∧ p timeAxis < m / 2} = 0 :=
    clm_eq_zero_of_dense _ (L.chambers F.α.atPoint).GNS.plant (L.chambers F.α.atPoint).GNS.dense
      (fun v => ((L.chambers F.α.atPoint).flow.ℚmeasure.null_pair hRm _).mp (hvec v))
  -- Step C: transport to the selected Wightman space
  have hW : (L.actors F.α.atPoint).momentum.region
      {p : E4 | 0 < p timeAxis ∧ p timeAxis < m / 2} = 0 := by
    ext1 z
    have hJ := (L.links F.α.atPoint).projections (L.cores F.α.atPoint) _ hRm z
    rw [hOS] at hJ
    have hnorm := (L.links F.α.atPoint).acts.scale
      ((L.actors F.α.atPoint).momentum.region {p : E4 | 0 < p timeAxis ∧ p timeAxis < m / 2} z)
    rw [hJ] at hnorm
    simpa using hnorm.symm
  -- Step D: the selected phase is the public theory
  rw [L.baseR] at hW
  unfold Hierarchy.HasEnergyGap WightmanTheory.HasEnergyGap
  exact ⟨m / 2, half_pos hm, hW⟩

/-- `SpectralEnergyObligation`, discharged for the constructed hierarchy. -/
theorem constructed_spectralEnergyObligation (order : ℕ → ℕ) :
    (hierarchy F Q).SpectralEnergyObligation order :=
  fun hProps _ hMix => constructed_hasEnergyGap_of_uniformMixedClustering F Q order hProps hMix

end Reverse

end YangMills

/-- The public existence theorem, strengthened: for the same witnesses,
uniform mixed clustering implies phase agreement and an energy gap. -/
theorem YangMills.jointExistence_with_conditional_energyGap :
    ∀ g : YangMills.GaugeGroup, g.IsSimple →
      ∃ C : YangMills.WilsonFamily g, YangMills.WilsonRegularity C ∧
        ∀ p : ℕ → ℕ, StrictMono p →
          ∃ q : ℕ → ℕ, StrictMono q ∧
            ∃ T : YangMills.Hierarchy C, T.Properties (p ∘ q) ∧
              (T.UniformMixedClustering → T.PhasesAgreeOnSeparated ∧ T.HasEnergyGap) := by
  intro g hg
  obtain ⟨C, _, _, reg, orders⟩ := YangMills.constructed.{0,0} g hg 1 zero_lt_one
  refine ⟨YangMills.wilsonFamily C, reg, fun p hp => ?_⟩
  let a : YM.Extraction.Order := ⟨.full, ⟨p, hp⟩⟩
  obtain ⟨q, S, F, L, Q, M, X, core, _⟩ := orders a
  exact ⟨q.per, q.per.monotone, YangMills.hierarchy F Q, core, fun hMix =>
    ⟨YangMills.Hierarchy.phaseCollapseObligation_holds (YangMills.hierarchy F Q) _ core
        (YangMills.phasewiseDiagonal_hierarchy F Q) hMix,
      YangMills.constructed_hasEnergyGap_of_uniformMixedClustering F Q _ core hMix⟩⟩

#check @YangMills.constructed_hasEnergyGap_of_uniformMixedClustering
#check @YangMills.jointExistence_with_conditional_energyGap
#print axioms YangMills.laplace_exclusion
#print axioms YangMills.clm_eq_zero_of_dense
#print axioms YangMills.internal_pair
#print axioms YangMills.constructed_hasEnergyGap_of_uniformMixedClustering
#print axioms YangMills.constructed_spectralEnergyObligation
#print axioms YangMills.jointExistence_with_conditional_energyGap
