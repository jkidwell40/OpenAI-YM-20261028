import ChallengeSpec

/-!
# Conditional Yang--Mills mass-gap bridge, version 3

RESEARCH SPECIFICATION; NOT A MASS-GAP PROOF.

The file uses the public `ChallengeSpec` interface and defines its own
energy-gap and invariant-mass-gap predicates.  It does not import the earlier
`MassGapTargets.lean`, which already defines some of the same names.

Proof terms supplied (ALL UNCOMPILED, NOT KERNEL-CHECKED):
`bridge_of_obligations`, `phasesAgree_of_varianceZero`, and (new in v4)
`diagonalToVariance` and `phaseCollapseObligation_holds`.
v4 also fixes: `x.ofLp` in `PhasewiseDiagonal`; integrability in
`continuous_const_of_integral_sq_norm_sub_eq_zero`.
What is NOT proved: the one-scale defect, finite-transfer estimates,
phasewise RP-to-diagonal derivation, spectral clustering-to-energy-gap,
or energy-gap-to-invariant-mass-gap covariance lemma.

The PhasewiseDiagonal structure below describes the *consequences* that the
internal phasewise reflection-positive reconstruction would have to supply.
In particular, it DOES NOT assert that they follow from the exported
`Hierarchy.Reconstructed` field (which only supplies Wightman axioms for
`T.selected`).  Its uniform diagonal-kernel bound must be justified from
reflection positivity plus continuity on the compact character space.

Compilation has not been performed.
-/

set_option autoImplicit false
noncomputable section

namespace YangMills
open MeasureTheory Filter

/-! ## Distinguish the energy gap from invariant mass -/

namespace WightmanTheory
variable {H : HilbertSpace} {Labels : FieldLabels}

/-- Spectral energy gap above the zero-energy vacuum.  A W0 spectrum condition
and uniqueness of the vacuum identify the rest of the allowed spectrum. -/
def HasEnergyGap (W : WightmanTheory H Labels) : Prop :=
  ∃ delta : ℝ, 0 < delta ∧
    W.energyMomentum.projection
      {p : Spacetime | 0 < time p ∧ time p < delta} = 0

/-- Gap in invariant mass, including lightlike nonzero momenta in the region
of forbidden spectrum.  An energy gap does not imply this just by a subset
argument; covariance of the *joint spectral measure* is essential. -/
def HasMassGap (W : WightmanTheory H Labels) : Prop :=
  ∃ delta : ℝ, 0 < delta ∧
    W.energyMomentum.projection
      {p : Spacetime | 0 < time p ∧ minkowskiSquare p < delta ^ 2} = 0

end WightmanTheory

/-! ## Finite-lattice hypothesis at the coupling of each target volume -/

/-- Unnormalized Wilson partition function at the *fixed* coupling
`C.beta N p`.  This is an extra definition: `WilsonFamily` exposes normalized
expectations, but no partition function. -/
def wilsonPartition {g : GaugeGroup} (C : WilsonFamily g)
    (N p : ℕ) (l : ℕ+) : ℝ :=
  let prior : Measure (Configuration g l) := Measure.pi (fun _ => C.haar)
  ∫ U, Real.exp (-(C.beta N p) * wilsonEnergy U) ∂prior

/-- Four-dimensional box defect. Both partition functions use the coupling
of the target volume index `p`, not independently retuned couplings. -/
def wilsonDefect {g : GaugeGroup} (C : WilsonFamily g)
    (N p : ℕ) (l : ℕ+) : ℝ :=
  16 * Real.log (wilsonPartition C N p l) -
    Real.log (wilsonPartition C N p (2 * l))

/-- (H): Every target volume in the *chosen* extraction order is a dyadic
multiple of one fixed physical reference period.  The defect at that base
period is uniformly small in cutoff and target-volume index, evaluated at
each target's own bare coupling.  This is NOT inferred from `JointExistence`.

There is no reliance on the hidden `Waits.lean` witness calendar and no
assumption that `C.beta N (order k)` is constant in `k`. -/
def OneScaleDefectBound {g : GaugeGroup} (C : WilsonFamily g)
    (order : ℕ → ℕ) : Prop :=
  ∃ base : ℕ+,
    (∀ k : ℕ, ∃ j : ℕ,
      C.period (order k) = base * (2 : ℕ+) ^ j) ∧
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ k : ℕ,
      let l : ℕ+ := base * C.denominator N
      0 < wilsonPartition C N (order k) l ∧
      0 < wilsonPartition C N (order k) (2 * l) ∧
      wilsonDefect C N (order k) l ≤ (1 / 4096 : ℝ)

/-- Shift all Euclidean points by `t` along the public interface's time axis. -/
def euclideanTimeShift (t : ℝ) : Spacetime :=
  WithLp.toLp 2 (fun i : Axis => if i = timeAxis then t else 0)

namespace Hierarchy
variable {g : GaugeGroup} {C : WilsonFamily g}

/-- The gap statements refer to the theory reconstructed from `T.selected`,
not to an abstract free theory or automatically to the phase mixture. -/
def HasEnergyGap (T : Hierarchy C) : Prop :=
  T.theory.HasEnergyGap

def HasMassGap (T : Hierarchy C) : Prop :=
  T.theory.HasMassGap

/-- An arbitrary phase's two-word correlation at Euclidean time displacement
`t`.  Labels `b` and locations `y` represent a reflected/adjoint word only
when the PhasewiseDiagonal hypothesis below supplies that identification. -/
def phasePairAt (T : Hierarchy C) (s : Option T.Character)
    {n m : ℕ} (b : Fin m → T.Tag) (y : Fin m → Spacetime)
    (a : Fin n → T.Tag) (x : Fin n → Spacetime) (t : ℝ) : ℂ :=
  T.grouped s b y a (fun j => x j + euclideanTimeShift t)

/-- Mixed connected correlation, with translation-invariant centering.
The centering is legitimate only after translation invariance is supplied. -/
def mixedConnected (T : Hierarchy C)
    {n m : ℕ} (b : Fin m → T.Tag) (y : Fin m → Spacetime)
    (a : Fin n → T.Tag) (x : Fin n → Spacetime) (t : ℝ) : ℂ :=
  T.phasePairAt none b y a x t -
    T.correlation none b (WithLp.toLp 2 y) *
    T.correlation none a (WithLp.toLp 2 x)

/-- The output required of the lattice-to-continuum step.  A common positive
rate and locally uniform constants are necessary; pointwise clustering alone
will NOT imply a gap. -/
def UniformMixedClustering (T : Hierarchy C) : Prop :=
  ∃ mass : ℝ, 0 < mass ∧
    ∀ (n m : ℕ) (a : Fin n → T.Tag) (b : Fin m → T.Tag)
      (R eta : ℝ), 0 ≤ R → 0 < eta →
      ∃ K t₀ : ℝ, 0 ≤ K ∧ 0 ≤ t₀ ∧
        ∀ (x : Fin n → Spacetime) (y : Fin m → Spacetime) (t : ℝ),
          (∀ i, ‖x i‖ ≤ R) →
          (∀ j, ‖y j‖ ≤ R) →
          (∀ i j, i ≠ j → eta ≤ ‖x i - x j‖) →
          (∀ i j, i ≠ j → eta ≤ ‖y i - y j‖) →
          t₀ ≤ t →
          ‖T.mixedConnected b y a x t‖ ≤ K * Real.exp (-mass * t)

/-! ## Minimal phase-diagonal consequence of OS reconstruction

`PhasewiseDiagonal` is deliberately *not* assumed to follow from the public
`Reconstructed` field. One must establish it from the internal phasewise
reflection-positivity/translation-semigroup/unique-vacuum construction.

For each separated word F this asks for a reflected companion F*, a time
threshold after which both blocks are separated, a uniform-in-character
bound on the diagonal kernel and its pointwise limit |E_xi F|^2.

Positivity and monotonicity are NOT fields here: they are candidate tools for
proving this structure from phasewise RP, not needed by Step 4 itself.
-/
structure PhasewiseDiagonal (T : Hierarchy C) : Prop where
  diagonal :
    ∀ {n : ℕ} (a : Fin n → T.Tag) (x : Points n),
      x ∈ WilsonFamily.separated n →
      ∃ (b : Fin n → T.Tag) (y : Fin n → Spacetime)
        (t₀ K : ℝ),
        0 ≤ t₀ ∧ 0 ≤ K ∧
        (∀ ξ : T.Character,
          T.correlation (some ξ) b (WithLp.toLp 2 y) =
            (starRingEnd ℂ) (T.correlation (some ξ) a x)) ∧
        (∀ t : ℝ, t₀ ≤ t →
          Function.Injective
            (Sum.elim y (fun j : Fin n => x.ofLp j + euclideanTimeShift t))) ∧
        (∀ (ξ : T.Character) (t : ℝ), t₀ ≤ t →
          ‖T.phasePairAt (some ξ) b y a x.ofLp t‖ ≤ K) ∧
        (∀ ξ : T.Character,
          Filter.Tendsto
            (fun t : ℝ => T.phasePairAt (some ξ) b y a x.ofLp t)
            Filter.atTop
            (nhds ((starRingEnd ℂ) (T.correlation (some ξ) a x) *
              T.correlation (some ξ) a x)))

/-- Source-side prerequisite to show, NOT a proved theorem.  Explicitly
separate the reflection-positivity-to-diagonal argument from the variance
argument below.  A genuine `PhasewiseRP` model requires the internal phase
OS Hilbert spaces, which the public interface does not export. -/
def PhasewiseRPToDiagonalObligation
    (T : Hierarchy C) (PhasewiseRP : Prop) : Prop :=
  PhasewiseRP → T.PhasewiseDiagonal

/-- The wanted conclusion: equality of all phase correlations at every
separated configuration, including `T.selected`.  Pointwise equality is later
extended to smeared fields using `Reconstructed.smooth` and continuity. -/
def PhasesAgreeOnSeparated (T : Hierarchy C) : Prop :=
  ∀ {n : ℕ} (a : Fin n → T.Tag) (x : Points n),
    x ∈ WilsonFamily.separated n →
    ∀ ξ : T.Character,
      T.correlation (some ξ) a x = T.correlation none a x

/-! ## Step 4: variance collapse

The analytic part is the following `DiagonalToVarianceObligation`:

(1) For a fixed separated word, use the diagonal kernel's `K` and pointwise
    phase-vacuum limit to pass the t → ∞ limit through the phase integral.
(2) Use `Reconstructed.mixture` for the doubled separated configuration and
    each one-word expectation.
(3) Apply `UniformMixedClustering` to the reflected word with an appropriate
    radius R and separation eta. All finite configurations have such R, eta.
(4) Use complex conjugation and probability normalization to derive

    ∫ ‖a(xi) - ∫a‖² dnu = 0.

These steps require real DCT, geometry and integral-algebra proofs and are
NOT covertly introduced as axioms or declared as proved.
-/

def PhaseVarianceZero (T : Hierarchy C) : Prop :=
  ∀ {n : ℕ} (a : Fin n → T.Tag) (x : Points n),
    x ∈ WilsonFamily.separated n →
      (∫ ξ : T.Character,
        ‖T.correlation (some ξ) a x - T.correlation none a x‖ ^ 2
        ∂T.phaseMeasure) = 0

/-- Specific analytic bridge from diagonal kernels to the zero-variance
identity, not yet established. Does not simply assume phase agreement. -/
def DiagonalToVarianceObligation
    (T : Hierarchy C) (order : ℕ → ℕ) : Prop :=
  T.Properties order → T.PhasewiseDiagonal →
    T.UniformMixedClustering → T.PhaseVarianceZero

/-- Independently meaningful measure-theoretic lemma. If a continuous
complex function has zero integrated squared deviation from `c` under a
full-support finite measure, it is identically `c`.

The proof uses Mathlib's `integral_eq_zero_iff_of_nonneg` and
`Measure.eq_of_ae_eq`.  It has no `sorry` but is UNCOMPILED here. -/
theorem continuous_const_of_integral_sq_norm_sub_eq_zero
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] [CompactSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
    (f : X → ℂ) (c : ℂ) (hf : Continuous f)
    (hZero : (∫ x, ‖f x - c‖ ^ 2 ∂μ) = 0) :
    ∀ x, f x = c := by
  have hg : Continuous (fun x : X => ‖f x - c‖ ^ 2) :=
    ((hf.sub continuous_const).norm).pow 2
  have hi : Integrable (fun x : X => ‖f x - c‖ ^ 2) μ :=
    -- v4 fix: no `Continuous.integrable`; use compact support of the whole space.
    hg.integrable_of_hasCompactSupport
      (IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport _)
        (Set.subset_univ _))
  have hAE : (fun x : X => ‖f x - c‖ ^ 2) =ᵐ[μ]
      (fun _ => (0 : ℝ)) :=
    (integral_eq_zero_iff_of_nonneg
      (fun x => sq_nonneg (‖f x - c‖)) hi).mp hZero
  have hall : (fun x : X => ‖f x - c‖ ^ 2) =
      (fun _ => (0 : ℝ)) :=
    MeasureTheory.Measure.eq_of_ae_eq (μ := μ) hAE hg continuous_const
  intro x
  have hz : ‖f x - c‖ ^ 2 = 0 := congrFun hall x
  have hn : ‖f x - c‖ = 0 := by
    nlinarith [norm_nonneg (f x - c)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

/-- The final Step-4 algebra/topology theorem: zero variance for every word
forces equality for every phase, including `T.selected`. -/
theorem phasesAgree_of_varianceZero
    (T : Hierarchy C) (order : ℕ → ℕ)
    (hProps : T.Properties order)
    (hZero : T.PhaseVarianceZero) :
    T.PhasesAgreeOnSeparated := by
  classical
  intro n a x hx ξ
  letI : IsProbabilityMeasure T.phaseMeasure :=
    hProps.reconstruction.normalized
  letI : T.phaseMeasure.IsOpenPosMeasure :=
    hProps.reconstruction.fullSupport
  have hf : Continuous (fun η : T.Character =>
      T.correlation (some η) a x) :=
    hProps.reconstruction.characterContinuity a x hx
  exact continuous_const_of_integral_sq_norm_sub_eq_zero
    T.phaseMeasure (fun η : T.Character => T.correlation (some η) a x)
    (T.correlation none a x) hf (hZero a x hx) ξ

/-- Composition of the analytic diagonal-to-variance obligation with the
proved-candidate variance-to-agreement lemma. The analytic obligation has
NOT been established; supplying it is the actual Step-4 work. -/
theorem phaseCollapse_of_diagonal
    (T : Hierarchy C) (order : ℕ → ℕ)
    (hDiagonalToVariance : T.DiagonalToVarianceObligation order)
    (hProps : T.Properties order)
    (hDiag : T.PhasewiseDiagonal)
    (hMix : T.UniformMixedClustering) :
    T.PhasesAgreeOnSeparated := by
  exact T.phasesAgree_of_varianceZero order hProps
    (hDiagonalToVariance hProps hDiag hMix)

/-- Step 4 as a named proposition in the overall bridge statement. -/
def PhaseCollapseObligation (T : Hierarchy C) (order : ℕ → ℕ) : Prop :=
  T.Properties order → T.PhasewiseDiagonal →
    T.UniformMixedClustering → T.PhasesAgreeOnSeparated

/-! ## v4: proof of `DiagonalToVarianceObligation`

STATUS: UNCOMPILED PROOF TERMS. Not kernel-checked. Uses exactly
`T.Properties order`, `PhasewiseDiagonal`, and `UniformMixedClustering`;
no further hypotheses are introduced.

Organization (as agreed):
* Geometry: positive minimum separation of finite injective families
  (empty and one-point families take `η = 1`); norm bound by a sum; the
  configuration read by `grouped` is separated.
* Reconstruction plumbing: mixture identity, continuity and integrability for
  `grouped` words.
* Analysis, along the discrete times `u k = max t₀ t₁ + k`:
    (I)  `∫ conj(a ξ) * a ξ dν = conj c * c`   (dominated convergence + clustering),
    (II) `∫ ‖a ξ - c‖² dν = 0`                 (integral algebra).

Mathlib names flagged as most likely to need adjustment at elaboration:
`Complex.conj_mul'`, `integral_ofReal`, `integral_conj`,
`Filter.tendsto_atTop_add_const_left`, `WithLp.toLp_ofLp`.
-/

section Step4Geometry

/-- A finite injective family has a positive minimum pairwise distance.
Families with fewer than two points have no distinct pairs; take `η = 1`. -/
theorem exists_pos_sep {E : Type*} [NormedAddCommGroup E] {n : ℕ}
    (f : Fin n → E) (hf : Function.Injective f) :
    ∃ η : ℝ, 0 < η ∧ ∀ i j, i ≠ j → η ≤ ‖f i - f j‖ := by
  classical
  let D : Finset ℝ :=
    (Finset.univ : Finset (Fin n)).offDiag.image
      (fun p : Fin n × Fin n => ‖f p.1 - f p.2‖)
  have hmem : ∀ i j, i ≠ j → ‖f i - f j‖ ∈ D := fun i j hij =>
    Finset.mem_image.mpr ⟨(i, j),
      Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _, hij⟩, rfl⟩
  by_cases hD : D.Nonempty
  · refine ⟨D.min' hD, ?_, fun i j hij => D.min'_le _ (hmem i j hij)⟩
    obtain ⟨p, hp, hpe⟩ := Finset.mem_image.mp (D.min'_mem hD)
    rw [← hpe]
    obtain ⟨-, -, hne⟩ := Finset.mem_offDiag.mp hp
    exact norm_pos_iff.mpr (sub_ne_zero.mpr fun h => hne (hf h))
  · exact ⟨1, one_pos, fun i j hij => absurd ⟨_, hmem i j hij⟩ hD⟩

theorem norm_le_sum_norms {E : Type*} [NormedAddCommGroup E] {n : ℕ}
    (f : Fin n → E) (i : Fin n) : ‖f i‖ ≤ ∑ j, ‖f j‖ :=
  Finset.single_le_sum (f := fun j => ‖f j‖)
    (fun j _ => norm_nonneg _) (Finset.mem_univ i)

/-- The point list actually read by `grouped` is separated whenever the
concatenation is injective: `grouped` only reorders by an equivalence. -/
theorem grouped_config_separated {m n : ℕ}
    (y : Fin m → Spacetime) (x : Fin n → Spacetime)
    (h : Function.Injective (Sum.elim y x)) :
    WithLp.toLp 2 ((Sum.elim y x) ∘ (Fintype.equivFin (Fin m ⊕ Fin n)).symm) ∈
      WilsonFamily.separated (Fintype.card (Fin m ⊕ Fin n)) := by
  change Function.Injective
    (WithLp.ofLp (WithLp.toLp 2
      ((Sum.elim y x) ∘ (Fintype.equivFin (Fin m ⊕ Fin n)).symm)))
  exact h.comp (Fintype.equivFin (Fin m ⊕ Fin n)).symm.injective

end Step4Geometry

section Step4Plumbing

theorem grouped_mixture (T : Hierarchy C) {order : ℕ → ℕ}
    (hP : T.Properties order) {m n : ℕ}
    (b : Fin m → T.Tag) (y : Fin m → Spacetime)
    (a : Fin n → T.Tag) (x : Fin n → Spacetime)
    (h : Function.Injective (Sum.elim y x)) :
    (∫ ξ, T.grouped (some ξ) b y a x ∂T.phaseMeasure) =
      T.grouped none b y a x := by
  dsimp only [Hierarchy.grouped]
  exact hP.reconstruction.mixture _ _ (grouped_config_separated y x h)

theorem grouped_continuous (T : Hierarchy C) {order : ℕ → ℕ}
    (hP : T.Properties order) {m n : ℕ}
    (b : Fin m → T.Tag) (y : Fin m → Spacetime)
    (a : Fin n → T.Tag) (x : Fin n → Spacetime)
    (h : Function.Injective (Sum.elim y x)) :
    Continuous (fun ξ : T.Character => T.grouped (some ξ) b y a x) := by
  dsimp only [Hierarchy.grouped]
  exact hP.reconstruction.characterContinuity _ _ (grouped_config_separated y x h)

theorem integrable_of_continuous_character (T : Hierarchy C)
    {order : ℕ → ℕ} (hP : T.Properties order)
    {f : T.Character → ℂ} (hf : Continuous f) :
    Integrable f T.phaseMeasure := by
  haveI : IsProbabilityMeasure T.phaseMeasure := hP.reconstruction.normalized
  exact hf.integrable_of_hasCompactSupport
    (IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport f)
      (Set.subset_univ _))

end Step4Plumbing

open ComplexConjugate in
/-- Step 4 analytic core (UNCOMPILED). -/
theorem diagonalToVariance (T : Hierarchy C) (order : ℕ → ℕ) :
    T.DiagonalToVarianceObligation order := by
  classical
  intro hP hDiag hMix n a x hx
  haveI : IsProbabilityMeasure T.phaseMeasure := hP.reconstruction.normalized
  have hxinj : Function.Injective x.ofLp := hx
  obtain ⟨b, y, t₀, K, _ht₀, _hK, hconj, hinj, hbound, hlim⟩ :=
    hDiag.diagonal a x hx
  set c : ℂ := T.correlation none a x with hc
  -- one-word data
  let f : T.Character → ℂ := fun ξ => T.correlation (some ξ) a x
  have hfc : Continuous f := hP.reconstruction.characterContinuity a x hx
  have hfI : Integrable f T.phaseMeasure :=
    T.integrable_of_continuous_character hP hfc
  have hgI : Integrable (fun ξ => conj (f ξ)) T.phaseMeasure :=
    T.integrable_of_continuous_character hP (Complex.continuous_conj.comp hfc)
  have hhI : Integrable (fun ξ => conj (f ξ) * f ξ) T.phaseMeasure :=
    T.integrable_of_continuous_character hP
      ((Complex.continuous_conj.comp hfc).mul hfc)
  have h1 : ∫ ξ, f ξ ∂T.phaseMeasure = c := hP.reconstruction.mixture a x hx
  have h2 : ∫ ξ, conj (f ξ) ∂T.phaseMeasure = conj c := by
    rw [integral_conj, h1]
  -- the reflected word is separated and has expectation conj c
  have hyinj : Function.Injective y := by
    intro i j h
    exact Sum.inl_injective (hinj t₀ le_rfl (by simp only [Sum.elim_inl]; exact h))
  have hysep : WithLp.toLp 2 y ∈ WilsonFamily.separated n := by
    change Function.Injective (WithLp.ofLp (WithLp.toLp 2 y)); exact hyinj
  have hb : T.correlation none b (WithLp.toLp 2 y) = conj c := by
    rw [← hP.reconstruction.mixture b (WithLp.toLp 2 y) hysep, ← h2]
    exact integral_congr_ae (Filter.Eventually.of_forall hconj)
  -- clustering constants
  obtain ⟨mass, hmass, hclust⟩ := hMix
  obtain ⟨ηx, hηx, hsepx⟩ := exists_pos_sep x.ofLp hxinj
  obtain ⟨ηy, hηy, hsepy⟩ := exists_pos_sep y hyinj
  set R : ℝ := (∑ i, ‖x.ofLp i‖) + ∑ j, ‖y j‖ with hR
  have hR0 : 0 ≤ R := add_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  obtain ⟨K', t₁, _hK', _ht₁, hdecay⟩ :=
    hclust n n a b R (min ηx ηy) hR0 (lt_min hηx hηy)
  have hxR : ∀ i, ‖x.ofLp i‖ ≤ R := fun i =>
    le_add_of_le_of_nonneg (norm_le_sum_norms _ i)
      (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  have hyR : ∀ j, ‖y j‖ ≤ R := fun j =>
    le_add_of_nonneg_of_le (Finset.sum_nonneg fun _ _ => norm_nonneg _)
      (norm_le_sum_norms _ j)
  have hxη : ∀ i j, i ≠ j → min ηx ηy ≤ ‖x.ofLp i - x.ofLp j‖ :=
    fun i j h => (min_le_left _ _).trans (hsepx i j h)
  have hyη : ∀ i j, i ≠ j → min ηx ηy ≤ ‖y i - y j‖ :=
    fun i j h => (min_le_right _ _).trans (hsepy i j h)
  -- discrete times
  let u : ℕ → ℝ := fun k => max t₀ t₁ + k
  have hu : Filter.Tendsto u Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
  have hu₀ : ∀ k, t₀ ≤ u k := fun k =>
    (le_max_left _ _).trans (le_add_of_nonneg_right (Nat.cast_nonneg k))
  have hu₁ : ∀ k, t₁ ≤ u k := fun k =>
    (le_max_right _ _).trans (le_add_of_nonneg_right (Nat.cast_nonneg k))
  -- (I.a) mixed connected correlation → 0
  have hdec : Filter.Tendsto (fun k => K' * Real.exp (-mass * u k))
      Filter.atTop (nhds 0) := by
    have h3 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (hu.const_mul_atTop hmass)).const_mul K'
    simpa [Function.comp, neg_mul] using h3
  have hconn : Filter.Tendsto
      (fun k => T.mixedConnected b y a x.ofLp (u k)) Filter.atTop (nhds 0) :=
    squeeze_zero_norm
      (fun k => hdecay x.ofLp y (u k) hxR hyR hxη hyη (hu₁ k)) hdec
  -- (I.b) mixed pair → conj c * c
  have hpairNone : Filter.Tendsto
      (fun k => T.phasePairAt none b y a x.ofLp (u k))
      Filter.atTop (nhds (conj c * c)) := by
    have hconst : Filter.Tendsto (fun _ : ℕ =>
        T.correlation none b (WithLp.toLp 2 y) *
          T.correlation none a (WithLp.toLp 2 x.ofLp)) Filter.atTop
        (nhds (T.correlation none b (WithLp.toLp 2 y) *
          T.correlation none a (WithLp.toLp 2 x.ofLp))) := tendsto_const_nhds
    have hsum := hconn.add hconst
    rw [hb, WithLp.toLp_ofLp, zero_add] at hsum
    refine hsum.congr fun k => ?_
    simp only [Hierarchy.mixedConnected, hb, WithLp.toLp_ofLp, ← hc, sub_add_cancel]
  -- (I.c) mixture of the pair at each discrete time
  have hpairInt : ∀ k,
      (∫ ξ, T.phasePairAt (some ξ) b y a x.ofLp (u k) ∂T.phaseMeasure) =
        T.phasePairAt none b y a x.ofLp (u k) := fun k => by
    unfold Hierarchy.phasePairAt
    exact T.grouped_mixture hP b y a _ (hinj (u k) (hu₀ k))
  -- (I.d) dominated convergence over phases
  have hDCT : Filter.Tendsto
      (fun k => ∫ ξ, T.phasePairAt (some ξ) b y a x.ofLp (u k) ∂T.phaseMeasure)
      Filter.atTop (nhds (∫ ξ, conj (f ξ) * f ξ ∂T.phaseMeasure)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => K)
      (fun k => ?_) (integrable_const K)
      (fun k => Filter.Eventually.of_forall fun ξ => hbound ξ (u k) (hu₀ k))
      (Filter.Eventually.of_forall fun ξ => (hlim ξ).comp hu)
    have hcont := T.grouped_continuous hP b y a _ (hinj (u k) (hu₀ k))
    exact hcont.aestronglyMeasurable
  -- (I) the substantive identity
  have h3 : ∫ ξ, conj (f ξ) * f ξ ∂T.phaseMeasure = conj c * c :=
    tendsto_nhds_unique hDCT (hpairNone.congr fun k => (hpairInt k).symm)
  -- (II) integral algebra
  have hexp : (fun ξ => ((‖f ξ - c‖ ^ 2 : ℝ) : ℂ)) =
      fun ξ => (conj (f ξ) * f ξ - conj c * f ξ) - (conj (f ξ) * c - conj c * c) := by
    funext ξ
    rw [Complex.ofReal_pow, ← Complex.conj_mul', map_sub]
    ring
  have hI : ∫ ξ, ((‖f ξ - c‖ ^ 2 : ℝ) : ℂ) ∂T.phaseMeasure = 0 := by
    rw [hexp,
      integral_sub (hhI.sub (hfI.const_mul _)) ((hgI.mul_const _).sub (integrable_const _)),
      integral_sub hhI (hfI.const_mul _),
      integral_sub (hgI.mul_const _) (integrable_const _),
      integral_const_mul, integral_mul_const, integral_const, h1, h2, h3]
    simp
  have hC : ((∫ ξ, ‖f ξ - c‖ ^ 2 ∂T.phaseMeasure : ℝ) : ℂ) = 0 := by
    rw [← integral_ofReal]; exact hI
  exact_mod_cast hC

/-- Step 4, conditional only on `PhasewiseDiagonal` (UNCOMPILED). With
`diagonalToVariance` and `phasesAgree_of_varianceZero`, the named obligation
`PhaseCollapseObligation` is discharged; what remains of Step 4 is
`PhasewiseRPToDiagonalObligation`. -/
theorem phaseCollapseObligation_holds (T : Hierarchy C) (order : ℕ → ℕ) :
    T.PhaseCollapseObligation order :=
  fun hP hDiag hMix =>
    T.phaseCollapse_of_diagonal order (T.diagonalToVariance order) hP hDiag hMix

/-- Step 5a: show a common exponential rate on a dense cyclic field domain
forces a *positive energy gap* in the selected reconstructed Hilbert space. -/
def SpectralEnergyObligation (T : Hierarchy C) (order : ℕ → ℕ) : Prop :=
  T.Properties order → T.PhasesAgreeOnSeparated →
    T.UniformMixedClustering → T.HasEnergyGap

/-- Step 5b (separate boost lemma): energy gap + W0 spectrum condition +
Lorentz covariance of the JOINT spectral measure excludes all nonvacuum
momenta with invariant mass less than the same positive threshold.
This cannot be proven merely by treating one forbidden set as a subset of
another: large-energy near-lightlike momenta require boosts. -/
def EnergyGapToMassGapObligation (T : Hierarchy C) (order : ℕ → ℕ) : Prop :=
  T.Properties order → T.HasEnergyGap → T.HasMassGap

end Hierarchy

/-! ## External lattice-analysis obligations, kept conspicuously explicit -/

/-- Operator-norm smoothing (A) and thermal-to-vacuum comparison (B) are
uninterpreted proposition parameters pending the transfer-matrix interface.
The proof of this implication is the unresolved lattice/continuum analysis. -/
def LatticeToMixedClusteringObligation
    {g : GaugeGroup} {C : WilsonFamily g}
    (order : ℕ → ℕ) (T : Hierarchy C)
    (A_UniformSmoothedOperatorBounds B_ThermalVacuumComparison : Prop) : Prop :=
  OneScaleDefectBound C order →
    A_UniformSmoothedOperatorBounds →
    B_ThermalVacuumComparison →
    T.Properties order → T.UniformMixedClustering

/-- Pure logic: given the four genuine analytic theorem obligations,
assemble the desired conclusion.  This is NOT a proof of any obligation. -/
theorem bridge_of_obligations
    {g : GaugeGroup} {C : WilsonFamily g}
    {order : ℕ → ℕ} (T : Hierarchy C)
    (A_UniformSmoothedOperatorBounds B_ThermalVacuumComparison : Prop)
    (hStep3 : LatticeToMixedClusteringObligation order T
      A_UniformSmoothedOperatorBounds B_ThermalVacuumComparison)
    (hStep4 : T.PhaseCollapseObligation order)
    (hStep5Energy : T.SpectralEnergyObligation order)
    (hBoost : T.EnergyGapToMassGapObligation order)
    (hOS : T.PhasewiseDiagonal)
    (hH : OneScaleDefectBound C order)
    (hA : A_UniformSmoothedOperatorBounds)
    (hB : B_ThermalVacuumComparison)
    (hProps : T.Properties order) : T.HasMassGap := by
  have hMix : T.UniformMixedClustering := hStep3 hH hA hB hProps
  have hAgree : T.PhasesAgreeOnSeparated := hStep4 hProps hOS hMix
  have hEnergy : T.HasEnergyGap := hStep5Energy hProps hAgree hMix
  exact hBoost hProps hEnergy

/-- Weaker existence objective: for each simple group, SOME strictly
increasing extraction order supports a constructed gapped hierarchy.
No claim about all orders or phases, and no existence theorem is proved. -/
def SomeExtractionWithGap : Prop :=
  ∀ g : GaugeGroup, g.IsSimple →
    ∃ C : WilsonFamily g, WilsonRegularity C ∧
      ∃ order : ℕ → ℕ, StrictMono order ∧
        ∃ T : Hierarchy C, T.Properties order ∧ T.HasMassGap

#check WightmanTheory.HasEnergyGap
#check WightmanTheory.HasMassGap
#check Hierarchy.HasEnergyGap
#check Hierarchy.HasMassGap
#check OneScaleDefectBound
#check Hierarchy.PhasewiseDiagonal
#check Hierarchy.PhaseVarianceZero
#check Hierarchy.DiagonalToVarianceObligation
#check Hierarchy.continuous_const_of_integral_sq_norm_sub_eq_zero
#check Hierarchy.phasesAgree_of_varianceZero
#check Hierarchy.phaseCollapse_of_diagonal
#check Hierarchy.diagonalToVariance
#check Hierarchy.phaseCollapseObligation_holds
#check Hierarchy.PhaseCollapseObligation
#check Hierarchy.SpectralEnergyObligation
#check Hierarchy.EnergyGapToMassGapObligation
#check bridge_of_obligations
#check SomeExtractionWithGap

end YangMills
