module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.Contracts
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.Reconstruction
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.Offenders
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.Preparation
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.CoverCentralizer
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.PreparationInput
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.ModuleCalculation

/-!
# The high-three-rank branch and rank-one reduction of B.5.7

The finite SQTK presentation is constructed from the actual quotient in
B.5.3 using the proved nilpotent-cover theorem. Its prime cores map onto
those of the quotient, so the three-core used in the module argument is
literally the image of the three-core in the cover.

The central Fitting case applies the full universal B.5.1 contract and keeps
all its module conclusions on the actual generalized Fitting subgroup.
In the noncentral case the cover reduction constructs the lifted component,
its rank bound, both layer identities, the cyclic three-core and its first
omega subgroup, and centralizer oddness. The module argument then identifies
the original component and O₃(G) with A₆ and C₃ and proves both centralizer
equalities. Reconstruction gives the literal internal product and a generator
inducing the specified outer automorphism on each factor.

`high_three_rank_alternative` assembles these two branches without an
intermediate-context premise. Its application to `AdequateAlternative`,
together with positive component three-rank from B.5.5, proves that every
component has three-rank exactly one under the negation of that alternative.

Exactly five universal earlier-source implications remain explicit:
* full B.5.1, `ProjectiveLine.QuasisimpleClassificationInput`, produced by
  `qt-b05-quasisimple`;
* full B.5.2 and B.5.5, `CoverInput` and `ComponentsInput` in
  `CoverCentralizer.SourceConstruction`, produced by `qt-b05-quotient-components`;
* full A.2.1, `CoverCentralizer.SourceConstruction.SemisimpleInput`, produced
  by `qt-a-02`;
* all six rows of I.1.3, `EarlierMultiplierInput` in
  `ModuleCalculation.NaturalReduction.ModelComparison.BinaryG2Exclusion`,
  produced by `qt-i-01`, including `qt-i01-lie-a2`.
The numerical multiplier bound needed by the cover proof is derived from
that same complete table. The cover proof establishes the component-uniqueness
and cyclic-core deductions used from A.3.18 directly, by rank, multiplier
and cyclic Sylow transfer arguments; it does not assume an A.3.18 alternative.
The preparation variants use the single B.5.5 input already consumed by
component descent: its literal chief-section projection proves positive
component rank and its Fitting field supplies the cover identity. Thus final
induction need not establish both B.5.5 presentations. The original APIs remain
available. The final conditional B.5.6 induction and earlier-source discharge
remain with `qt-b05-general-source-induction` and its source assembly owner.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, B.5.2–B.5.7,
printed pp.103–106. No assertion about the disputed fixed-space splitting
in B.5.6(4) is made.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank
open CoverCentralizer.SourceConstruction
open ModuleCalculation.NaturalReduction.ModelComparison.BinaryG2Exclusion
universe u v

/-- All six actual multiplier groups in I.1.3 have order dividing 48;
the exhaustive clause also handles the trivial multiplier. -/
private theorem multiplierInput_of_table {K : GroupClass.{u}}
    (multipliers : EarlierMultiplierInput K) : MultiplierInput K := by
  classical
  intro S _ _ _ _ hs
  rcases subsingleton_or_nontrivial (PerfectCentralCovering.schurMultiplier S) with ht | hn
  · let := ht
    simp only [Nat.card_unique, one_dvd]
  · obtain ⟨r, hr⟩ := (multipliers S hs).exhaustive.mp hn
    obtain ⟨e⟩ := (multipliers S hs).values r hr
    rw [Nat.card_congr e.toEquiv]
    cases r <;> norm_num [MultiplierShape.Carrier, Nat.card_prod]

variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}
variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
variable (ρ : Representation (ZMod 2) G V)

/-- The full earlier B.5.1 conclusion is retained on the actual generalized Fitting subgroup. -/
theorem quasisimple_branch (earlier : ProjectiveLine.QuasisimpleClassificationInput.{u,v} K)
    (hyp : FFHypothesis K ρ) {L : Subgroup G} (hL : IsComponent G L)
    (hsqtk : IsSQTK K L) (hfit : generalizedFitting G = L ⊔ center G) :
    IsQuasisimple (generalizedFitting G) ∧
      Nonempty (ProjectiveLine.QuasisimpleSourceConclusion ρ (generalizedFitting G)) := by
  obtain ⟨c⟩ := earlier G V ρ L
    ⟨hyp.finite_module, hyp.faithful, hL.2, hsqtk, hfit, hyp.twoCore, hyp.generated⟩
  rw [← c.fitting_eq]
  exact ⟨hL.2, ⟨c⟩⟩

/-- Application of the central branch to the adequate classification's literal alternative. -/
theorem adequate_of_central_fitting
    (earlier : ProjectiveLine.QuasisimpleClassificationInput.{u,v} K)
    (hyp : FFHypothesis K ρ) {L : Subgroup G} (hL : IsComponent G L)
    (hsqtk : IsSQTK K L) (hfit : generalizedFitting G = L ⊔ center G) :
    AdequateAlternative ρ := by
  obtain ⟨hq, ⟨c⟩⟩ := quasisimple_branch ρ earlier hyp hL hsqtk hfit
  exact Or.inr (.quasisimple hq c)

/-- Actual three-core application of the group reconstruction. The source
assembly below constructs both intermediate records on this same component. -/
theorem outerShape_of_module_calculation {L : Subgroup G}
    (d : NoncentralContext K G L) (c : CubicCentralizers G L) :
    Nonempty (OuterSixThreeShape G) := by
  let : L.Normal := d.normal
  exact outerShape_of_centralizers L (pCore 3 G) c.componentEquiv c.threeCoreEquiv
    c.component_centralizer c.threeCore_centralizer d.noncentral

/-- The constructed outer shape gives the adequate alternative on the original action. -/
theorem adequate_of_module_calculation {L : Subgroup G}
    (d : NoncentralContext K G L) (c : CubicCentralizers G L) :
    AdequateAlternative ρ := by
  obtain ⟨h⟩ := outerShape_of_module_calculation d c
  exact Or.inr (.outerSixThree h)

/-- The high-three-rank component branch underlying B.5.7, conditional only
on the five complete universal earlier-source implications. The quasisimple
alternative retains all B.5.1 clauses; the other has the actual outer shape. -/
theorem high_three_rank_alternative
    (earlier : ProjectiveLine.QuasisimpleClassificationInput.{u,v} K)
    (h52 : CoverInput K) (h55 : ComponentsInput.{u,v} K)
    (hA : SemisimpleInput K) (multipliers : EarlierMultiplierInput K)
    (hyp : FFHypothesis K ρ) {L : Subgroup G}
    (hL : IsComponent G L) (hr : 1 < primeRank 3 L) :
    (IsQuasisimple (generalizedFitting G) ∧
      Nonempty (ProjectiveLine.QuasisimpleSourceConclusion ρ (generalizedFitting G))) ∨
      Nonempty (OuterSixThreeShape G) := by
  rcases CoverCentralizer.reduction h52 h55 hA
    (multiplierInput_of_table multipliers) hyp hL hr with ⟨hsq, hfit⟩ | hd
  · exact Or.inl (quasisimple_branch ρ earlier hyp hL hsq hfit)
  · obtain ⟨d⟩ := hd
    obtain ⟨c⟩ := ModuleCalculation.cubicCentralizers_of_earlier_source
      ρ earlier multipliers hyp hL hr d
    exact Or.inr (outerShape_of_module_calculation d c)

/-- Apply the high-rank branch to the separate adequate classification on
the original action, without asserting the disputed fixed-space splitting. -/
theorem adequate_of_high_three_rank
    (earlier : ProjectiveLine.QuasisimpleClassificationInput.{u,v} K)
    (h52 : CoverInput K) (h55 : ComponentsInput.{u,v} K)
    (hA : SemisimpleInput K) (multipliers : EarlierMultiplierInput K)
    (hyp : FFHypothesis K ρ) {L : Subgroup G}
    (hL : IsComponent G L) (hr : 1 < primeRank 3 L) : AdequateAlternative ρ := by
  rcases high_three_rank_alternative ρ earlier h52 h55 hA multipliers hyp hL hr with
    ⟨hq, ⟨c⟩⟩ | hc
  · exact Or.inr (.quasisimple hq c)
  · obtain ⟨c⟩ := hc
    exact Or.inr (.outerSixThree c)

/-- B.5.7's exact component rank-one reduction for a counterexample to the
separately named adequate classification. The lower bound comes from the
complete B.5.5 chief-section model conclusion. -/
theorem component_rank_eq_one_of_not_adequate
    (earlier : ProjectiveLine.QuasisimpleClassificationInput.{u,v} K)
    (h52 : CoverInput K) (h55 : ComponentsInput.{u,v} K)
    (hA : SemisimpleInput K) (multipliers : EarlierMultiplierInput K)
    (hyp : FFHypothesis K ρ) (hnot : ¬ AdequateAlternative ρ)
    {L : Subgroup G} (hL : IsComponent G L) : primeRank 3 L = 1 := by
  have hpos := CoverCentralizer.component_rank_pos h55 hyp hL
  have hle : primeRank 3 L ≤ 1 := by
    by_contra hr
    exact hnot (adequate_of_high_three_rank ρ earlier h52 h55 hA multipliers
      hyp hL (by omega))
  omega

/-- The source B.5.7 high-rank branch using the same B.5.5 chief-section
input as the component descent. Its positive-rank and Fitting consequences
supply the cover construction, without a second classification presentation. -/
theorem high_three_rank_alternative_of_preparation
    (earlier : ProjectiveLine.QuasisimpleClassificationInput.{u,v} K)
    (h52 : CoverInput K)
    (h5 : ComponentReduction.PreliminaryActions.Preparation.ComponentInput.{u,v} K)
    (hA : SemisimpleInput K) (multipliers : EarlierMultiplierInput K)
    (hyp : FFHypothesis K ρ) {L : Subgroup G}
    (hL : IsComponent G L) (hr : 1 < primeRank 3 L) :
    (IsQuasisimple (generalizedFitting G) ∧
      Nonempty (ProjectiveLine.QuasisimpleSourceConclusion ρ (generalizedFitting G))) ∨
      Nonempty (OuterSixThreeShape G) := by
  rcases CoverCentralizer.reduction_of_preparation ρ h52 h5 hA
    (multiplierInput_of_table multipliers) hyp hL hr with ⟨hsq, hfit⟩ | hd
  · exact Or.inl (quasisimple_branch ρ earlier hyp hL hsq hfit)
  · obtain ⟨d⟩ := hd
    obtain ⟨c⟩ := ModuleCalculation.cubicCentralizers_of_earlier_source
      ρ earlier multipliers hyp hL hr d
    exact Or.inr (outerShape_of_module_calculation d c)

/-- Apply the single-input B.5.7 reduction to the original action's adequate
classification, retaining every earlier B.5.1 action conclusion. -/
theorem adequate_of_high_three_rank_of_preparation
    (earlier : ProjectiveLine.QuasisimpleClassificationInput.{u,v} K)
    (h52 : CoverInput K)
    (h5 : ComponentReduction.PreliminaryActions.Preparation.ComponentInput.{u,v} K)
    (hA : SemisimpleInput K) (multipliers : EarlierMultiplierInput K)
    (hyp : FFHypothesis K ρ) {L : Subgroup G}
    (hL : IsComponent G L) (hr : 1 < primeRank 3 L) : AdequateAlternative ρ := by
  rcases high_three_rank_alternative_of_preparation ρ earlier h52 h5 hA multipliers
    hyp hL hr with ⟨hq, ⟨c⟩⟩ | hc
  · exact Or.inr (.quasisimple hq c)
  · obtain ⟨c⟩ := hc
    exact Or.inr (.outerSixThree c)

/-- B.5.7's exact component rank-one conclusion from the B.5.5 input already
used for component descent. -/
theorem component_rank_eq_one_of_preparation
    (earlier : ProjectiveLine.QuasisimpleClassificationInput.{u,v} K)
    (h52 : CoverInput K)
    (h5 : ComponentReduction.PreliminaryActions.Preparation.ComponentInput.{u,v} K)
    (hA : SemisimpleInput K) (multipliers : EarlierMultiplierInput K)
    (hyp : FFHypothesis K ρ) (hnot : ¬ AdequateAlternative ρ)
    {L : Subgroup G} (hL : IsComponent G L) : primeRank 3 L = 1 := by
  have hpos := component_rank_pos_of_preparation ρ (h5 G V ρ hyp) hL
  have hle : primeRank 3 L ≤ 1 := by
    by_contra hr
    exact hnot (adequate_of_high_three_rank_of_preparation ρ earlier h52 h5 hA
      multipliers hyp hL (by omega))
  omega

end CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank
