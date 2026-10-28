module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.PreliminaryActions.Comparison.ModelFacts.Centers
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.PreliminaryActions.Comparison.ModelFacts.Transport
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.PreliminaryActions.Comparison.ModelFacts.Doubled
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.PreliminaryActions.Comparison.ModelFacts.TwoAndFive
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.PreliminaryActions.Comparison.ModelFacts.ThreeCovers

/-!
# Source rows on the literal B.5.9 seed

The complete projective-line-correct B.5.1 implication is applied to the
prepared faithful quotient LA/C_LA(U). Exhausting every source constructor
leaves the rank-one rows and proves that the original L is disjoint from
C_G(L). The imported transport identifies the actual offender image with
Aut_A(U), proving the rank-equality and inner-action transfer steps.

`comparedCase_of_source` assembles all five surviving rows. Perfectness
first proves that L⁺ generates the whole seed, identifying the source moved
space with U. The branch comparisons then establish the actual marked
actions, offender images, Irr⁺ assertions, inner actions and rank equalities.
`comparisonCertificate_of_source_classification` applies the complete earlier
B.5.1 implication to this literal quotient and compares that same witness.
The final theorem supplies `LocalAlternative` without a comparison premise.

The only earlier-source implications retained by this comparison are the
full projective-line-correct B.5.1 input (owner `qt-b05-quasisimple`) and
the full B.4.8(2) input (owners `qt-b-04-natural-extensions` / `qt-b-04`).
Their final discharge belongs to `qt-b05-general-classification`. The seed
preparation is the separate proved output of `Preparation.prepared_of_source`;
no U=[V,L], A≤L, local extension classification or selected row is assumed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.9,
printed pp.107–108, using B.4.2, B.4.8(2), B.5.1 and I.1.6.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.PreliminaryActions
open QuasisimpleSource
universe u v

/-- The complete earlier source theorem supplies one actual conclusion;
the rank reduction and centralizer disjointness hold for that same witness. -/
theorem source_rows_on_seed {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) {K : GroupClass.{u}} {A L : Subgroup G}
    (hLA : ⁅L,A⁆ = L) (p : Prepared ρ K hLA) (hr : primeRank 3 L = 1)
    (earlier : ProjectiveLine.QuasisimpleClassificationInput.{u,v} K) :
    ∃ c : ProjectiveLine.QuasisimpleSourceConclusion
        (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA),
      RankOneActionCase (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA) c.sectionData ∧
        Disjoint L (centralizer (L : Set G)) := by
  obtain ⟨c⟩ := earlier _ _ (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA) p.source
  exact ⟨c, seed_rankOneAction_of_source ρ hLA p hr c,
    seed_disjoint_of_source ρ hLA p hr c⟩

variable {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V)

/-- Exhaust the complete source conclusion on the literal seed. The common
moved-space identity is proved here from perfectness; each surviving row
retains its original action, offender family and quotient convention. -/
theorem comparedCase_of_source
    (h48 : ThreeCovers.CentralExtension.EarlierB48Two.{u,v})
    {K : GroupClass.{u}} (hyp : FFHypothesis K ρ)
    {A L : Subgroup G} (hA : IsMinimalBestOffender ρ A)
    (hL : IsComponent G L) (hLA : ⁅L,A⁆ = L)
    (p : Prepared ρ K hLA) (hr : primeRank 3 L = 1)
    (c : ProjectiveLine.QuasisimpleSourceConclusion
      (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA)) :
    ComparedCase ρ hLA := by
  have hm := seedQuotient_moved_eq_top ρ hLA hL
  cases seed_rankOneAction_of_source ρ hLA p hr c with
  | irreducible hi hf hir row hext =>
      cases row with
      | linearTwo F hg e ho hq =>
          exact compared_linearTwo_of_source ρ hLA p hr c hm hi hf hir hext F hg e ho hq
      | linearThree F ho hg e hq =>
          exact compared_linearThree_of_source ρ h48 hLA p hr c hm hi hf hir hext F ho hg e hq
      | symmetricFive e ho hq =>
          exact compared_symmetricFive_of_source ρ hLA p hyp hA c hm hi hf hir hext e ho hq
  | doubleThree F ho ht e hoff hq =>
      exact compared_doubleThree_of_source ρ hLA p hL hr c F ho ht e hoff hq

/-- Apply the full earlier B.5.1 theorem to the prepared quotient and prove
its comparison certificate. No local comparison conclusion is an input. -/
theorem comparisonCertificate_of_source_classification
    (h48 : ThreeCovers.CentralExtension.EarlierB48Two.{u,v})
    {K : GroupClass.{u}}
    (earlier : ProjectiveLine.QuasisimpleClassificationInput.{u,v} K)
    (hyp : FFHypothesis K ρ)
    {A L : Subgroup G} (hA : IsMinimalBestOffender ρ A)
    (hL : IsComponent G L) (hLA : ⁅L,A⁆ = L)
    (p : Prepared ρ K hLA) (hr : primeRank 3 L = 1) :
    ComparisonCertificate ρ hLA := by
  obtain ⟨c⟩ := earlier _ _ (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA) p.source
  exact ⟨⟨c⟩, comparedCase_of_source ρ h48 hyp hA hL hLA p hr c⟩

/-- The actual consumer of the exhaustive comparison. This discharges the
local-action premise of the preliminary assembly from the faithful preparation
and the two full earlier-source implications. -/
theorem localAlternative_of_source_classification
    (h48 : ThreeCovers.CentralExtension.EarlierB48Two.{u,v})
    {K : GroupClass.{u}}
    (earlier : ProjectiveLine.QuasisimpleClassificationInput.{u,v} K)
    (hyp : FFHypothesis K ρ)
    {A L : Subgroup G} (hA : IsMinimalBestOffender ρ A)
    (hL : IsComponent G L) (hLA : ⁅L,A⁆ = L)
    (p : Prepared ρ K hLA) (hr : primeRank 3 L = 1) :
    LocalAlternative ρ hLA :=
  localAlternative_of_comparison ρ hLA
    (comparisonCertificate_of_source_classification ρ h48 earlier hyp hA hL hLA p hr)

end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.PreliminaryActions
