module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.PreliminaryActions.LocalContracts
public import Theory.SpecificGroups.Classical.BinaryDerivedCubicRank
public import Theory.SpecificGroups.Classical.SignedThreeCubicRank

/-!
# Source comparison for the preliminary component action

The source B.5.1 conclusion is a statement about the faithful action on the
literal quotient `LA/C_LA(U)`.  `LocalAlternative`, in contrast, is a statement
about the original seed action and remembers the offender image, the marked
`S₅` action, and the centralizer projections.  These are different interfaces:
the former does not definitionally identify its moved section with `U`, nor does
it transport the offender subgroup back through the quotient map.

This file publishes the comparison certificate used by the source assembly.
Its `source` field is the complete earlier B.5.1 conclusion; its `case` field
is the result of the B.4.2/B.4.8/I.1.6 comparison on that literal section.
The conversion to `LocalAlternative` is proved here. The extension
`Comparison.ModelFacts` constructs the certificate by exhausting the complete
source cases, proving the quotient-to-seed transport and eliminating the
other B.4.2 rows using the actual three-rank hypothesis. Its theorem
`localAlternative_of_source_classification` has no comparison-case premise.
`Comparison.PreparedApplication` connects this theorem to the preliminary
assembly. Neither construction assumes `U = W` or `A ≤ L`.

The two rank lemmas at the end record reusable eliminations: the existing
concrete model calculations exclude derived symplectic and `G₂` rows, and the
signed cubic calculation excludes even binary degree in an `SL₃` row.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.4.2,
B.4.8 and B.5.9, printed pp.86, 91 and 107–108.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.PreliminaryActions
open QuasisimpleSource
universe u v w

variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V]
  [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The five rows left after the B.4.2/B.4.8 comparison.  The group and
representation data are all on the literal seed action; no conclusion about
the ambient moved space is included here. -/
inductive ComparedCase {A L : Subgroup G} (hLA : ⁅L,A⁆ = L) : Prop
  | linearTwo (F : BinaryField)
      (natural : IsLinearNatural (reducedAction (seedComponentAction ρ hLA)) F 2)
      (irrPlus : IsIrrPlus ρ L (naturalSeedSpace ρ L A))
      (sylow : ∃ T : Sylow 2 (seedComponentImage ρ hLA),
        seedOffenderImage ρ hLA = (T : Subgroup (seedComponentImage ρ hLA)).map
          (seedComponentImage ρ hLA).subtype)
      (inner : InducesInner A L) (disjoint : Disjoint L (centralizer (L : Set G)))
      (rank_eq : SeedRankEquality ρ A L)
  | symmetricFive
      (action : MarkedActionEquiv (seedSubrepresentation ρ hLA).toRepresentation
        ⊤ (L.subgroupOf (L ⊔ A))
        (BinaryPermutation.naturalRepresentation (Fin 5)) (alternatingGroup (Fin 5)))
      (order : Nat.card (seedOffenderImage ρ hLA) = 2)
      (rank_eq : SeedRankEquality ρ A L)
  | doubleThree (F : BinaryField) (odd_degree : Odd F.degree)
      (natural : IsRepeatedLinearNatural (seedComponentAction ρ hLA) F 3 2)
      (span : naturalSeedSpace ρ L A ≤ sSup {I | IsIrrPlus ρ L I})
      (inner : InducesInner A L) (disjoint : Disjoint L (centralizer (L : Set G)))
      (rank_eq : SeedRankEquality ρ A L)
  | naturalThree (F : BinaryField) (odd_degree : Odd F.degree)
      (natural : ActionEquiv (seedComponentAction ρ hLA) (linearNatural F 3))
      (inner : InducesInner A L)
  | fourCover (cover : FourDimensionalCoverSource (seedComponentAction ρ hLA))
      (klein : Nonempty (seedOffenderImage ρ hLA ≃* Multiplicative (Fin 2 → ZMod 2)))
      (irrPlus : IsIrrPlus ρ L (naturalSeedSpace ρ L A))
      (inner : InducesInner A L) (disjoint : Disjoint L (centralizer (L : Set G)))
      (rank_eq : SeedRankEquality ρ A L)

namespace ComparedCase

/-- Every compared row is one of the five native local alternatives. -/
theorem toLocalAlternative {A L : Subgroup G} {hLA : ⁅L,A⁆ = L}
    (c : ComparedCase ρ hLA) : LocalAlternative ρ hLA := by
  cases c with
  | linearTwo F natural irrPlus sylow inner disjoint rank_eq =>
      exact .linearTwo F natural irrPlus sylow inner disjoint rank_eq
  | symmetricFive action order rank_eq =>
      exact .symmetricFive action order rank_eq
  | doubleThree F odd_degree natural span inner disjoint rank_eq =>
      exact .doubleThree F odd_degree natural span inner disjoint rank_eq
  | naturalThree F odd_degree natural inner =>
      exact .naturalThree F odd_degree natural inner
  | fourCover cover klein irrPlus inner disjoint rank_eq =>
      exact .fourCover cover klein irrPlus inner disjoint rank_eq

end ComparedCase

/-- A certificate retains the complete earlier conclusion together with the
local comparison of its actual quotient action.  Keeping the source conclusion
in the certificate prevents a downstream consumer from silently replacing the
projective-line-correct B.5.1 input by a reduced action label. -/
structure ComparisonCertificate [Finite G]
    {A L : Subgroup G} (hLA : ⁅L,A⁆ = L) where
  source : Nonempty (ProjectiveLine.QuasisimpleSourceConclusion
    (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA))
  case : ComparedCase ρ hLA

/-- The source comparison output consumed by `preliminary_of_local_alternative`.
The complete source conclusion remains available in the certificate for audits;
the proof uses only the verified comparison row. -/
theorem localAlternative_of_comparison
    [Finite G]
    {A L : Subgroup G} (hLA : ⁅L,A⁆ = L)
    (c : ComparisonCertificate ρ hLA) : LocalAlternative ρ hLA :=
  c.case.toLocalAlternative

/-- If a source producer already has the universal B.5.1 implication, it can
package its actual conclusion and a separately proved comparison row without
changing the quotient convention. -/
theorem comparisonCertificate_of_source
    [Finite G]
    {A L : Subgroup G} (hLA : ⁅L,A⁆ = L)
    (source : Nonempty (ProjectiveLine.QuasisimpleSourceConclusion
      (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA)))
    (case : ComparedCase ρ hLA) : ComparisonCertificate ρ hLA :=
  ⟨source, case⟩

/- The earlier universal implication is applied to the actual faithful seed
quotient here.  This is deliberately separate from the comparison row: the
source producer must still prove that its selected B.4.2/B.4.8 row is the one
realized by this conclusion. -/
theorem comparisonCertificate_of_earlier
    {K : GroupClass.{u}} [Finite G]
    {A L : Subgroup G} (hLA : ⁅L,A⁆ = L)
    (p : Prepared ρ K hLA)
    (earlier : ProjectiveLine.QuasisimpleClassificationInput.{u,v} K)
    (case : ComparedCase ρ hLA) : ComparisonCertificate ρ hLA := by
  obtain ⟨c⟩ := earlier _ _ (seedQuotientAction ρ hLA)
    (seedComponentImage ρ hLA) p.source
  exact ⟨⟨c⟩, case⟩

/-- Convenient assembly form: once the source producer has supplied its
comparison row, the earlier universal implication and `Prepared.source` are
discharged on the actual quotient in one step. -/
theorem localAlternative_of_earlier
    {K : GroupClass.{u}} [Finite G]
    {A L : Subgroup G} (hLA : ⁅L,A⁆ = L)
    (p : Prepared ρ K hLA)
    (earlier : ProjectiveLine.QuasisimpleClassificationInput.{u,v} K)
    (case : ComparedCase ρ hLA) : LocalAlternative ρ hLA :=
  localAlternative_of_comparison ρ hLA
    (comparisonCertificate_of_earlier ρ hLA p earlier case)

end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.PreliminaryActions

namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.PreliminaryActions

open QuasisimpleSource
open Theory.GroupTheory
universe u w

/-- A component of three-rank one cannot be the derived symplectic model.  The
model equivalence is explicit because the source action itself may be on a
cover rather than on the derived subgroup. -/
theorem not_derived_symplectic_of_threeRank_one
    {L : Type u} {H : Type w} [Group L] [Group H] [Finite L] [Finite H]
    (e : L ≃* H)
    (hmodel : 2 ≤ primeRank 3 H)
    (hr : primeRank 3 L = 1) : False := by
  have he := primeRank_equiv 3 e
  rw [hr] at he
  omega

/-- The corresponding exclusion for the derived `G₂` model. -/
theorem not_derived_g2_of_threeRank_one
    {L : Type u} {H : Type w} [Group L] [Group H] [Finite L] [Finite H]
    (e : L ≃* H)
    (hmodel : 2 ≤ primeRank 3 H)
    (hr : primeRank 3 L = 1) : False := by
  have he := primeRank_equiv 3 e
  rw [hr] at he
  omega

/-- Concrete specialization of the preceding lemma to the actual derived
symplectic carrier. -/
theorem not_binary_derived_symplectic_of_threeRank_one
    {L : Type u} [Group L] [Finite L]
    (e : L ≃* _root_.commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)))
    (hr : primeRank 3 L = 1) : False :=
  not_derived_symplectic_of_threeRank_one e
    Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.symplectic hr

/-- Concrete specialization to the actual derived binary `G₂` carrier. -/
theorem not_binary_derived_g2_of_threeRank_one
    {L : Type u} [Group L] [Finite L]
    (e : L ≃* _root_.commutator (Atlas.G2.Model (ZMod 2)))
    (hr : primeRank 3 L = 1) : False :=
  not_derived_g2_of_threeRank_one e
    Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.g2 hr

/-- Even binary degree is excluded in an actual `SL₃` model when the component
has three-rank one.  The field cardinality is taken from the `BinaryField`
record, so no implicit identification of a field family is used. -/
theorem not_even_linearThree_of_threeRank_one
    {L : Type u} [Group L] [Finite L]
    (F : BinaryField) (e : L ≃* Matrix.SpecialLinearGroup (Fin 3) F.Carrier)
    (heven : Even F.degree) (hr : primeRank 3 L = 1) : False := by
  have hmodel := Theory.SpecificGroups.SignedThreeCubicRank.linear_special
    F.card_eq heven
  have he := primeRank_equiv 3 e
  rw [hr] at he
  omega

end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.PreliminaryActions
