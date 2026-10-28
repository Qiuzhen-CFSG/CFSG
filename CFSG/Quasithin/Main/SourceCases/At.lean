module

public import CFSG.Quasithin.Main.SourceCases
public import CFSG.Quasithin.MainForward.SourceCases.At
public import CFSG.Quasithin.Chapter14.Section08.SourceApplications.KnownSimple

/-!
# Main-Theorem equivalence from the same-G,T source branches

The forward implication constructs the original simple QTKE hypothesis before
asking for local structural and naturality inputs. Both retain the actual
multiple-overgroup guard, so neither requires singleton normalization. The
five-row dispatcher accepts the full A₅ model output. The reverse implication
is the existing full-catalogue converse.

The MS application supplies E through the current source assembly. These are
conditional endpoints: the Chapter12, quotient and recognition inputs, and the
separate MS/15.1.3 inputs, still require their source producers. The universal
public endpoints in `Main.SourceCases` remain unchanged.
Source: Aschbacher--Smith, Main Theorem 0.1.2 and its proof on printed p.1166.
-/

public section
namespace CFSG.Quasithin

open Subgroup Theory.GroupTheory ClassificationModels
open Chapter12.Section02 Chapter14.Section08.SourceCases
open Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation
open ChapterA.Section05To06 Chapter15.Section03
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

universe u
variable {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
variable
  (structural : IsSimpleQTKE KnownSimple.IsKnownSimple G → ∀ T : Sylow 2 G,
    1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
    Structural1222At KnownSimple.IsKnownSimple T)
  (caseOne : IsSimpleQTKE KnownSimple.IsKnownSimple G → ∀ T : Sylow 2 G,
    1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard → Earlier1332CaseOneAt T)
  (catalogue : Catalogue G) (unitary : UnitaryExclusion G)
  (six : SixRecognition G) (nonabelian : NonabelianRecognition G)
  (abelian : AbelianRecognition G) (five : FiveRecognition G)

include structural caseOne catalogue unitary six nonabelian abelian five

/-- The proper-K equivalence with structure and naturality requested only
for the original simple QTKE group and its multiple-overgroup Sylow subgroups. -/
theorem classification_of_local_source_branches_and_E_at
    (hna : ¬ IsMulCommutative G)
    (hK : HasProperKSubgroups KnownSimple.IsKnownSimple G)
    (hE : IsSimpleQTKE KnownSimple.IsKnownSimple G → ∀ T : Sylow 2 G,
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      MainForward.faithfulLocalComponents T = ∅ → IsTheoremEModel G) :
    (IsQuasithin G ∧ IsEvenCharacteristic G) ↔ IsQTKEModel G := by
  constructor
  · rintro ⟨hQT, hEC⟩
    have hG : IsSimpleQTKE KnownSimple.IsKnownSimple G :=
      ⟨⟨hQT, hK, hEC⟩, inferInstance, hna⟩
    exact MainForward.forward_of_local_source_branches_at (structural hG) (caseOne hG)
      catalogue unitary six nonabelian abelian five hG (hE hG)
  · exact MainConverse.quasithin_and_evenCharacteristic_of_model hna

/-- Apply the existing MS/15.1.3 source producer of E to the local forward
route. No universal structural theorem is inferred from its local instances. -/
theorem classification_of_MS_and_local_source_branches_at
    (earlier : EarlierMSClassifications.{u} KnownSimple.IsKnownSimple)
    (hna : ¬ IsMulCommutative G)
    (hK : HasProperKSubgroups KnownSimple.IsKnownSimple G)
    (h1513 : IsSimpleQTKE KnownSimple.IsKnownSimple G → ∀ T : Sylow 2 G,
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      MainForward.faithfulLocalComponents T = ∅ → ∀ Mc : Subgroup G,
      maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc} →
      IsTheoremEModel G ∨ ∃ M : Subgroup G, IsOrderingMaximal T M ∧
        Nonempty (NaturalOrthogonalAction M (localModule T M))) :
    (IsQuasithin G ∧ IsEvenCharacteristic G) ↔ IsQTKEModel G := by
  apply classification_of_local_source_branches_and_E_at structural caseOne catalogue
    unitary six nonabelian abelian five hna hK
  intro hG T hmany hempty
  exact Chapter15.source_theoremE_of_MS_classifications earlier hG T hmany hempty
    (h1513 hG T hmany hempty)

omit six five in
/-- Instantiate the A₅ and both A₆ rows using the current terminal and
central-quotient source APIs. The terminal A.3.12 input is discharged upstream;
the literal source contexts and independent 5.2.3 input remain visible. -/
theorem classification_of_MS_and_source_contexts_at
    (source1381 : Chapter14.Section03.FaithfulSource.Theorem1381.{u})
    (contexts : FiveContextInput G)
    (h523 : Source523.EarlierTheorem.{u} KnownSimple.IsKnownSimple)
    (earlier : EarlierMSClassifications.{u} KnownSimple.IsKnownSimple)
    (hna : ¬ IsMulCommutative G)
    (hK : HasProperKSubgroups KnownSimple.IsKnownSimple G)
    (h1513 : IsSimpleQTKE KnownSimple.IsKnownSimple G → ∀ T : Sylow 2 G,
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      MainForward.faithfulLocalComponents T = ∅ → ∀ Mc : Subgroup G,
      maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc} →
      IsTheoremEModel G ∨ ∃ M : Subgroup G, IsOrderingMaximal T M ∧
        Nonempty (NaturalOrthogonalAction M (localModule T M))) :
    (IsQuasithin G ∧ IsEvenCharacteristic G) ↔ IsQTKEModel G :=
  classification_of_MS_and_local_source_branches_at structural caseOne catalogue unitary
    (sixRecognition_of_theorem1381 source1381) nonabelian abelian
    (fiveRecognition_of_source_context_knownSimple contexts h523) earlier hna hK h1513

end CFSG.Quasithin
