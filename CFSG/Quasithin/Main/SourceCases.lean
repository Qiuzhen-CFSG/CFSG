module

public import CFSG.Quasithin.Main.RemainingSources
public import CFSG.Quasithin.MainForward.SourceCases
public import CFSG.Quasithin.Chapter14.Section08.SourceApplications

/-!
# Main-Theorem equivalence using the five local quotient branches

This specializes the remaining-source assembly to the full-model A₅ route.
The forward proof uses the completed Chapter 2 theorem and the actual D
quotient dispatcher; the converse is already proved for the full catalogue.
The second theorem supplies E through the existing MS/15.1.3 source assembly.

All earlier source premises remain explicit. In particular these theorems do
not assert completion of D, E or the unconditional Main Theorem. Source:
Aschbacher--Smith, Main Theorem 0.1.2 and its proof on printed p.1166.
-/

public section
namespace CFSG.Quasithin

open Subgroup Theory.GroupTheory ClassificationModels
open Chapter14.Section08.SourceCases
open Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation
open ChapterA.Section05To06 Chapter15.Section03
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

universe u
variable {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
variable (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
  (caseOne : Chapter14.Section03.CaseOneSource.Earlier1332CaseOne.{u})
  (catalogue : Catalogue G) (unitary : UnitaryExclusion G)
  (six : SixRecognition G) (nonabelian : NonabelianRecognition G)
  (abelian : AbelianRecognition G) (five : FiveRecognition G)

include structural caseOne catalogue unitary nonabelian abelian

include six five in
/-- The exact proper-K equivalence through the local source branches. The A₅
input has only the full-model conclusion actually supplied by its producer. -/
theorem classification_of_local_source_branches_and_E
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
    exact MainForward.forward_of_local_source_branches structural caseOne catalogue
      unitary six nonabelian abelian five hG (hE hG)
  · exact MainConverse.quasithin_and_evenCharacteristic_of_model hna

include six five in
/-- The specialized counterpart of `classification_of_MS_and_remaining_sources`:
use the full-model A₅ endpoint and supply E from the original MS and 15.1.3
inputs, preserving the whole Main-Theorem catalogue including general Ree. -/
theorem classification_of_MS_and_local_source_branches
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
  apply classification_of_local_source_branches_and_E structural caseOne catalogue
    unitary six nonabelian abelian five hna hK
  intro hG T hmany hempty
  exact Chapter15.source_theoremE_of_MS_classifications earlier hG T hmany hempty
    (h1513 hG T hmany hempty)

/-- A literal application of the current A₅ terminal export and the original
13.8.1 central-quotient interface. The earlier context construction, A.3.12,
5.2.3, MS and 15.1.3 inputs remain explicit for their source producers. -/
theorem classification_of_MS_and_source_contexts
    (source1381 : Chapter14.Section03.FaithfulSource.Theorem1381.{u})
    (contexts : FiveContextInput G)
    (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
      IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ →
      ∀ (S : Sylow 2 Y) (B : Subgroup Y), B ∈ ChapterA.Section03.localCComponents S →
        Chapter1.Section02.A312Conclusion B)
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
  classification_of_MS_and_local_source_branches structural caseOne catalogue unitary
    (sixRecognition_of_theorem1381 source1381) nonabelian abelian
    (fiveRecognition_of_source_context contexts hA312 h523) earlier hna hK h1513

end CFSG.Quasithin
