module

public import CFSG.Quasithin.Main.SourceCases.At
public import CFSG.Quasithin.Chapter15.SourceAssembly.C132Complete

/-!
# The guarded Main equivalence with original C.1.32 supplied

The complete rank-one source supplies Theorem E from the original 15.1.3
and 15.3.13 inputs. Applying it at the existing E boundary preserves every
guarded D source input, the proper-K hypothesis, and the full QTKE catalogue.
Source: Aschbacher--Smith Theorem E and the Main Theorem, pp.1165--1166.
-/

public section
namespace CFSG.Quasithin
open Subgroup Theory.GroupTheory ClassificationModels
open Chapter12.Section02 Chapter14.Section08.SourceCases
open ChapterA.Section05To06 Chapter15.Section03
universe u
variable {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]

/-- The exact local Main interface with E reduced to its two independent
original source inputs and the C.1.32 reconstruction supplied internally. -/
theorem classification_of_original_1513_15313_and_local_source_branches_at
    (structural : IsSimpleQTKE KnownSimple.IsKnownSimple G → ∀ T : Sylow 2 G,
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Structural1222At KnownSimple.IsKnownSimple T)
    (caseOne : IsSimpleQTKE KnownSimple.IsKnownSimple G → ∀ T : Sylow 2 G,
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard → Earlier1332CaseOneAt T)
    (catalogue : Catalogue G) (unitary : UnitaryExclusion G)
    (six : SixRecognition G) (nonabelian : NonabelianRecognition G)
    (abelian : AbelianRecognition G) (five : FiveRecognition G)
    (hna : ¬ IsMulCommutative G)
    (hK : HasProperKSubgroups KnownSimple.IsKnownSimple G)
    (h1513 : IsSimpleQTKE KnownSimple.IsKnownSimple G → ∀ T : Sylow 2 G,
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      MainForward.faithfulLocalComponents T = ∅ → ∀ Mc : Subgroup G,
      maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc} →
      IsTheoremEModel G ∨ ∃ M : Subgroup G, IsOrderingMaximal T M ∧
        Nonempty (NaturalOrthogonalAction M (localModule T M)))
    (h13 : IsSimpleQTKE KnownSimple.IsKnownSimple G → ∀ T : Sylow 2 G,
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      MainForward.faithfulLocalComponents T = ∅ →
      ∀ d : CharacteristicTwo.LocalData G, d.T = T →
      IsOrderingMaximal d.T d.M →
      maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc} →
      ∀ Yplus : Subgroup G, Hypothesis15310 d.M d.Y d.S d.V₁ Yplus →
      primeRank 3 Yplus = 2 →
      ∀ I ∈ outsideFamily Yplus d.S d.M, generalizedFitting I ≠ pCore 2 I) :
    (IsQuasithin G ∧ IsEvenCharacteristic G) ↔ IsQTKEModel G := by
  apply classification_of_local_source_branches_and_E_at structural caseOne catalogue
    unitary six nonabelian abelian five hna hK
  intro hG T hmany hempty
  exact Chapter15.source_theoremE_of_original_1513_and_15313 hG T hmany hempty
    (h1513 hG T hmany hempty) (h13 hG T hmany hempty)

end CFSG.Quasithin
