module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Catalogue.Preparation
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Catalogue.CoreQuotients
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Reduction
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Catalogue.LinearExclusions.Source
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Catalogue.SevenKernel.Source

/-!
# Assembly of the original parabolic quotient catalogue

The binary rank-one star row contradicts the proved F.6.18 exclusion after
recovering its full two-core quotient. The binary linear-three and G₂ rows
also recover their full quotients. Both six-letter rows retain the possible
central cover. The higher linear exclusions and the natural and exceptional
seven-letter kernel arguments discharge every remaining catalogue premise.

The final model theorem uses only the unchanged original hypotheses.
Its actual rank-three application retains the separately owned module and
six-letter reconstruction premises, whose discharge belongs to the parent
rank-three assembly.
Source: Aschbacher--Smith original 14.6.10(5), printed pp.1029--1030.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open ParabolicCatalogue
universe u
variable {G : Type u} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (hlinear : LinearExclusionInput hG T hempty hM hunique hmany hcard e hab)
    (hseven : SevenRecoveryInput hG T hempty hM hunique hmany hcard e hab)

include hlinear hseven

/-- The seven actual star models give the four required intrinsic quotient
alternatives once the two remaining catalogue steps have been proved. -/
theorem source_second_parabolic_models_of_catalogue_steps :
    SourceSecondParabolicModelInput hG T hempty hM hunique hmany hcard e hab := by
  intro H hH d I hI
  obtain ⟨hi,hm,hnb⟩ := prepared hG T hempty hM hunique hmany hcard e hab H hH d I hI
  obtain ⟨hthree,hfour⟩ := hlinear H hH d I hI
  cases hm with
  | linearTwo F _ _ a =>
    exact (hnb F (binary_two_core_quotient hi F a)).elim
  | linearThree F hd a =>
    have hpos := F.degree_pos
    have hc : F.degree = 1 ∨ F.degree = 2 := by omega
    rcases hc with hc | hc
    · let : Fintype F.Carrier := Fintype.ofFinite _
      let b : F.Carrier ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
        rw [← Nat.card_eq_fintype_card,F.card_eq,hc]
        simp)
      exact Or.inl (binary_three_core_quotient hi (a.trans (Atlas.fieldEquivSL 3 b)))
    · exact (hthree F hc ⟨a⟩).elim
  | alternatingSix a =>
    exact Or.inr (Or.inl ⟨ChapterC.C27Source.source_a6_coreCenterQuotientEquiv hi a⟩)
  | alternatingSeven a =>
    exact Or.inr (Or.inr (Or.inl (hseven H hH d I hI ⟨a⟩)))
  | tripleSix _ a =>
    exact Or.inr (Or.inl (triple_six_central_quotient hi a))
  | g2DerivedTwo a =>
    exact Or.inr (Or.inr (Or.inr (g2_core_quotient hi a)))
  | linearFourTwo a =>
    exact (hfour ⟨a⟩).elim

/-- Supply the literal model premise of the parent rank-three assembly.
The two catalogue steps, reconstruction and module contracts remain explicit. -/
theorem source_second_parabolic_rank_three_of_catalogue_steps
    (ha : AlternatingSixReconstructionInput.{u} KnownSimple.IsKnownSimple)
    (hbinary : SourceSecondParabolicBranch hG T hempty hM hunique hmany hcard e hab
      (fun C => Nonempty ((C ⧸ pCore 2 C) ≃* SL(3,ZMod 2))))
    (hsevenModule : SourceSecondParabolicBranch hG T hempty hM hunique hmany hcard e hab
      (fun C => Nonempty ((C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 7))))
    (hg2 : SourceSecondParabolicBranch hG T hempty hM hunique hmany hcard e hab
      (fun C => Nonempty ((C ⧸ pCore 2 C) ≃* commutator (Atlas.G2.Model (ZMod 2))))) :
    SourceSecondParabolicRankThree hG T hempty hM hunique hmany hcard e hab := by
  exact source_second_parabolic_rank_three_of_model_branches
    hG T hempty hM hunique hmany hcard e hab ha
    (source_second_parabolic_models_of_catalogue_steps
      hG T hempty hM hunique hmany hcard e hab hlinear hseven)
    hbinary hsevenModule hg2

omit hlinear hseven in
/-- The complete intrinsic quotient catalogue under the original hypotheses
of 14.6.10(5). Only the six-letter alternative retains a central cover. -/
theorem source_second_parabolic_models :
    SourceSecondParabolicModelInput hG T hempty hM hunique hmany hcard e hab :=
  source_second_parabolic_models_of_catalogue_steps hG T hempty hM hunique hmany hcard e hab
    (linear_exclusion_input hG T hempty hM hunique hmany hcard e hab)
    (SevenKernel.sevenRecoveryInput hG T hempty hM hunique hmany hcard e hab)

omit hlinear hseven in
/-- Apply the completed catalogue to the literal rank-three consumer.
The remaining reconstruction and module premises belong to the parent assembly. -/
theorem source_second_parabolic_rank_three_of_catalogue
    (ha : AlternatingSixReconstructionInput.{u} KnownSimple.IsKnownSimple)
    (hbinary : SourceSecondParabolicBranch hG T hempty hM hunique hmany hcard e hab
      (fun C => Nonempty ((C ⧸ pCore 2 C) ≃* SL(3,ZMod 2))))
    (hsevenModule : SourceSecondParabolicBranch hG T hempty hM hunique hmany hcard e hab
      (fun C => Nonempty ((C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 7))))
    (hg2 : SourceSecondParabolicBranch hG T hempty hM hunique hmany hcard e hab
      (fun C => Nonempty ((C ⧸ pCore 2 C) ≃* commutator (Atlas.G2.Model (ZMod 2))))) :
    SourceSecondParabolicRankThree hG T hempty hM hunique hmany hcard e hab :=
  source_second_parabolic_rank_three_of_model_branches
    hG T hempty hM hunique hmany hcard e hab ha
    (source_second_parabolic_models hG T hempty hM hunique hmany hcard e hab)
    hbinary hsevenModule hg2

end CFSG.Quasithin.Chapter14.Section06
