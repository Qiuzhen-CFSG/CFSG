module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.AlternatingSix

/-!
# Assembly of the remaining original second-parabolic branches

The catalogue comparison and the binary-linear, alternating-seven and G₂
module branches have independent contracts. Whole-core A₆ reconstruction
discharges that branch through the original exceptional-cover exclusion and
the completed alternating-six calculation. The assembled rank-three result
feeds the literal terminal rank contradiction while retaining its witness.

The four source contracts and A₆ reconstruction are explicit prerequisites;
this conditional assembly does not assert original 14.6.10(5) without them.
Source: Aschbacher--Smith, printed pp.1029--1030, 1036--1037 and 1042.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
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
    (ha : AlternatingSixReconstructionInput.{u} KnownSimple.IsKnownSimple)
    (hmodels : SourceSecondParabolicModelInput hG T hempty hM hunique hmany hcard e hab)
    (hbinary : SourceSecondParabolicBranch hG T hempty hM hunique hmany hcard e hab
      (fun C => Nonempty ((C ⧸ pCore 2 C) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))))
    (hseven : SourceSecondParabolicBranch hG T hempty hM hunique hmany hcard e hab
      (fun C => Nonempty ((C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 7))))
    (hg2 : SourceSecondParabolicBranch hG T hempty hM hunique hmany hcard e hab
      (fun C => Nonempty ((C ⧸ pCore 2 C) ≃* commutator (Atlas.G2.Model (ZMod 2)))))

include ha hmodels hbinary hseven hg2

/-- The four literal quotient rows give the unchanged rank-three contract.
The A₆ row includes its central cover and uses whole-core reconstruction. -/
theorem source_second_parabolic_rank_three_of_model_branches :
    SourceSecondParabolicRankThree hG T hempty hM hunique hmany hcard e hab := by
  intro H hH d I hI hpreferred
  rcases hmodels H hH d I hI with hb | ha6 | h7 | hg
  · exact hbinary H hH d I hI hpreferred hb
  · exact source_second_parabolic_a6_rank_three_of_reconstruction
      hG T hempty hM hunique hmany hcard e hab ha H hH d I hI hpreferred ha6
  · exact hseven H hH d I hI hpreferred h7
  · exact hg2 H hH d I hI hpreferred hg

/-- The actual terminal consumer, with its rank-three argument assembled
from the remaining independent source branches and its witness kept explicit. -/
theorem source_terminal_contradiction_of_model_branches
    (hwitness : SourceTerminalWitness hG T hempty hM hunique hmany hcard e hab) : False := by
  exact source_terminal_contradiction hG T hempty hM hunique hmany hcard e hab
    (source_second_parabolic_rank_three_of_model_branches
      hG T hempty hM hunique hmany hcard e hab ha hmodels hbinary hseven hg2) hwitness

end CFSG.Quasithin.Chapter14.Section06
