module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Binary.SourceComplete
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Catalogue.Source
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Seven.Complete.Source
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.G2.Source
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.G2Reconstruction.Source

/-!
# Original second-parabolic rank three, reduced only to A₆ reconstruction

The actual quotient catalogue, binary envelope argument and both seven-letter
module cases are proved. The G₂ branch uses the proved whole-core reconstruction.
Their assembly leaves only the independently owned A₆ whole-core reconstruction
explicit, including its central-cover alternative. The literal terminal consumer
retains SourceTerminalWitness, which belongs to the final 14.6.25 assembly.

The A₆ input is produced by qt-e-ms-small-a6-reconstruction. Its final discharge
remains with qt-e-14610-rank-three and qt-e-14625-source; this conditional result
does not claim completion of original 14.6.10(5).
Source: Aschbacher--Smith, original 14.6.10(5), printed pp.1028--1030,
and the terminal rank contradiction on pp.1036--1037, 1042.
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

/-- The G₂ source branch with whole-core reconstruction discharged. -/
theorem source_second_parabolic_g2_rank_three_complete :
    SourceSecondParabolicBranch hG T hempty hM hunique hmany hcard e hab
      (fun C => Nonempty ((C ⧸ pCore 2 C) ≃* commutator (Atlas.G2.Model (ZMod 2)))) :=
  source_second_parabolic_g2_rank_three_of_reconstruction
    hG T hempty hM hunique hmany hcard e hab g2Reconstruction_knownSimple

/-- All actual quotient and module branches are discharged except the
independently owned natural-or-central-cover A₆ whole-core reconstruction. -/
theorem source_second_parabolic_rank_three_of_a6_reconstruction
    (ha : AlternatingSixReconstructionInput.{u} KnownSimple.IsKnownSimple) :
    SourceSecondParabolicRankThree hG T hempty hM hunique hmany hcard e hab :=
  source_second_parabolic_rank_three_of_model_branches
    hG T hempty hM hunique hmany hcard e hab ha
    (source_second_parabolic_models hG T hempty hM hunique hmany hcard e hab)
    (source_second_parabolic_binary_rank_three_complete
      hG T hempty hM hunique hmany hcard e hab)
    (Seven.Complete.source_branch hG T hempty hM hunique hmany hcard e hab)
    (source_second_parabolic_g2_rank_three_complete
      hG T hempty hM hunique hmany hcard e hab)

/-- The terminal rank contradiction now requires only A₆ reconstruction and
the original terminal witness, with no universal linear-three classifier. -/
theorem source_terminal_contradiction_of_a6_reconstruction
    (ha : AlternatingSixReconstructionInput.{u} KnownSimple.IsKnownSimple)
    (hwitness : SourceTerminalWitness hG T hempty hM hunique hmany hcard e hab) : False :=
  source_terminal_contradiction hG T hempty hM hunique hmany hcard e hab
    (source_second_parabolic_rank_three_of_a6_reconstruction
      hG T hempty hM hunique hmany hcard e hab ha) hwitness

end CFSG.Quasithin.Chapter14.Section06
