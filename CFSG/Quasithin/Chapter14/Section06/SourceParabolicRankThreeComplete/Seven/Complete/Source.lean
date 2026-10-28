module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Seven.Reconstruction.Source
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Seven.Exceptional.Source
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Seven.OrdinaryGeometry.Coordinates.Source
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Seven.OrdinaryGeometry.Pair.Source

/-!
# The complete seven-letter source branch

Whole-block reconstruction and the exceptional four-space calculation are
proved inputs. In the ordinary case the whole-module chart is constructed,
and the original moved plane and fixed point determine the orientation of
the two marked parabolics. The resulting six-support vector feeds the
preferred-centralizer and maximal-intersection contradiction.

The cubic-pair recognition retains the literal images and discharges the
last ordinary-module premise. Thus the final source branch has no extra
reconstruction, action, marking or recognition assumptions.
Source: Aschbacher--Smith, original14.6.10(5), printed pp.1029--1030.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06.Seven.Complete
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

/-- The original branch, with reconstruction, coordinates, point orientation
and exceptional rank all discharged. Cubic-pair recognition remains explicit. -/
theorem source_branch_of_cubicRecognition
    (hc : OrdinaryGeometry.Pair.CubicPairRecognition.{u}) :
    SourceSecondParabolicBranch hG T hempty hM hunique hmany hcard e hab
      (fun C => Nonempty ((C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 7))) :=
  source_branch_of_inputs hG T hempty hM hunique hmany hcard e hab
    (Reconstruction.reconstructionInput hG T hempty hM hunique hmany hcard e hab)
    (OrdinaryGeometry.ordinaryGeometryInput_of_pair hG T hempty hM hunique hmany hcard e hab
      (OrdinaryGeometry.Pair.pairInput_of_cubicRecognition
        hG T hempty hM hunique hmany hcard e hab hc))
    (Exceptional.source_rank_input hG T hempty hM hunique hmany hcard e hab)

/-- Reduction's literal hseven consumer. The other catalogue branches remain
with the rank-three assembly owner, qt-e-14610-rank-three. -/
theorem source_rank_three_of_cubicRecognition
    (hc : OrdinaryGeometry.Pair.CubicPairRecognition.{u})
    (ha : AlternatingSixReconstructionInput.{u} KnownSimple.IsKnownSimple)
    (hmodels : SourceSecondParabolicModelInput hG T hempty hM hunique hmany hcard e hab)
    (hbinary : SourceSecondParabolicBranch hG T hempty hM hunique hmany hcard e hab
      (fun C => Nonempty ((C ⧸ pCore 2 C) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))))
    (hg2 : SourceSecondParabolicBranch hG T hempty hM hunique hmany hcard e hab
      (fun C => Nonempty ((C ⧸ pCore 2 C) ≃* commutator (Atlas.G2.Model (ZMod 2))))) :
    SourceSecondParabolicRankThree hG T hempty hM hunique hmany hcard e hab :=
  source_second_parabolic_rank_three_of_model_branches
    hG T hempty hM hunique hmany hcard e hab ha hmodels hbinary
    (source_branch_of_cubicRecognition hG T hempty hM hunique hmany hcard e hab hc) hg2

/-- Construct the entire ordinary geometry on the original component and choice. -/
theorem ordinaryGeometryInput :
    OrdinaryGeometryInput hG T hempty hM hunique hmany hcard e hab :=
  OrdinaryGeometry.ordinaryGeometryInput_of_pair hG T hempty hM hunique hmany hcard e hab
    (OrdinaryGeometry.Pair.pairInput hG T hempty hM hunique hmany hcard e hab)

/-- The exact original alternating-seven branch of 14.6.10(5).
Both ordinary and exceptional whole-block cases are discharged. -/
theorem source_branch :
    SourceSecondParabolicBranch hG T hempty hM hunique hmany hcard e hab
      (fun C => Nonempty ((C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 7))) :=
  source_branch_of_cubicRecognition hG T hempty hM hunique hmany hcard e hab
    OrdinaryGeometry.Pair.cubicPairRecognition

/-- The actual Reduction consumer, with the seven-letter branch fully supplied.
The other catalogue branches retain their original assembly owner. -/
theorem source_rank_three
    (ha : AlternatingSixReconstructionInput.{u} KnownSimple.IsKnownSimple)
    (hmodels : SourceSecondParabolicModelInput hG T hempty hM hunique hmany hcard e hab)
    (hbinary : SourceSecondParabolicBranch hG T hempty hM hunique hmany hcard e hab
      (fun C => Nonempty ((C ⧸ pCore 2 C) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))))
    (hg2 : SourceSecondParabolicBranch hG T hempty hM hunique hmany hcard e hab
      (fun C => Nonempty ((C ⧸ pCore 2 C) ≃* commutator (Atlas.G2.Model (ZMod 2))))) :
    SourceSecondParabolicRankThree hG T hempty hM hunique hmany hcard e hab :=
  source_second_parabolic_rank_three_of_model_branches
    hG T hempty hM hunique hmany hcard e hab ha hmodels hbinary
    (source_branch hG T hempty hM hunique hmany hcard e hab) hg2

end CFSG.Quasithin.Chapter14.Section06.Seven.Complete
