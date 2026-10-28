module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Seven.Ordinary
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Reduction

/-!
# Assembly of the seven-letter branch of original 14.6.10(5)

Whole-core reconstruction separates the ordinary and exceptional A₇ blocks.
The ordinary partition geometry feeds the proved preferred-centralizer and
maximal-intersection contradiction; the exceptional four-space supplies
rank three. This discharges Reduction's literal hseven argument once those
three independently owned source inputs are proved.

This conditional assembly is not yet the unconditional seven-letter theorem.
Source: Aschbacher--Smith, original14.6.10(5), pp.1029--1030.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06.Seven
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

    (hr : ReconstructionInput hG T hempty hM hunique hmany hcard e hab)
    (ho : OrdinaryGeometryInput hG T hempty hM hunique hmany hcard e hab)
    (hx : ExceptionalRankInput hG T hempty hM hunique hmany hcard e hab)

include hr ho hx

/-- The exact alternating-seven branch, conditional only on its independent
whole-core and marked-module source inputs. -/
theorem source_branch_of_inputs :
    SourceSecondParabolicBranch hG T hempty hM hunique hmany hcard e hab
      (fun C => Nonempty ((C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 7))) := by
  intro H hH d I hI hpreferred he
  rcases hr H hH d I hI he with hb | hb
  · obtain ⟨g⟩ := ho H hH d I hI hb
    exact (ordinary_false_of_geometry hG T hempty hM hunique hmany hcard e hab
      H hH d I hI hpreferred hb g).elim
  · exact hx H hH d I hI hpreferred hb

/-- The literal Reduction consumer, with hseven supplied by this assembly.
The other catalogue and module branches retain their original owners. -/
theorem source_rank_three_of_seven_inputs
    (ha : AlternatingSixReconstructionInput.{u} KnownSimple.IsKnownSimple)
    (hmodels : SourceSecondParabolicModelInput hG T hempty hM hunique hmany hcard e hab)
    (hbinary : SourceSecondParabolicBranch hG T hempty hM hunique hmany hcard e hab
      (fun C => Nonempty ((C ⧸ pCore 2 C) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))))
    (hg2 : SourceSecondParabolicBranch hG T hempty hM hunique hmany hcard e hab
      (fun C => Nonempty ((C ⧸ pCore 2 C) ≃* commutator (Atlas.G2.Model (ZMod 2))))) :
    SourceSecondParabolicRankThree hG T hempty hM hunique hmany hcard e hab := by
  exact source_second_parabolic_rank_three_of_model_branches
    hG T hempty hM hunique hmany hcard e hab ha hmodels hbinary
    (source_branch_of_inputs hG T hempty hM hunique hmany hcard e hab hr ho hx) hg2

end CFSG.Quasithin.Chapter14.Section06.Seven
