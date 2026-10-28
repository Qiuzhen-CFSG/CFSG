module

public import CFSG.Quasithin.Chapter14.Section06.SourceCyclicTrack
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticReduction

/-!
# The original cyclic branch after marked quintic enumeration

The existing source reduction settles index three and supplies index five
in the remaining cyclic case. Given enumeration of that literal quintic
pair, the full Ree exclusion and original rigidity leave the Tits pair,
the corrected Sz(2) quotient, and actual Parrott normalizer/fusion data.

This is a conditional consumer of marked enumeration, not the completion
of original 14.6.12. Ambient recognition from these data remains separate;
neither missing theorem is included in a source hypothesis record.

Source: Aschbacher--Smith 14.6.12(2), printed p.1031, via 14.2.20(1)
and 14.2.21--22, printed pp.988--989.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The original cyclic source, conditional only on enumeration of its actual
index-five pair, reaches the concrete Tits local configuration. Ambient model
recognition is not inferred from the local amalgam marking. -/
theorem source_solvable_minimal_cyclic_model_or_tits_fusion_of_enumeration
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    (hcyc : IsCyclic (pResidual 2 (J ⧸ pCore 2 J)))
    (henum : (T : Subgroup G).relIndex J = 5 →
      ChapterF.GreenBook.IsBinaryReeAmalgam
        (RankTwoAmalgam.ofSubgroups J (J ⊓ (sourceResidual M Mc ⊔ (T : Subgroup G)))
          (sourceResidual M Mc ⊔ (T : Subgroup G)) inf_le_left inf_le_right) ∨
      ChapterF.GreenBook.IsAtlasTitsAmalgam
        (RankTwoAmalgam.ofSubgroups J (J ⊓ (sourceResidual M Mc ⊔ (T : Subgroup G)))
          (sourceResidual M Mc ⊔ (T : Subgroup G)) inf_le_left inf_le_right)) :
    ClassificationModels.IsTheoremEModel G ∨
      (ChapterF.GreenBook.IsAtlasTitsAmalgam
        (RankTwoAmalgam.ofSubgroups J (J ⊓ (sourceResidual M Mc ⊔ (T : Subgroup G)))
          (sourceResidual M Mc ⊔ (T : Subgroup G)) inf_le_left inf_le_right) ∧
      J = Mc ∧ M = sourceResidual M Mc ⊔ (T : Subgroup G) ∧
      J = centralizer (centralInvolutions T : Set G) ∧
      Nonempty ((J ⧸ pCore 2 J) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) ∧
      ∃ z : G, zpowers z = centralInvolutions T ∧
        Recognition.ParrottCentralizerHypotheses z ∧ Recognition.ParrottLocalInputs z ∧
        ∃ d : Recognition.ParrottSecondElementaryData z,
          Nonempty (Recognition.ParrottNormalizerFusionData d)) := by
  rcases source_solvable_minimal_cyclic_model_or_quintic_track
    hG T hempty hM hu hmany hcard e hab J hJ hs hcyc with hm | hq
  · exact Or.inl hm
  · exact Or.inr (Section02.SolvableAmalgam.source_quintic_fusion_of_ree_tits_marks
      hG T hempty hM hu hmany hcard e J hJ (henum hq.1))

end CFSG.Quasithin.Chapter14.Section06
