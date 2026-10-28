module

public import CFSG.Quasithin.Chapter14.Section06.SourceCyclicRecognition
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticEnumeration

/-!
# The cyclic source consumer of the two endpoint identification theorems

First-endpoint enumeration and identification of the cubic partner in the
Tits case supply the literal marked-enumeration input of
`source_solvable_minimal_cyclic_model_or_tits_fusion_of_enumeration`.
The original cyclic hypotheses and the chosen subgroup J are unchanged.
Both endpoint premises remain explicit pending their structural proofs;
neither this conditional consumer nor the marking reduction is a proof
of unconditional quintic enumeration or ambient recognition.

Source: Aschbacher--Smith14.6.12(2), p.1031, using14.2.20--22, pp.988--989.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The actual cyclic consumer now needs only the two structural endpoint
theorems. The whole-overlap marking is constructed by the reduction. -/
theorem source_solvable_minimal_cyclic_model_or_tits_fusion_of_endpoints
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
    (hfirst : (T : Subgroup G).relIndex J = 5 →
      Nonempty (Tits.ExceptionalParabolics.FullRee.first ≃* J) ∨
      Nonempty (Tits.ExceptionalParabolics.first ≃* J))
    (hsecond : (T : Subgroup G).relIndex J = 5 →
      Nonempty (Tits.ExceptionalParabolics.first ≃* J) →
      Nonempty (Tits.ExceptionalParabolics.second ≃*
        (sourceResidual M Mc ⊔ (T : Subgroup G) : Subgroup G))) :
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
  apply source_solvable_minimal_cyclic_model_or_tits_fusion_of_enumeration
    hG T hempty hM hu hmany hcard e hab J hJ hs hcyc
  intro hi
  exact Section02.SolvableAmalgam.source_quintic_enumeration_of_endpoint_identifications
    hG T hempty hM hu hmany hcard e J hJ hi (hfirst hi) (hsecond hi)

end CFSG.Quasithin.Chapter14.Section06
