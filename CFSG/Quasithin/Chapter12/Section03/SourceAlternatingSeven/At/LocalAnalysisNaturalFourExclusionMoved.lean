module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisNaturalFourExclusionMoved
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisNaturalFourExclusionEnlargements

/-!
# LocalAnalysisNaturalFourExclusionMoved at the original ambient group and Sylow subgroup

These are the same source arguments as `LocalAnalysisNaturalFourExclusionMoved`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

public noncomputable section

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02

open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G}

namespace Setup

variable (S : Setup T L V)

theorem four_exists_nonsplit_enlargement_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T)
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G)) :
    let Q := S.fourComponentPointCore z
    ∃ K : Subgroup G,
      S.fourComponentPointPerfect z < K ∧
      Input KnownSimple.IsKnownSimple (S.fourPointCentralizer z) Q (S.fourPointLocal z) K ∧
      KernelConclusion K Q ∧ OffenderConclusion K Q ∧
      (K ⊓ normalizer (V : Set G)).pCoreIn 2 ≤ centralizer (V : Set G) ∧
      V ≤ (⁅starV K Q,K.subgroupOf (K ⊔ Q)⁆).map (K ⊔ Q).subtype ∧
      z ∈ (⁅starV K Q,K.subgroupOf (K ⊔ Q)⁆).map (K ⊔ Q).subtype ⊓
        centralizer (K : Set G) ∧
      (let ρ := starRepresentation K Q
       let J := offenderSubgroup ρ
       starImage K Q K ≤ J ∧
         Nonempty (ChapterC.C27Source.NonsplitMovedConclusion (ρ.comp J.subtype)
           ((starImage K Q K).subgroupOf J))) := by
  obtain ⟨K,hDK,hi,hn,hker,hoff,hcent,hcores,hV,hzK⟩ :=
    S.four_exists_quasisimple_C27_enlargement_at structural escape e hd hz hz1 hzT
  have he := S.four_overcomponent_star_moved_eq_at structural e hd hz hz1 hzT hi.component hDK.le
  have hzstar : z ∈ (⁅starV K (S.fourComponentPointCore z),
      K.subgroupOf (K ⊔ S.fourComponentPointCore z)⁆).map
        (K ⊔ S.fourComponentPointCore z).subtype ⊓ centralizer (K : Set G) := by
    rwa [he]
  refine ⟨K,hDK,hi,hker,hoff,hcent,?_,hzstar,
    ChapterC.C27Source.star_moved_nonsplit_of_fixed_point hi hz1 hzstar⟩
  rwa [he]

end Setup

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

