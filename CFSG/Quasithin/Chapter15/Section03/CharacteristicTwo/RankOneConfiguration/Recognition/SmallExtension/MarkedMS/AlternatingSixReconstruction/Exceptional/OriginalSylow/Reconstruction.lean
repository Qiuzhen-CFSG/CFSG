module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.DistanceFourTerminal

/-!
# Exceptional whole-core reconstruction at original Sylow pairs

The original Sylow witness excludes the plane image. The remaining Borel
image has distance four and is excluded by the actual even-cover action on
the moving central quotient. This exhausts the original commutator core.
The existing faithful FF recognition then supplies all five intrinsic core
clauses and the unchanged C.1.32 alternatives, including relative blockhood.

Source: MS93 (5.12) and Section 7; Aschbacher--Smith C.1.32(4).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.OriginalSylow
open Exhaustion
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R)
  (e : CentralMarking L) (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hSyl : Chapter1.IsSylowIn 2 R (L ⊔ R))

include h e hz hSyl

/-- All larger distances and the nonsylow plane have already been excluded;
the terminal Borel contradiction therefore exhausts the original core. -/
theorem coreExhaustion : CoreExhaustion L R := by
  rcases coreExhaustion_or_borel_distance_four h e hz hSyl with
    hx | ⟨hk, _, _, _, u, hR⟩
  · exact hx
  · exact (borel_four_impossible h e hz hk u hR).elim

/-- Existing recognition supplies all five clauses on the whole intrinsic core. -/
theorem core_facts :
    IsElementaryAbelian 2 (ChapterC.blockU L) ∧
      ChapterC.blockU L ≤ centralizer (pCore 2 L : Set L) ∧
      ChapterC.BlockModuleIrreducible L ∧
      Nat.card (ChapterC.blockU L) = 2 ^ 6 ∧
      centralizer (ChapterC.blockU L : Set L) = pCore 2 L :=
  core_facts_of_exhaustion h e hz
    (coreExhaustion h e hz hSyl)

/-- The cubic center selects the exceptional alternative in the unchanged
whole-core reconstruction structure. -/
theorem reconstruction : AlternatingSixReconstruction L := by
  obtain ⟨he, hc, hi, hu, hf⟩ := core_facts h e hz hSyl
  exact ⟨he, hc, hi, Or.inr ⟨hz, hu, hf⟩⟩

/-- The exact five-way C.1.32 output, with relative blockhood supplied by
the original small MS pair. -/
theorem rankTwo : RankTwoAlternatives L R :=
  h.rankTwo_of_alternatingSix_reconstruction e
    (reconstruction h e hz hSyl)


end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
