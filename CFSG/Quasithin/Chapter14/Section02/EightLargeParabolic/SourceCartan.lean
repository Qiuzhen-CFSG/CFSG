module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourcePathProfile
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.ReducedCartan

/-!
# The actual full source Cartan has order seven

The original Borel has exactly T as two-core and index seven over T.
Its compatible full Cartan is a complement, so its universal image has
order seven. This retains the original full middle and prescribed Cartan.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceCartan
open ChapterF.Source ChapterF.Source.SuzukiContainment ChapterF.Source.DGS85.OriginalExtension
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.ReducedCartan
variable {G : Type*} [Group G]

private theorem cartan_card_eq_index {L : Fin 2 → Subgroup G} {S : Subgroup G}
    (c : CompatibleCartans L (reducedSylow L S)) :
    Nat.card (cartan c) = (reducedSylow L S).relIndex
      (commonBorel L (reducedSylow L S)) := by
  rw [cartan, card_map_of_injective middleMap_injective]
  exact c.joint_complement.symm.index_eq_card.symm

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (eR : (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃* Theory.PSL2.BinaryGroup 3)
include hG hempty hM hu hmany hcard e hH eR

/-- Every prescribed compatible full Cartan of the original reversed source
has order seven in the literal universal amalgam. -/
theorem source_cartan_order
    (c : CompatibleCartans ![locals T M Mc H 1,locals T M Mc H 0]
      (reducedSylow ![locals T M Mc H 1,locals T M Mc H 0] (T : Subgroup G))) :
    Nat.card (cartan c) = 7 := by
  let L := ![locals T M Mc H 1,locals T M Mc H 0]
  have hB : commonBorel L (T : Subgroup G) = H ⊓ M := by
    change borel (locals T M Mc H 1) (T : Subgroup G) ⊔
      borel (locals T M Mc H 0) (T : Subgroup G) ⊔ (T : Subgroup G) = _
    rw [sup_comm (borel (locals T M Mc H 1) (T : Subgroup G))
      (borel (locals T M Mc H 0) (T : Subgroup G))]
    exact (source_parabolics hG T hempty hM hu hmany hcard e H hH eR).2.2.1
  have hS : reducedSylow L (T : Subgroup G) = (T : Subgroup G) := by
    change (commonBorel L (T : Subgroup G)).pCoreIn 2 = _
    rw [hB]
    exact source_borel_twoCore hG T hempty hM hu hmany hcard e H hH eR
  rw [cartan_card_eq_index]
  change (reducedSylow L (T : Subgroup G)).relIndex
    (commonBorel L (reducedSylow L (T : Subgroup G))) = 7
  rw [hS,hB]
  exact source_sylow_index_borel hG T hempty hM hu hmany hcard e H hH eR

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceCartan
