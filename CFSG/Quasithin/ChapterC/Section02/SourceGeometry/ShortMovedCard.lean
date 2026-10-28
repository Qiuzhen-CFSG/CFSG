module
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Omega
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.BlockKernel
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.BlockRigidity.Commutation.ShortTransport

/-!
# Bounding the intrinsic block module by the literal moved star subgroup

For a short component normalized by R, the omega-center commutator in LR
is the embedded intrinsic layer U(L). Transport through the original
subgroup inclusion preserves its order, and the central quotient Ũ(L)
has no larger order. This comparison does not identify an arbitrary
isomorphic representation with the block module.

The fixed A₇ consumer uses the proved order 64 of the original moved
subgroup. Source: Aschbacher--Smith C.1.7--11 and C.2.7, pp.123--124,145.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction
variable {G : Type*} [Group G] [Finite G]

theorem blockModule_card_le_star_moved_of_short (L R : Subgroup G)
    (hn : R ≤ normalizer (L : Set G)) (hs : IsShort L) :
    Nat.card (BlockModule L) ≤
      Nat.card (⁅starV L R,L.subgroupOf (L ⊔ R)⁆ : Subgroup (L ⊔ R : Subgroup G)) := by
  let J := L ⊔ R
  let C := L.subgroupOf J
  let e : C ≃* L := subgroupOfEquivOfLe (show L ≤ J from le_sup_left)
  let : C.Normal := normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer hn)
  have hb : IsBlock C := ⟨inferInstance,hs.of_mulEquiv e.symm,(inferInstance : C.Normal).isSubnormal⟩
  have he := BlockOmega.omega_commutator hb
  change ⁅starV L R,C⁆ = (blockU C).map C.subtype at he
  have hmap : (blockU C).map e.toMonoidHom = blockU L := by
    rw [blockU,map_commutator,pCore_map_iso,map_top_of_surjective _ e.surjective,blockU]
  calc
    Nat.card (BlockModule L) ≤ Nat.card (blockU L) :=
      Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective (blockFixed L))
    _ = Nat.card (blockU C) := by rw [←hmap,card_map_of_injective e.injective]
    _ = Nat.card ((blockU C).map C.subtype) := (card_map_of_injective C.subtype_injective).symm
    _ = Nat.card (⁅starV L R,C⁆ : Subgroup J) := congrArg Nat.card (congrArg (fun A : Subgroup J => ↥A) he.symm)
end CFSG.Quasithin.ChapterC.C27Source
