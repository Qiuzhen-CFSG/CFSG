module
public import Theory.Representation.PSL3Two.NaturalDualNonFF
public import Theory.SpecificGroups.PSL3Two.Automorphisms.OuterOrder

/-!
# The literal inner actor of a binary linear-three marking

Pull the inner automorphism group back to the original ambient group.
Centerlessness gives its unique SL₃(2) actor, and the outer group of order
two bounds the stabilizer index. If the marked component supplies all inner
automorphisms, this actor is surjective. These are the support stabilizer
and actor used in Aschbacher--Smith 14.6.24(3), printed p.1041.
-/

@[expose] public noncomputable section
open Subgroup
namespace BinaryLinearThree.NaturalDual
variable {G : Type*} [_root_.Group G] (H : Subgroup G) (α : H →* MulAut Group)

def innerPreimage : Subgroup G :=
  ((MulAut.innerSubgroup Group).comap α).map H.subtype

theorem innerPreimage_le : innerPreimage H α ≤ H := map_subtype_le _

theorem mem_innerPreimage (x : H) :
    (x : G) ∈ innerPreimage H α ↔ α x ∈ MulAut.innerSubgroup Group := by
  change (H.subtype x) ∈ ((MulAut.innerSubgroup Group).comap α).map H.subtype ↔ _
  rw [mem_map_iff_mem H.subtype_injective]
  rfl

/-- Conjugation identifies the centerless component with its inner automorphisms. -/
def innerConjEquiv : Group ≃* MulAut.innerSubgroup Group :=
  MonoidHom.ofInjective (MulAut.conj_injective_of_center_eq_bot Matrix.PSL3Two.center_eq_bot)

def innerActor : innerPreimage H α →* Group :=
  innerConjEquiv.symm.toMonoidHom.comp
    ((α.comp (inclusion (innerPreimage_le H α))).codRestrict
      (MulAut.innerSubgroup Group) (fun a =>
        (mem_innerPreimage H α (inclusion (innerPreimage_le H α) a)).mp a.property))

theorem conj_innerActor (a : innerPreimage H α) :
    MulAut.conj (innerActor H α a) = α (inclusion (innerPreimage_le H α) a) := by
  exact congrArg (MulAut.innerSubgroup Group).subtype (innerConjEquiv.apply_symm_apply _)

theorem innerActor_surjective (hα : MulAut.innerSubgroup Group ≤ α.range) :
    Function.Surjective (innerActor H α) := by
  intro g
  obtain ⟨a,ha⟩ := hα (show MulAut.conj g ∈ MulAut.innerSubgroup Group from ⟨g,rfl⟩)
  have ham : (a : G) ∈ innerPreimage H α :=
    (mem_innerPreimage H α a).mpr (ha ▸ ⟨g,rfl⟩)
  refine ⟨⟨a,ham⟩,?_⟩
  apply MulAut.conj_injective_of_center_eq_bot Matrix.PSL3Two.center_eq_bot
  exact (conj_innerActor H α ⟨a,ham⟩).trans ha

theorem innerPreimage_relIndex_dvd_two : (innerPreimage H α).relIndex H ∣ 2 := by
  have he : (innerPreimage H α).subgroupOf H = (MulAut.innerSubgroup Group).comap α :=
    comap_map_eq_self_of_injective H.subtype_injective _
  change ((innerPreimage H α).subgroupOf H).index ∣ 2
  rw [he,index_comap]
  have hc : (MulAut.innerSubgroup Group).index = 2 :=
    Matrix.PSL3Two.Automorphisms.card_outer_sl
  exact (relIndex_dvd_index_of_normal (H := MulAut.innerSubgroup Group) (K := α.range)).trans
    (dvd_of_eq hc)

/-- The natural actor has the same rank as the original marked inner image. -/
theorem innerActor_image_rank (B : Subgroup G) (hB : B ≤ innerPreimage H α) :
    Representation.BinaryOffender.rank ((B.subgroupOf (innerPreimage H α)).map
      (innerActor H α)) = Representation.BinaryOffender.rank ((B.subgroupOf H).map α) := by
  have hm : (((B.subgroupOf (innerPreimage H α)).map (innerActor H α)).map
      (MulAut.conj : Group →* MulAut Group)) = (B.subgroupOf H).map α := by
    rw [map_map]
    ext x
    constructor
    · rintro ⟨b,hb,rfl⟩
      exact ⟨inclusion (innerPreimage_le H α) b,hb,(conj_innerActor H α b).symm⟩
    · rintro ⟨b,hb,rfl⟩
      exact ⟨⟨b,hB hb⟩,hb,conj_innerActor H α ⟨b,hB hb⟩⟩
  rw [←hm]
  exact (Representation.BinaryOffender.rank_map_injective (MulAut.conj : Group →* MulAut Group)
    (MulAut.conj_injective_of_center_eq_bot Matrix.PSL3Two.center_eq_bot) _).symm

end BinaryLinearThree.NaturalDual
