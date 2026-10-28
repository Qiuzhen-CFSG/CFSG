module
public import Theory.SpecificGroups.SymmetricFive.PentagonNormalizer
public import Theory.GroupTheory.CoprimeNormalizerAutomorphisms
public import Theory.GroupTheory.SylowNormalizerCommutingFamily
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.FiveCore.SourceCompletion.Quaternion
/-!
# The actual H-normalizer of the source five-subgroup

The original Ru₂ quotient map embeds the chosen Sylow five-group. Frattini
lifting transports the full S₅ automizer to its H-normalizer. The literal
centralizer has order40, so kernel and image counting gives normalizer
order160 and the full restricted ambient automorphism action.

All local quaternion data are constructed from the original LocalSetup.
Source: Aschbacher--Smith J.3.6, printed p.439.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.Section03
open Centralizers Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G}
private instance primeFive : Fact (Nat.Prime 5) := ⟨by decide⟩

private theorem B5_card (B5 : Sylow 5 d.toTypeRuSetup.H) : Nat.card B5=5 := by
  rw [B5.card_eq_multiplicity,d.ru2.card_H d.card_Z]
  decide +kernel

private theorem image_subgroupOf (B5 : Sylow 5 d.toTypeRuSetup.H) :
    (B5Image B5).subgroupOf d.toTypeRuSetup.H = (B5 : Subgroup d.toTypeRuSetup.H) := by
  ext b
  constructor
  · rintro ⟨a,ha,he⟩
    exact (Subtype.ext he : a=b) ▸ ha
  · intro hb
    exact ⟨b,hb,rfl⟩

theorem local_five_full_automizer (B5 : Sylow 5 d.toTypeRuSetup.H) :
    Function.Surjective (B5 : Subgroup d.toTypeRuSetup.H).normalizerMonoidHom := by
  let f := d.ru2.quotientMap
  let A := (B5 : Subgroup d.toTypeRuSetup.H)
  let B := A.map f
  have hi := d.toTypeRuSetup.quotientMap_injective_on_odd A (by rw [B5_card B5]; decide)
  let e : A ≃* B := MulEquiv.ofBijective (f.subgroupMap A)
    ⟨fun x y h => hi (congrArg Subtype.val h), f.subgroupMap_surjective A⟩
  have hb : Nat.card B=5 := (Nat.card_congr e.toEquiv).symm.trans (B5_card B5)
  apply normalizerMonoidHom_surjective_of_lift A B f e (fun _ => rfl)
  · exact (B5.normalizer_map_surjective f d.ru2.quotient_surjective).symm.le
  · exact Equiv.Perm.five_subgroup_full_automizer B hb

theorem local_five_full_ambient_action (B5 : Sylow 5 d.toTypeRuSetup.H) :
    Function.Surjective ((B5Image B5).normalizerMonoidHom.comp
      (d.toTypeRuSetup.H.subgroupOf (normalizer (B5Image B5 : Set G))).subtype) := by
  apply normalizerMonoidHom_restrict_surjective _ _ (map_subtype_le _)
  rw [image_subgroupOf]
  exact local_five_full_automizer B5

theorem local_five_normalizer_card (c : Choices d) (B5 : Sylow 5 d.toTypeRuSetup.H) :
    Nat.card (d.toTypeRuSetup.H ⊓ normalizer (B5Image B5 : Set G) : Subgroup G)=160 := by
  obtain ⟨q⟩ := c.fiveQuaternionData_source B5
  let A := (B5 : Subgroup d.toTypeRuSetup.H)
  let C := centralizer (A : Set d.toTypeRuSetup.H)
  have hCm : C.map d.toTypeRuSetup.H.subtype = d.toTypeRuSetup.H ⊓ G5 B5 := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      refine ⟨y.property,?_⟩
      rintro b ⟨a,ha,rfl⟩
      exact congrArg Subtype.val (hy a ha)
    · intro hx
      refine ⟨⟨x,hx.1⟩,?_,rfl⟩
      intro a ha
      exact Subtype.ext (hx.2 a (mem_map_of_mem d.toTypeRuSetup.H.subtype ha))
  have hC : Nat.card C=40 := by
    rw [← card_map_of_injective (K:=C) d.toTypeRuSetup.H.subtype_injective,hCm,q.local_card]
  let : IsCyclic A := isCyclic_of_prime_card (B5_card B5)
  have ha : Nat.card (MulAut A)=4 := by rw [IsCyclic.card_mulAut,B5_card B5]; decide
  have hk : Nat.card A.normalizerMonoidHom.ker=40 := by
    rw [normalizerMonoidHom_ker,
      Nat.card_congr (subgroupOfEquivOfLe (Subgroup.centralizer_le_normalizer (A : Set d.toTypeRuSetup.H))).toEquiv]
    exact hC
  have he := A.normalizerMonoidHom.ker.card_mul_index
  rw [hk,index_ker,MonoidHom.range_eq_top.mpr (local_five_full_automizer B5),card_top,ha] at he
  have hNm : (normalizer (A : Set d.toTypeRuSetup.H)).map d.toTypeRuSetup.H.subtype =
      d.toTypeRuSetup.H ⊓ normalizer (B5Image B5 : Set G) := by
    have hh := subgroupOf_normalizer_eq
      (show B5Image B5 ≤ d.toTypeRuSetup.H from map_subtype_le _)
    rw [image_subgroupOf B5] at hh
    have hm := congrArg (Subgroup.map d.toTypeRuSetup.H.subtype) hh
    rw [subgroupOf_map_subtype] at hm
    exact hm.symm.trans (inf_comm _ _)
  rw [← hNm,card_map_of_injective d.toTypeRuSetup.H.subtype_injective]
  exact he.symm

end CFSG.Quasithin.ChapterJ.Section03
