module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules.PairMarkedAction
/-!
The original marked factor exchange transports to the two literal natural axes in the plus group. Together with the full faithful action, this supplies the paired Baumann theorem on K joined with T_v, preserving the original Baumann image.

Source: Aschbacher--Smith 13.6.14, printed pp.929--930.
-/
public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
open ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives
open ChapterB ChapterB.SourceInduction ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]

theorem pair_marked_baumann_image_source
    (K L T : Subgroup G) (z v : G)
    [IsElementaryAbelian 2 (WK K L T z v)]
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) (hzT : z ∈ Tv T v)
    (hK : K ∈ Yz L T z v)
    (hLv : plusImage K L T z v hL hz (Lv L v) ≤
      plusImage K L T z v hL hz (Kminus K T v))
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (d : SourceTwoFactorCase ((wkRepresentation K L T z v hL hz).comp
      (offenderSubgroup (wkRepresentation K L T z v hL hz)).subtype))
    (F : BinaryField) (c : d.MarkedProduct (linearNatural F 2))
    (hI : offenderSubgroup (wkRepresentation K L T z v hL hz) =
      plusImage K L T z v hL hz (Kminus K T v))
    (t : G) (ht : t ∈ Tv T v)
    (hex : let := offenderSubgroup_normal (wkRepresentation K L T z v hL hz)
      let tA : plusActor K L T v := ⟨t,(show Tv T v ≤ plusActor K L T v from le_sup_right) ht⟩
      d.first.map (MulAut.conjNormal (plusMk K L T z v hL hz tA)).toMonoidHom = d.second ∧
      d.second.map (MulAut.conjNormal (plusMk K L T z v hL hz tA)).toMonoidHom = d.first) :
    plusImage K L T z v hL hz (baumann (Tv T v)) =
      plusImage K L T z v hL hz (Tv T v) ⊓ plusImage K L T z v hL hz (Kminus K T v) := by
  let α := wkRepresentation K L T z v hL hz
  let I := offenderSubgroup α
  let C := plusImage K L T z v hL hz (Kminus K T v)
  let D := Matrix.SpecialLinearGroup (Fin 2) F.Carrier
  let := offenderSubgroup_normal α
  let e := (MulEquiv.subgroupCongr hI.symm).trans c.action.groupEquiv
  obtain ⟨ρ,hρ,he,hres⟩ := pair_marked_full_action_source K L T z v hL hz hK hLv hSylow d F c hI
  apply paired_baumann_image_source K L T z v hK hL hz hzT hLv hSylow F.Carrier e
    ρ hρ hres c.quotientMap c.quotientMap_surjective he hI.le
  let tj : ↥(K ⊔ Tv T v) := ⟨t,(show Tv T v ≤ K ⊔ Tv T v from le_sup_right) ht⟩
  let tA : plusActor K L T v := ⟨t,(show Tv T v ≤ plusActor K L T v from le_sup_right) ht⟩
  have hem : C.subtype.comp e.symm.toMonoidHom =
      I.subtype.comp c.action.groupEquiv.symm.toMonoidHom := by
    ext x
    rfl
  have h₁ : ((⊤ : Subgroup D).prod ⊥).map (C.subtype.comp e.symm.toMonoidHom) =
      d.first.map I.subtype := by rw [hem,←map_map,c.first_eq]
  have h₂ : ((⊥ : Subgroup D).prod ⊤).map (C.subtype.comp e.symm.toMonoidHom) =
      d.second.map I.subtype := by rw [hem,←map_map,c.second_eq]
  have hc : I.subtype.comp (MulAut.conjNormal (plusMk K L T z v hL hz tA)).toMonoidHom =
      (MulAut.conj (joinPlusMap K L T z v hL hz tj)).toMonoidHom.comp I.subtype := by
    ext x
    rfl
  refine ⟨tj,ht,?_,?_⟩
  · rw [h₁,h₂,map_map,←hc,←map_map,hex.1]
  · rw [h₂,h₁,map_map,←hc,←map_map,hex.2]

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
