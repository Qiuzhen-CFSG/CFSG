module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldMarkedQuotient
public import Theory.GroupTheory.ExtraspecialDihedralElementaryOverlap
public import Theory.GroupTheory.EmbeddedCenterMap

/-!
# Original module overlap with the marked extraspecial kernel

The same full dihedral quotient fixes the original overlap: U meets its
extraspecial kernel P in an elementary sixteen, containing Z(P), and U
has image an elementary four. The intersection is self-centralizing in P,
and consequently C_P(U)=U∩P as well. No model-only overlap is substituted
for the original U.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

public theorem original_tripleSix_escaping_marked_core_overlap
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t≠1)
    (heven : 2∣(centralizer ({(t:G)} : Set G)).relIndex K)
    (hout : ¬centralizer ({(t:G)} : Set G)≤normalizer (K : Set G)) :
    ∃ π : T→*DihedralGroup 4, Function.Surjective π ∧
      let P := π.ker.map (T : Subgroup G).subtype
      P≤(T : Subgroup G) ∧ (T : Subgroup G)≤normalizer (P : Set G) ∧
        Nat.card P=128 ∧ IsExtraspecial 2 P ∧
        Nonempty (P≃*DihedralCentralProductThree.Model) ∧
        Nat.card (U⊓P : Subgroup G)=16 ∧ Nat.card ((U.subgroupOf T).map π)=4 ∧
        centerIn P≤U ∧ P⊓centralizer (U⊓P : Set G)=U⊓P ∧
        P⊓centralizer (U : Set G)=U⊓P := by
  obtain ⟨π,hπ,hPT,hTP,hPc,hEx,_,hmodel⟩ :=
    original_tripleSix_escaping_marked_dihedral_quotient h structural D a t ht heven hout
  let P := π.ker.map (T : Subgroup G).subtype
  let U₀ := U.subgroupOf T
  let eP := π.ker.equivMapOfInjective (T : Subgroup G).subtype (T : Subgroup G).subtype_injective
  let : IsExtraspecial 2 P := hEx
  let : IsExtraspecial 2 π.ker := IsExtraspecial.of_mulEquiv eP.symm hEx
  let := D.elementary
  let : IsElementaryAbelian 2 U₀ := IsElementaryAbelian.subgroupOf D.le_sylow
  have hQc : Nat.card π.ker=128 := (Nat.card_congr eP.toEquiv).trans hPc
  have hUc : Nat.card U₀=64 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe D.le_sylow).toEquiv]
    exact (Nat.card_congr (tripleSixPointCoordinates D a).toEquiv).trans Atlas.Codes.hexacode_card
  obtain ⟨hI,hIU,hZ,_⟩ := extraspecial_dihedral_elementary_overlap π hQc U₀ hUc
  have hmap : (U₀⊓π.ker : Subgroup T).map (T : Subgroup G).subtype=U⊓P := by
    rw [Subgroup.map_inf _ _ _ (T : Subgroup G).subtype_injective,
      map_subgroupOf_eq_of_le D.le_sylow]
  have hIc : Nat.card (U⊓P : Subgroup G)=16 := by
    rw [←hmap,card_map_of_injective (T : Subgroup G).subtype_injective]
    exact hI
  have hZU : centerIn P≤U := by
    rw [centerIn_eq_map_center,←map_embeddedCenter π.ker (T : Subgroup G).subtype
      (T : Subgroup G).subtype_injective]
    exact (map_mono hZ).trans_eq (map_subgroupOf_eq_of_le D.le_sylow)
  let I := U⊓P
  let A := I.subgroupOf P
  let : IsElementaryAbelian 2 I := IsElementaryAbelian.of_injective
    (inclusion inf_le_left) (inclusion_injective _)
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.subgroupOf inf_le_right
  have hAc : Nat.card A=16 :=
    (Nat.card_congr (subgroupOfEquivOfLe (show I≤P from inf_le_right)).toEquiv).trans hIc
  have hZA : center P≤A := by
    intro z hz
    exact ⟨hZU (by rw [centerIn_eq_map_center]; exact mem_map_of_mem _ hz),z.property⟩
  have hCA : centralizer (A : Set P)=A :=
    extraspecial_two_centralizer_eq_of_card_sq A hZA (by rw [hAc,hPc]; norm_num)
  have hCI : P⊓centralizer (I : Set G)=I := by
    apply le_antisymm
    · intro x hx
      have hh : (⟨x,hx.1⟩:P)∈centralizer (A : Set P) := by
        intro y hy
        exact Subtype.ext (hx.2 y.val hy)
      rw [hCA] at hh
      exact hh
    · exact le_inf inf_le_right (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  have hCU : P⊓centralizer (U : Set G)=I := by
    apply le_antisymm ((inf_le_inf_left P (centralizer_le inf_le_left)).trans_eq hCI)
    exact le_inf inf_le_right (inf_le_left.trans U.le_centralizer)
  exact ⟨π,hπ,hPT,hTP,hPc,hEx,hmodel,hIc,hIU,hZU,hCI,hCU⟩

end CFSG.Quasithin.Chapter12.Section07
