module
public import Theory.SpecificGroups.SymmetricFive.WreathComponents
public import Theory.GroupTheory.IndexTwoIntersection

/-!
# Components through a symmetric-five wreath two-core quotient

The actual quotient map identifies each component modulo its own two-core
with its image. Solvable-kernel component lifting preserves normalizers,
so the concrete wreath calculation gives their index two. Every Sylow
two-subgroup crosses this index-two normalizer. The wreath radical is a
two-group, hence trivial in the two-core quotient; the original radical
therefore equals the original two-core.

Source: Aschbacher--Smith 15.2.4, printed p.1106.
-/

public section
open Subgroup Theory.GroupTheory
namespace Theory.SpecificGroups.SymmetricFive.WreathComponents
variable {D : Type*} [Group D] [Finite D]

omit [Finite D] in
theorem wreath_quotient_not_solvable (e : (D ⧸ pCore 2 D) ≃* W) :
    ¬ Group.IsSolvable D := by
  intro hs
  let := hs
  exact not_solvable (Group.isSolvable_of_surjective
    (f := e.toMonoidHom.comp (QuotientGroup.mk' _))
    (e.surjective.comp (QuotientGroup.mk'_surjective _)))

theorem wreath_quotient_radical (e : (D ⧸ pCore 2 D) ≃* W) :
    solvableRadical D = pCore 2 D := by
  have hw : pCore 2 W = ⊥ := by
    rw [← pCore_map_iso 2 e,pCore_quotient_pCore_eq_bot,Subgroup.map_bot]
  have hrad : solvableRadical (D ⧸ pCore 2 D) = ⊥ := by
    apply (map_eq_bot_iff_of_injective _ (f := e.toMonoidHom) e.injective).mp
    rw [map_solvableRadical_equiv,radical_eq_bot_of_twoCore hw]
  have hle := map_solvableRadical_le_of_surjective (QuotientGroup.mk' (pCore 2 D))
    (QuotientGroup.mk'_surjective _)
  rw [hrad,le_bot_iff,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk'] at hle
  apply le_antisymm hle
  let : Group.IsNilpotent (pCore 2 D) := pCore_isPGroup.isNilpotent
  exact le_solvableRadical _ inferInstance inferInstance

theorem wreath_quotient_component (e : (D ⧸ pCore 2 D) ≃* W)
    {K : Subgroup D} (hK : K.IsCComponent) :
    Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) ∧
      (normalizer (K : Set D)).index = 2 := by
  let q := QuotientGroup.mk' (pCore 2 D)
  let L := K.map q
  let : Group.IsNilpotent (pCore 2 D) := pCore_isPGroup.isNilpotent
  have hL : L.IsCComponent := hK.map_quotient _
  obtain ⟨a⟩ := component_equiv (hL.map_equiv e)
  refine ⟨⟨(cComponentTwoCoreQuotientEquiv hK).trans ((e.subgroupMap L).trans a)⟩,?_⟩
  have hi := component_normalizer_index (hL.map_equiv e)
  rw [← map_equiv_normalizer_eq L e,index_map_of_bijective e.bijective] at hi
  exact (cComponent_normalizer_index_quotient hK (pCore 2 D)).symm.trans hi

theorem wreath_quotient_sylow_component_index (e : (D ⧸ pCore 2 D) ≃* W)
    (S : Sylow 2 D) {K : Subgroup D} (hK : K.IsCComponent) :
    ((S : Subgroup D) ⊓ normalizer (K : Set D)).relIndex S = 2 := by
  have hi := (wreath_quotient_component e hK).2
  rw [inf_relIndex_left]
  apply subgroupOf_index_eq_two _ _ hi
  intro h
  have hd := index_dvd_of_le h
  rw [hi] at hd
  exact S.not_dvd_index hd

end Theory.SpecificGroups.SymmetricFive.WreathComponents
