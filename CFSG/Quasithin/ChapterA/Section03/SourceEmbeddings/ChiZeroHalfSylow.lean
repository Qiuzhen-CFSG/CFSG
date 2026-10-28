module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.ChiZero
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Restriction
public import Theory.SpecificGroups.PSL2.BinaryHalfSylowOvergroups
public import Theory.GroupTheory.HalfSylowOvergroupSolvability

/-!
# Local component rigidity from half a Sylow in χ₀

A proper nonsolvable subgroup of a binary rank-one group has index divisible
by four. The alternating-five and cubic quotient alternatives have no proper
nonsolvable subgroup. These tests lift through the two-core of a χ₀ block.

Intersect the actual Sylow and its subgroup of index at most two with the
containing component. The original local component remains a component after
adjoining this intersection. Its join is nonsolvable and cannot have index
divisible by four, so it equals the containing group. C-component minimality
then gives equality of the two original components.

This is the non-enlargement step in the starred claim of Aschbacher–Smith
2.4.25, printed p.542. The half-Sylow premise is retained explicitly.
-/

public section
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- Proper subgroups of a χ₀ block containing half a Sylow are solvable. -/
theorem chiZero_solvable_of_not_four_dvd_index (h : ChapterC.IsChiZeroBlock G)
    (D : Subgroup G) (hne : D ≠ ⊤) (hi : ¬ 4 ∣ D.index) : Group.IsSolvable D := by
  apply solvable_of_not_four_dvd_index_of_twoCore_quotient h.chi.short.twoPerfect ?_ D hne hi
  intro J hJ hns
  rcases h with ⟨n,hn,_,F,_,_,hF,_,hmodel⟩ | h | h
  · let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    obtain ⟨e⟩ := hmodel.quotient_iso
    let e' := e.trans (Theory.PSL2.sl2QuotientEquiv F)
    have hproper : J.map e'.toMonoidHom ≠ ⊤ := by
      intro he
      apply hJ
      exact (map_injective e'.injective) (he.trans (map_top_of_surjective _ e'.surjective).symm)
    have hns' : ¬ Group.IsSolvable (J.map e'.toMonoidHom) := by
      intro hs
      let := hs
      exact hns (Group.isSolvable_of_isSolvable_injective
        (f := (J.equivMapOfInjective e'.toMonoidHom e'.injective).toMonoidHom)
        (J.equivMapOfInjective e'.toMonoidHom e'.injective).injective)
    simpa only [index_map_of_bijective (f := e'.toMonoidHom) e'.bijective] using Theory.PSL2.binary_four_dvd_index_of_nonsolvable
      (by omega : 0 < n) hF (J.map e'.toMonoidHom) hproper hns'
  · obtain ⟨e⟩ := h.2.2.quotient_iso
    let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
    let : Group.IsSolvable (G ⧸ pCore 2 G) :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    exact (hns inferInstance).elim
  · obtain ⟨e⟩ := h.2.2.quotient_iso
    exact (hns (alternatingGroup.isSolvable_subgroup_of_equiv_five e J hJ)).elim

/-- Local component rigidity in a χ₀ component for the original half-Sylow actor. -/
theorem eq_of_chiZero_containing_component_half_sylow
    (T : Sylow 2 G) {R B L : Subgroup G}
    (hRT : R ≤ T) (hi : R.relIndex T ≤ 2)
    (hB : B ∈ localCComponents R) (hL : L.IsCComponent) (hBL : B ≤ L)
    (hmodel : ChapterC.IsChiZeroBlock L) : B = L := by
  obtain ⟨S,hS⟩ := T.exists_subgroupOf_eq_of_subnormal L hL.subnormal
  have hRS : R.subgroupOf L ≤ (S : Subgroup L) := by
    rw [hS]
    exact comap_mono hRT
  have hidx : (R.subgroupOf L).relIndex S ≤ 2 := by
    change (R.comap L.subtype).relIndex (S : Subgroup L) ≤ 2
    rw [relIndex_comap,hS,subgroupOf_map_subtype]
    exact (relIndex_le_of_le_right inf_le_left index_ne_zero_of_finite).trans hi
  let J : Subgroup L := B.subgroupOf L ⊔ R.subgroupOf L
  have hBJ : ((B.subgroupOf L).subgroupOf J).IsCComponent := local_restrict hB hBL
  have htop : J = ⊤ := by
    by_contra hne
    let := chiZero_solvable_of_not_four_dvd_index hmodel J hne
      (not_four_dvd_index_of_half_sylow S hRS hidx le_sup_right)
    exact hBJ.not_isSolvable inferInstance
  have hBC : (B.subgroupOf L).IsCComponent := by
    rw [htop] at hBJ
    have hh := hBJ.map_equiv (topEquiv : (⊤ : Subgroup L) ≃* L)
    change (((B.subgroupOf L).subgroupOf ⊤).map (⊤ : Subgroup L).subtype).IsCComponent at hh
    simpa only [map_subgroupOf_eq_of_le le_top] using hh
  exact le_antisymm hBL (subgroupOf_eq_top.mp (hL.eq_top_of_isCComponent hBC))
end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
