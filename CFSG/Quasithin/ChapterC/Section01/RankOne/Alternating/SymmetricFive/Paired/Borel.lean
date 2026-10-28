module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.ComponentSylowNormalizer
public import Theory.SpecificGroups.Alternating.FiveBorelOvergroups

/-!
# The original alternating-five component Borel is in the maximal local

Restrict the prescribed Sylow subgroup to its actual simple component.
The source component-normalizer theorem places that Sylow normalizer in
the unique maximal overgroup. The fixed original A₅ coordinates identify
it with an even point stabilizer, giving the cubic seed used in paired
C.1.24 without a local placement premise.

Source: Aschbacher--Smith B.6.8(3), C.1.24 and E.2.3(3).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.SymmetricFive.Paired
open ChapterB
variable {G : Type*} [Group G] [Finite G]

theorem source_component_borel
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    {L : Subgroup G} (hL : IsComponent G L)
    (e : L ≃* alternatingGroup (Fin 5)) :
    ∃ i : Fin 5,
      ((MulAction.stabilizer (alternatingGroup (Fin 5)) i).map e.symm.toMonoidHom).map L.subtype ≤
        minimalParabolicMax T hP := by
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup L := e.isSimpleGroup
  have heven : 2 ∣ Nat.card L := by
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  obtain ⟨P,hP₀⟩ := T.exists_subgroupOf_eq_of_subnormal L hL.1
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨i,hi⟩ := Theory.SpecificGroups.Alternating.FiveBorelOvergroups.sylow_normalizer_eq_stabilizer Q
  have heq : (MulAction.stabilizer (alternatingGroup (Fin 5)) i).map e.symm.toMonoidHom =
      normalizer (P : Set L) := by
    rw [←hi]
    change (normalizer ((Q : Subgroup (alternatingGroup (Fin 5))) : Set _)).map e.symm.toMonoidHom = _
    rw [map_equiv_normalizer_eq]
    change normalizer (((P : Subgroup L).map e.toMonoidHom).map e.symm.toMonoidHom : Set L) = _
    have hh : ((P : Subgroup L).map e.toMonoidHom).map e.symm.toMonoidHom = P :=
      e.mapSubgroup.symm_apply_apply P
    rw [hh]
    rfl
  refine ⟨i,?_⟩
  rw [heq]
  apply le_trans _ (component_sylow_normalizer_le_maximal T hP hL heven)
  apply le_inf (map_subtype_le _)
  have hh := Subgroup.le_normalizer_map (H := (P : Subgroup L)) L.subtype
  rw [hP₀,subgroupOf_map_subtype] at hh
  change (normalizer ((P : Subgroup L) : Set L)).map L.subtype ≤ _
  rw [hP₀]
  exact hh
end CFSG.Quasithin.ChapterC.SymmetricFive.Paired
