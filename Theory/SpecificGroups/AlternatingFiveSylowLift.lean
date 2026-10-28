module
public import Theory.SpecificGroups.AlternatingFiveSolvableSylow
public import Theory.GroupTheory.PCoreSurjective

/-!
# Solvable Sylow overgroups above an A₅ two-core quotient

A solvable overgroup of a Sylow two-subgroup of E normalizes it when
E/O₂(E) is the actual A₅ group. Apply the A₅ Sylow-overgroup theorem to
the quotient image, then lift the normalizer: the quotient kernel lies
in the supplied Sylow subgroup.

Source: the Sylow intersection step in Aschbacher–Smith 13.2.9, p. 880.
-/
public section
open Subgroup
namespace Theory.SpecificGroups
variable {E : Type*} [Group E] [Finite E]

theorem solvable_sylow_overgroup_normalizes_of_alternatingFive_quotient
    (e : (E ⧸ pCore 2 E) ≃* alternatingGroup (Fin 5)) (S : Sylow 2 E)
    (J : Subgroup E) [Group.IsSolvable J] (hSJ : (S : Subgroup E) ≤ J) :
    J ≤ normalizer (S : Set E) := by
  let q := QuotientGroup.mk' (pCore 2 E)
  let P := S.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  let I := J.map q
  let : Group.IsSolvable I := Group.isSolvable_of_surjective (q.subgroupMap_surjective J)
  have hn := alternatingGroup.solvable_sylow_overgroup_le_normalizer_of_equiv e P I
    (map_mono hSJ)
  have hpre : ((S : Subgroup E).map q).comap q = (S : Subgroup E) := by
    rw [comap_map_eq,QuotientGroup.ker_mk',sup_of_le_left (pCore_isPGroup.le_sylow_of_normal S)]
  apply le_normalizer_iff.mpr
  intro j hj s hs
  rw [←hpre]
  exact le_normalizer_iff.mp hn (q j) (mem_map_of_mem q hj)
    (q s) (mem_map_of_mem q hs)
end Theory.SpecificGroups

