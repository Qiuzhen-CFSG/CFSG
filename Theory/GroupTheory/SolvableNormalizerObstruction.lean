module

public import Theory.GroupTheory.PCoreImage
public import Theory.Quasithin
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.GroupTheory.Solvable

/-!
# A solvable normalizer obstruction in a simple two-core quotient

Maximal two-locality first places a normalized solvable subgroup inside the
local group: its nontrivial two-core has a two-local normalizer. Its image
in the nonsolvable simple quotient is then a solvable normal subgroup,
hence trivial. The original subgroup must consequently be a two-group.

Both normality and the quotient are relative to the local group. This is
the final normalizer contradiction in Aschbacher–Smith 13.4.12, pp.910–911.
-/

public section
open Subgroup
namespace Theory.GroupTheory
/-- A solvable normal subgroup is killed by a surjection to a nonsolvable
simple group. -/
theorem solvable_normal_le_simple_ker
    {A B : Type*} [Group A] [Group B] [IsSimpleGroup B]
    (f : A →* B) (hf : Function.Surjective f) (hb : ¬ Group.IsSolvable B)
    (K : Subgroup A) [K.Normal] [Group.IsSolvable K] : K ≤ f.ker := by
  have hn := Subgroup.Normal.map (inferInstance : K.Normal) f hf
  let : Group.IsSolvable (K.map f) :=
    Group.isSolvable_of_surjective (f := f.subgroupMap K) (f.subgroupMap_surjective K)
  have he : K.map f = ⊥ := by
    rcases hn.eq_bot_or_eq_top with h | h
    · exact h
    · exact (hb (Group.isSolvable_of_surjective (f := (K.map f).subtype)
        (by rw [h]; exact topEquiv.surjective))).elim
  intro x hx
  have hm := mem_map_of_mem f hx
  rw [he, mem_bot] at hm
  exact hm

/-- A maximal two-local group with a nonsolvable simple quotient over its
two-core cannot normalize a solvable non-two-group with nontrivial two-core.
The normalized group is first placed inside the local group by maximality. -/
theorem not_normalizes_solvable
    {G S : Type*} [Group G] [Group S] [IsSimpleGroup S]
    (N K : Subgroup G) (hN : IsMaximalTwoLocal N)
    (hcore : K.pCoreIn 2 ≠ ⊥) (hsolv : Group.IsSolvable K)
    (hnot : ¬ IsPGroup 2 K)
    (e : (N ⧸ pCore 2 N) ≃* S) (hS : ¬ Group.IsSolvable S) :
    ¬ N ≤ normalizer (K : Set G) := by
  intro hn
  have hchar : normalizer (K : Set G) ≤ normalizer (K.pCoreIn 2 : Set G) :=
    normalizer_le_normalizer_characteristic_image K (pCore 2 K)
  have hmax : normalizer (K.pCoreIn 2 : Set G) ≤ N :=
    hN.2 ⟨K.pCoreIn 2, hcore, isPGroup_pCoreIn 2 K, rfl⟩ (hn.trans hchar)
  have hKN : K ≤ N := K.le_normalizer.trans (hchar.trans hmax)
  let : (K.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hKN).mpr hn
  let : Group.IsSolvable K := hsolv
  let : Group.IsSolvable (K.subgroupOf N) :=
    Group.isSolvable_of_isSolvable_injective (f := (subgroupOfEquivOfLe hKN).toMonoidHom)
      (subgroupOfEquivOfLe hKN).injective
  let f : N →* S := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 N))
  have hker : f.ker = pCore 2 N := by
    ext x
    change e (QuotientGroup.mk' (pCore 2 N) x) = 1 ↔ _
    rw [e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  have hk := solvable_normal_le_simple_ker f
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) hS (K.subgroupOf N)
  rw [hker] at hk
  have hp : K ≤ N.pCoreIn 2 := by
    have hh := map_mono (f := N.subtype) hk
    rwa [map_subgroupOf_eq_of_le hKN] at hh
  exact hnot ((isPGroup_pCoreIn 2 N).to_le hp)

end Theory.GroupTheory
