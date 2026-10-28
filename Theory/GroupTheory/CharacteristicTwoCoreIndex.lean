module

public import Theory.GroupTheory.CharacteristicTwoIndexTwoRestriction
public import Mathlib.GroupTheory.Sylow

/-!
# Characteristic two from a small index in the two-core

Let G have self-centralizing two-core Q. If H intersects Q in a subgroup
of index at most two, then H also has self-centralizing two-core. No
normality of H is required. Indeed C_G(H ∩ Q) is a two-group: use the
self-centralizing property of Q when the index is one, and the proved
index-two restriction bound otherwise. The normal subgroup C_H(O₂(H))
embeds in that centralizer and therefore lies in O₂(H).

Since Q lies in every Sylow two-subgroup S, the hypothesis follows from
[S : S ∩ H] ≤ 2. This is the intrinsic inheritance argument needed for
Aschbacher–Smith, Lemma 1.1.4(7), printed pp.500–501 in the combined
1 March 2004 manuscript.
-/

public section

namespace Subgroup

/-- A subgroup meeting the two-core in index at most two inherits
characteristic two, without a normality assumption on that subgroup. -/
theorem centralizer_pCore_le_of_core_index_le_two
    {G : Type*} [Group G] [Finite G]
    (hc : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (H : Subgroup G) (hi : (H.subgroupOf (pCore 2 G)).index ≤ 2) :
    centralizer (pCore 2 H : Set H) ≤ pCore 2 H := by
  let Q := pCore 2 G
  let R := H ⊓ Q
  let U := Q.subgroupOf H
  have hU : U ≤ pCore 2 H :=
    le_sSup ⟨inferInstance, (pCore_isPGroup (p := 2) (G := G)).comap_subtype⟩
  have heq : R.subgroupOf Q = H.subgroupOf Q := by
    ext x
    simp [R]
  have hiR : (R.subgroupOf Q).index ≤ 2 := by
    rw [heq]
    exact hi
  have hC : IsPGroup 2 (centralizer (R : Set G)) := by
    by_cases h1 : (R.subgroupOf Q).index = 1
    · have hRQ : R = Q := le_antisymm inf_le_right (relIndex_eq_one.mp h1)
      rw [hRQ]
      exact (pCore_isPGroup (p := 2) (G := G)).to_le hc
    · have hpos : (R.subgroupOf Q).index ≠ 0 := index_ne_zero_of_finite
      have htwo : (R.subgroupOf Q).index = 2 := by omega
      exact centralizer_isPGroup_of_index_two_in_core hc R htwo
  let C := centralizer (pCore 2 H : Set H)
  let f : C →* centralizer (R : Set G) :=
    (H.subtype.comp C.subtype).codRestrict _ (by
      intro c
      apply mem_centralizer_iff.mpr
      intro r hr
      exact congrArg Subtype.val (mem_centralizer_iff.mp c.property
        (⟨r, hr.1⟩ : H) (hU hr.2)))
  have hf : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (Subtype.ext (congrArg (fun x => x.val) hab))
  exact le_sSup ⟨inferInstance, hC.of_injective f hf⟩

/-- Characteristic two passes to a subgroup whose intersection with a
Sylow two-subgroup has index at most two. -/
theorem centralizer_pCore_le_of_sylow_relIndex_le_two
    {G : Type*} [Group G] [Finite G]
    (hc : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (S : Sylow 2 G) (H : Subgroup G)
    (hi : H.relIndex (S : Subgroup G) ≤ 2) :
    centralizer (pCore 2 H : Set H) ≤ pCore 2 H := by
  apply centralizer_pCore_le_of_core_index_le_two hc H
  exact (relIndex_le_of_le_right (pCore_isPGroup.le_sylow_of_normal S)
    (index_ne_zero_of_finite : H.relIndex (S : Subgroup G) ≠ 0)).trans hi

end Subgroup
