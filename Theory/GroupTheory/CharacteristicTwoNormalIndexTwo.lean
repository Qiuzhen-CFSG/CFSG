module

public import Theory.GroupTheory.CharacteristicTwoIndexTwoRestriction

/-!
# Characteristic two passes to normal subgroups of index dividing two

Let H be normal in a finite group G with self-centralizing two-core Q.
The intersection H ∩ Q has index one or two in Q. Its centralizer in G is
therefore a two-group, using the fixed-index-two automorphism calculation.
Since H ∩ Q lies in O₂(H), the normal subgroup C_H(O₂(H)) is also a two-group
and is contained in O₂(H).

This restriction lemma is used for the actual intersections of the binary
G₂ parabolics with G₂(2)′ in the converse to Aschbacher–Smith, Theorem 0.1.2,
printed pp.3–4 and 481–482. All cores and centralizers in the conclusion
are intrinsic to H.
-/

namespace Subgroup

/-- A normal subgroup of index one or two inherits a self-centralizing two-core. -/
public theorem centralizer_pCore_le_of_normal_index_dvd_two {G : Type*} [Group G] [Finite G]
    (hcentral : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (H : Subgroup G) [H.Normal] (hi : H.index ∣ 2) :
    centralizer (pCore 2 H : Set H) ≤ pCore 2 H := by
  let Q := pCore 2 G
  let R := H ⊓ Q
  let U := Q.subgroupOf H
  have hU : U ≤ pCore 2 H :=
    le_sSup ⟨inferInstance, (pCore_isPGroup (p := 2) (G := G)).comap_subtype⟩
  have heq : R.subgroupOf Q = H.subgroupOf Q := by
    ext x
    simp [R]
  have hd : (R.subgroupOf Q).index ∣ 2 := by
    rw [heq]
    exact (H.relIndex_dvd_index_of_normal Q).trans hi
  have hC : IsPGroup 2 (centralizer (R : Set G)) := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
    · have hRQ : R = Q := by
        apply le_antisymm inf_le_right
        exact (Subgroup.relIndex_eq_one.mp h1)
      rw [hRQ]
      exact (pCore_isPGroup (p := 2) (G := G)).to_le hcentral
    · exact centralizer_isPGroup_of_index_two_in_core hcentral R h2
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


end Subgroup
