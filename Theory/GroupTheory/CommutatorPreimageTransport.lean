module

public import Theory.GroupTheory.CommutatorPreimage
public import Mathlib.GroupTheory.Index

/-!
# Restriction and quotient indices of the commutator preimage

The construction commutes with restriction to a subgroup containing the
core and actor and normalizing the layer. Its relative index is the index
of the actor centralizer on the core image in the quotient by that layer.
The layer need only be normal in the restricted group.
-/

namespace Subgroup

public theorem commutatorPreimage_subgroupOf
    {G : Type*} [Group G] (Q E Z P : Subgroup G)
    (hQP : Q ≤ P) (hEP : E ≤ P) (hPZ : P ≤ normalizer Z) :
    (commutatorPreimage Q E Z).subgroupOf P =
      commutatorPreimage (Q.subgroupOf P) (E.subgroupOf P) (Z.subgroupOf P) := by
  let _ : (Z.subgroupOf P).Normal := normal_subgroupOf_of_le_normalizer hPZ
  have hleft : (commutatorPreimage Q E Z).subgroupOf P ≤
      commutatorPreimage (Q.subgroupOf P) (E.subgroupOf P) (Z.subgroupOf P) := by
    apply le_commutatorPreimage
    · exact fun _ helement => commutatorPreimage_le Q E Z helement
    · apply commutator_le.mpr
      intro first hfirst second hsecond
      exact commutator_commutatorPreimage_le Q E Z (hQP.trans hPZ)
        (commutator_mem_commutator hfirst hsecond)
  apply le_antisymm hleft
  let D := commutatorPreimage (Q.subgroupOf P) (E.subgroupOf P) (Z.subgroupOf P)
  have hmap : D.map P.subtype ≤ commutatorPreimage Q E Z := by
    apply le_commutatorPreimage
    · exact (map_mono (commutatorPreimage_le _ _ _)).trans_eq
        (map_subgroupOf_eq_of_le hQP)
    · have hbound := map_mono (f := P.subtype)
        (commutator_commutatorPreimage_le (Q.subgroupOf P) (E.subgroupOf P)
          (Z.subgroupOf P) le_normalizer_of_normal)
      rw [map_commutator, map_subgroupOf_eq_of_le hEP] at hbound
      exact hbound.trans (by rw [subgroupOf_map_subtype]; exact inf_le_left)
  exact fun _ helement => hmap (mem_map_of_mem P.subtype helement)

public theorem commutatorPreimage_relIndex_eq_centralizer
    {G : Type*} [Group G] (Q E Z : Subgroup G) [Z.Normal] :
    (commutatorPreimage Q E Z).relIndex Q =
      (centralizer (E.map (QuotientGroup.mk' Z) : Set (G ⧸ Z))).relIndex
        (Q.map (QuotientGroup.mk' Z)) := by
  rw [commutatorPreimage_eq_inf_comap_centralizer, inf_relIndex_left, relIndex_comap]

public theorem commutatorPreimage_relIndex_subgroup_quotient
    {G : Type*} [Group G] (Q E Z P : Subgroup G)
    (hQP : Q ≤ P) (hEP : E ≤ P) (hPZ : P ≤ normalizer Z) :
    let _ : (Z.subgroupOf P).Normal := normal_subgroupOf_of_le_normalizer hPZ
    (commutatorPreimage Q E Z).relIndex Q =
      (centralizer ((E.subgroupOf P).map (QuotientGroup.mk' (Z.subgroupOf P)) :
        Set (P ⧸ Z.subgroupOf P))).relIndex
        ((Q.subgroupOf P).map (QuotientGroup.mk' (Z.subgroupOf P))) := by
  let _ : (Z.subgroupOf P).Normal := normal_subgroupOf_of_le_normalizer hPZ
  dsimp only
  rw [← relIndex_subgroupOf (H := commutatorPreimage Q E Z) hQP,
    commutatorPreimage_subgroupOf Q E Z P hQP hEP hPZ]
  exact commutatorPreimage_relIndex_eq_centralizer _ _ _

end Subgroup
