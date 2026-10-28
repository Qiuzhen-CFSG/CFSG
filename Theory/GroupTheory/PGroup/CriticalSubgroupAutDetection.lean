module

public import Theory.GroupTheory.PGroup.CriticalSubgroupAutomorphisms

/-!
# Detecting a non-two-group automorphism group on a critical subgroup

The restriction kernel for a critical subgroup is a two-group by its
centralizer condition. If the automorphism group of the critical subgroup
were also a two-group, the ambient automorphism group would be one.

This shared consequence of Thompson's critical subgroup theorem is used in
both the central-four and central-involution cases of the normal-eight
argument. Source: Gorenstein, *Finite Groups*, Theorem 5.3.11, pp.185–186.
-/

open Subgroup

namespace IsCriticalPSubgroup

/-- A critical subgroup detects a non-two-group automorphism group. -/
public theorem not_isPGroup_mulAut_of_ambient
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    {C : Subgroup P} (hC : IsCriticalPSubgroup 2 C)
    (hAut : ¬ IsPGroup 2 (MulAut P)) : ¬ IsPGroup 2 (MulAut C) := by
  let : C.Characteristic := hC.characteristic
  intro h
  let r := MulAut.characteristic C
  have hk : IsPGroup 2 r.ker :=
    C.isPGroup_characteristic_restriction_kernel_of_centralizer_le
      (hP.to_subgroup C) (by rw [hC.centralizer_eq]; exact map_subtype_le _)
  have ht := (h.to_subgroup r.range).comap_of_ker_isPGroup r hk
  rw [MonoidHom.comap_range_self] at ht
  exact hAut (ht.of_equiv Subgroup.topEquiv)

end IsCriticalPSubgroup
