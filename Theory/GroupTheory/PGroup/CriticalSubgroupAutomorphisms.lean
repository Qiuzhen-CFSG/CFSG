module

public import Theory.GroupTheory.PGroup.CriticalSubgroup
public import Theory.GroupTheory.CharacteristicSelfCentralizingAutomorphisms
public import Theory.GroupTheory.PrimeOrderLift

/-!
# Coprime automorphisms detected by a critical subgroup

Restriction to a critical subgroup of a finite p-group preserves the order
of every automorphism of order coprime to p. Its centralizer condition makes
the restriction kernel a p-group, and hence the kernel meets each such
cyclic automorphism subgroup trivially.

This is the automorphism-detection consequence of Thompson's critical
subgroup construction; see Gorenstein, *Finite Groups*, Theorem 5.3.11,
pp.185–186. It does not assert an exponent bound for the critical subgroup.
-/

namespace IsCriticalPSubgroup

/-- Restriction to a critical subgroup preserves coprime automorphism orders. -/
public theorem orderOf_restrict_eq_of_coprime
    {p : ℕ} {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup p P) {C : Subgroup P} (hC : IsCriticalPSubgroup p C)
    (a : MulAut P) (hcop : p.Coprime (orderOf a)) :
    letI : C.Characteristic := hC.characteristic
    orderOf (MulAut.characteristic C a) = orderOf a := by
  let : C.Characteristic := hC.characteristic
  have hself : Subgroup.centralizer (C : Set P) ≤ C := by
    rw [hC.centralizer_eq]
    exact Subgroup.map_subtype_le _
  exact (MulAut.characteristic C).orderOf_map_eq_of_coprime_of_isPGroup_ker
    (C.isPGroup_characteristic_restriction_kernel_of_centralizer_le
      (hP.to_subgroup C) hself) a hcop

/-- An order-nine automorphism of a two-group restricts to one on every
critical subgroup. Thus excluding order nine can be done on that subgroup. -/
public theorem no_order_nine_of_restriction
    {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P) {C : Subgroup P} (hC : IsCriticalPSubgroup 2 C)
    (hno : ∀ a : MulAut C, orderOf a ≠ 9) :
    ∀ a : MulAut P, orderOf a ≠ 9 := by
  intro a ha
  let : C.Characteristic := hC.characteristic
  have hcop : Nat.Coprime 2 (orderOf a) := by rw [ha]; decide
  exact hno (MulAut.characteristic C a) ((hC.orderOf_restrict_eq_of_coprime hP a hcop).trans ha)

end IsCriticalPSubgroup
