module

public import Theory.GroupTheory.CharacteristicSelfCentralizingAutomorphisms

/-!
# Coprime automorphisms detected on a characteristic p-subgroup

Restriction to a self-centralizing characteristic p-subgroup has a p-group
kernel. If an automorphism has order coprime to p and to the order of the
subgroup's full automorphism group, its restriction and then the original
automorphism are trivial.

Source application: the natural-extension row of Aschbacher--Smith A.3.6
in the Cartan component argument, 11.5.6(3), printed pp.780--781.
-/

public section
open Subgroup

namespace MulAut
/-- A coprime automorphism is detected by a characteristic self-centralizing
p-subgroup and the full automorphism group of that subgroup. -/
theorem eq_one_of_coprime_characteristic_restriction
    {Q : Type*} [Group Q] [Finite Q]
    (N : Subgroup Q) [N.Characteristic] {p : ℕ}
    (hp : IsPGroup p N) (hself : centralizer (N : Set Q) ≤ N)
    (a : MulAut Q) (hcop : Nat.Coprime (orderOf a) p)
    (haut : Nat.Coprime (orderOf a) (Nat.card (MulAut N))) : a = 1 := by
  let f := MulAut.characteristic N
  have hf : f a = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes haut (orderOf_map_dvd f a) (orderOf_dvd_natCard _))
  let b : f.ker := ⟨a,hf⟩
  have hk := N.isPGroup_characteristic_restriction_kernel_of_centralizer_le hp hself
  have hbk : Nat.Coprime (orderOf b) (orderOf a) := hk.orderOf_coprime hcop.symm b
  have hba : orderOf b = orderOf a := (Subgroup.orderOf_coe b).symm
  have hb : b = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes hbk dvd_rfl hba.dvd)
  exact congrArg Subtype.val hb
end MulAut
