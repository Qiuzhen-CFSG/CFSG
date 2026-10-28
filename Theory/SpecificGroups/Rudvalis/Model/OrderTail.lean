module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel3Data
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel4Data

/-!
# The terminal twenty-element subgroup of the Rudvalis chain

The last two orbit lengths are 5 and 4. All transition identities are checked
pointwise in the kernel; the final subgroup has no generators. Applying the
word-subgroup bijection twice proves that the third subgroup has order 20.
The witnesses come from the ATLAS permutations cited in `OrderChainData`.
-/

namespace Rudvalis.OrderCertificate
open Theory.GroupTheory
set_option maxRecDepth 30000
set_option maxHeartbeats 1600000
set_option Elab.async false

public theorem L4Step (i : Fin 2) (r : Fin 4) :
    L4Gen i * L4Rep r = L4Rep (L4Act i r) * evalWord L5Gen (L4Factor i r) := by
  apply Equiv.ext
  revert i r
  apply allFin₃
  decide +kernel

public theorem H4_card : Nat.card H4 = 4 := by
  have h := wordSubgroup_card_eq_mul_next
    L4Gen L4Inv L4Inv_spec L5Gen L5Inv L5Inv_spec
    L4Rep L4Act L4Factor (4 : Fin 4060) L4Point (0 : Fin 4)
    L4Rep_mem
    (wordSubgroup_le_of_gen_mem (fun i => Fin.elim0 i))
    L4Rep_base L4Rep_point L4Point_injective
    (wordSubgroup_fix_of_gen_fix L5Gen L5Inv L5Inv_spec (fun i => Fin.elim0 i))
    L4Step
  change Nat.card H4 = 4 * Nat.card H5 at h
  simpa only [H5_card, Nat.mul_one] using h

public theorem L3Step (i : Fin 4) (r : Fin 5) :
    L3Gen i * L3Rep r = L3Rep (L3Act i r) * evalWord L4Gen (L3Factor i r) := by
  apply Equiv.ext
  revert i r
  apply allFin₃
  decide +kernel

public theorem H3_card : Nat.card H3 = 20 := by
  have h := wordSubgroup_card_eq_mul_next
    L3Gen L3Inv L3Inv_spec L4Gen L4Inv L4Inv_spec
    L3Rep L3Act L3Factor (3 : Fin 4060) L3Point (0 : Fin 5)
    L3Rep_mem H4_le L3Rep_base L3Rep_point L3Point_injective H4_fix L3Step
  change Nat.card H3 = 5 * Nat.card H4 at h
  simpa only [H4_card] using h

end Rudvalis.OrderCertificate
