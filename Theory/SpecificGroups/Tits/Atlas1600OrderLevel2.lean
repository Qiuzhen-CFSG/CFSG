module

public import Theory.SpecificGroups.Tits.Atlas1600OrderLevel2Data

/-!
# The terminal stabilizer in the Atlas degree-1600 model

At base point 2 the 32 word representatives are distinct, and multiplication by
any of the six signed generators permutes these representatives. There is no
remaining factor. The generic word-subgroup bijection therefore gives order 32.
The witnesses originate from the Atlas permutations in
`refs/original/n-group-global/atlas-tits-p1600-{a,b}.g`.
-/

namespace Tits.Atlas1600OrderCertificate
open Theory.GroupTheory
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

public theorem L2Step (i : Fin 6) (r : Fin 32) :
    L2Gen i * L2Rep r = L2Rep (L2Act i r) * evalWord L3Gen (L2Factor i r) := by
  apply Equiv.ext
  revert i r
  apply allFin₃
  decide +kernel

public theorem H2_card : Nat.card H2 = 32 := by
  have h := wordSubgroup_card_eq_mul_next
    L2Gen L2Inv L2Inv_spec L3Gen L3Inv L3Inv_spec
    L2Rep L2Act L2Factor (2 : Fin 1600) L2Point (0 : Fin 32)
    L2Rep_mem
    (wordSubgroup_le_of_gen_mem (fun i => Fin.elim0 i))
    L2Rep_base L2Rep_point L2Point_injective
    (wordSubgroup_fix_of_gen_fix L3Gen L3Inv L3Inv_spec (fun i => Fin.elim0 i))
    L2Step
  change Nat.card H2 = 32 * Nat.card H3 at h
  simpa only [H3_card, Nat.mul_one] using h

end Tits.Atlas1600OrderCertificate
