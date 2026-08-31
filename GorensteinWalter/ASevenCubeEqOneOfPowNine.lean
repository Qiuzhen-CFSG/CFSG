module

public import GorensteinWalter.ASevenInvariantOddPSubgroupCertificateDefs
import Mathlib.Tactic

namespace GorensteinWalter

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
public theorem a7_cube_eq_one_of_pow_nine :
    ∀ x : ASevenCertificateGroup, x ^ 9 = 1 → x ^ 3 = 1 := by
  intro x hx
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  apply Subtype.ext
  have hxPerm : (x : Equiv.Perm (Fin 7)) ^ 9 = 1 :=
    congrArg Subtype.val hx
  change (x : Equiv.Perm (Fin 7)) ^ 3 = 1
  rw [Equiv.Perm.pow_prime_eq_one_iff]
  intro n hn
  have hndvd : n ∣ 9 :=
    (Equiv.Perm.dvd_of_mem_cycleType hn).trans
      (orderOf_dvd_of_pow_eq_one hxPerm)
  have hnle : n ≤ 7 :=
    (Equiv.Perm.le_card_support_of_mem_cycleType hn).trans
      ((x : Equiv.Perm (Fin 7)).support.card_le_univ.trans_eq (by simp))
  have hnlt : 1 < n := Equiv.Perm.one_lt_of_mem_cycleType hn
  interval_cases n <;> norm_num at hndvd <;> omega

end GorensteinWalter
