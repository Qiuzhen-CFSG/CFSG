module

public import Theory.GroupTheory.PGroup.ClassTwoCyclicDerived

/-!
# Cyclic derived subgroup with central quotient of order at most four

A finite two-group with central quotient of order at most four is class two.
Its central quotient has first omega of order at most four, so the existing
two-generator commutator calculation makes its derived subgroup cyclic.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace IsPGroup

theorem isCyclic_commutator_of_card_center_quotient_le_four
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hbound : Nat.card (P ⧸ center P) ≤ 4) :
    IsCyclic (commutator P) := by
  have hQ := hP.to_quotient (center P)
  obtain ⟨n, hn⟩ := hQ.exists_card_eq
  have hnle : n ≤ 2 := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    simpa only [← hn] using hbound
  have hcomm : IsMulCommutative (P ⧸ center P) := by
    interval_cases n
    · let : IsCyclic (P ⧸ center P) := isCyclic_of_card_dvd_prime (p := 2) (by
        rw [hn]
        norm_num)
      infer_instance
    · let : IsCyclic (P ⧸ center P) := isCyclic_of_card_dvd_prime (p := 2) (by
        rw [hn]
        norm_num)
      infer_instance
    · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq hn
  exact hP.isCyclic_commutator_of_card_omega_center_quotient_le_four
    (Normal.quotient_commutative_iff_commutator_le.mp hcomm)
    ((card_le_card_group _).trans hbound)

end IsPGroup
