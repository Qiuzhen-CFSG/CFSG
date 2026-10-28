module
public import Theory.GroupTheory.Hall.TwoClosedNormal
public import Theory.GroupTheory.PResidual.FiniteImage
/-!
# Odd Hall subgroups of the two-residual

An odd Hall subgroup of O²(N) is also Hall in N. Its index in N is its
index in O²(N) times the order of the two-group N/O²(N). This statement
uses the residual embedded in the original ambient group.

Source application: the Borel O²(N_{L₀}(T ∩ L₀)) in Aschbacher--Smith,
10.2.3, printed p.745.
-/

public section
open Subgroup
namespace Subgroup.OddHall
variable {G : Type*} [Group G] [Finite G]
theorem hall_of_twoResidual (N C : Subgroup G)
    (hC : C ≤ (pResidual 2 N).map N.subtype)
    (hHall : IsHallSubgroup oddPrimes (C.subgroupOf ((pResidual 2 N).map N.subtype))) :
    IsHallSubgroup oddPrimes (C.subgroupOf N) := by
  let R := (pResidual 2 N).map N.subtype
  have hRN : R ≤ N := map_subtype_le _
  have hCN : C ≤ N := hC.trans hRN
  refine ⟨?_,?_⟩
  · intro p hp
    have hc : Nat.card (C.subgroupOf N) = Nat.card (C.subgroupOf R) :=
      (Nat.card_congr (subgroupOfEquivOfLe hCN).toEquiv).trans
        (Nat.card_congr (subgroupOfEquivOfLe hC).toEquiv).symm
    exact hHall.p_in_pi_of_p_dvd_card p (hc ▸ hp)
  · intro p hp hodd
    change p.val ∣ C.relIndex N at hp
    rw [←relIndex_mul_relIndex C R N hC hRN] at hp
    rcases p.property.dvd_mul.mp hp with h | h
    · exact hHall.p_in_pi_of_p_dvd_index p h hodd
    · have hR : R.subgroupOf N = pResidual 2 N := by
        exact (pResidual 2 N).comap_map_eq_self_of_injective N.subtype_injective
      change p.val ∣ (R.subgroupOf N).index at h
      rw [hR,index_eq_card] at h
      obtain ⟨n,hn⟩ := (isPGroup_quotient_pResidual (G := N) 2).exists_card_eq
      rw [hn] at h
      exact hodd (Nat.prime_eq_prime_of_dvd_pow p.property Nat.prime_two h)
end Subgroup.OddHall
