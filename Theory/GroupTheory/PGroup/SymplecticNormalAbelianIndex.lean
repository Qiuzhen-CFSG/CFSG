module

public import Theory.GroupTheory.PGroup.BinaryCommutatorIndex
public import Theory.GroupTheory.PGroup.ClassTwoCyclicCenter
public import Theory.GroupTheory.PGroup.CyclicRotationAbelianIndex
public import Theory.GroupTheory.PGroup.SymplecticRotationDichotomy
public import Theory.Frattini.SubgroupIndexBound

/-!
# Normal abelian self-centralizer indices in binary symplectic groups

For a finite two-group with cyclic center and elementary abelian central
quotient, an abelian self-centralizer has index at most the order of its first
omega subgroup. In the nonabelian case the derived subgroup is central of
order two, so the binary commutator-character estimate applies. The abelian
case has self-centralizer equal to the whole group.

A binary symplectic two-group with cyclic center has either such a central
quotient or a large cyclic rotation subgroup. In the latter branch, normality
of the abelian self-centralizer allows the rotation index estimate to apply.
Thus in both branches its index is at most its first omega order. If that
order is at most four, the index is at most four and the Frattini quotient has
order at most sixteen.

This is the intrinsic symplectic-type specialization of MacWilliams–Sah,
quoted in Janko–Thompson, Math. Z. 113 (1970), result 1.1, printed p.385,
and applied on p.389.
-/

open Subgroup

namespace IsPGroup

/-- Central binary quotients with cyclic center satisfy the stronger omega
index bound. Normality of the abelian self-centralizer is not needed. -/
public theorem abelian_index_le_omega_one_of_elementary_central_quotient
    {Q : Type*} [Group Q] [Finite Q] [IsCyclic (center Q)]
    (hQ : IsPGroup 2 Q) (hq : IsElementaryAbelian 2 (Q ⧸ center Q))
    (A : Subgroup Q) [IsMulCommutative A]
    (hC : centralizer (A : Set Q) ≤ A) :
    A.index ≤ Nat.card (omega₁ A (p := 2)) := by
  by_cases hab : center Q = ⊤
  · have htop : A = ⊤ := top_unique (by
      rw [← hab]
      exact (center_le_centralizer (A : Set Q)).trans hC)
    rw [htop, index_top]
    exact Nat.card_pos
  · exact index_le_omega_one_of_binary_commutators A (_root_.commutator Q)
      (hQ.to_subgroup A) hq.commutator_le_center_of_central_quotient
      (hq.card_commutator_eq_two_of_cyclic_center hab)
      (commutator_mono le_rfl le_top) hC

/-- First omega of order at most four gives self-centralizer index at most
four in the elementary central-quotient branch. -/
public theorem abelian_index_le_four_of_elementary_central_quotient
    {Q : Type*} [Group Q] [Finite Q] [IsCyclic (center Q)]
    (hQ : IsPGroup 2 Q) (hq : IsElementaryAbelian 2 (Q ⧸ center Q))
    (A : Subgroup Q) [IsMulCommutative A]
    (hC : centralizer (A : Set Q) ≤ A)
    (hO : Nat.card (omega₁ A (p := 2)) ≤ 4) : A.index ≤ 4 :=
  (hQ.abelian_index_le_omega_one_of_elementary_central_quotient hq A hC).trans hO

/-- The central-quotient branch also gives the required Frattini order bound. -/
public theorem frattini_card_le_sixteen_of_elementary_central_quotient
    {Q : Type*} [Group Q] [Finite Q] [IsCyclic (center Q)]
    (hQ : IsPGroup 2 Q) (hq : IsElementaryAbelian 2 (Q ⧸ center Q))
    (A : Subgroup Q) [IsMulCommutative A]
    (hC : centralizer (A : Set Q) ≤ A)
    (hO : Nat.card (omega₁ A (p := 2)) ≤ 4) :
    Nat.card (Q ⧸ frattini Q) ≤ 16 :=
  (hQ.card_frattini_quotient_le_index_mul_omega_one A).trans
    (by
      simpa using Nat.mul_le_mul
        (hQ.abelian_index_le_four_of_elementary_central_quotient hq A hC hO) hO)

/-- In a binary symplectic two-group with cyclic center, a normal abelian
self-centralizer has index at most the order of its first omega subgroup. -/
public theorem normal_abelian_index_le_omega_one_of_symplectic_type
    {Q : Type*} [Group Q] [Finite Q] [IsCyclic (center Q)]
    (hQ : IsPGroup 2 Q) (hsymp : IsBinarySymplecticType Q)
    (A : Subgroup Q) [A.Normal] [IsMulCommutative A]
    (hC : centralizer (A : Set Q) ≤ A) :
    A.index ≤ Nat.card (omega₁ A (p := 2)) := by
  rcases hsymp.elementary_central_quotient_or_large_rotation hQ with
    hq | ⟨r, hr, hrn, hi, hsq, hcent⟩
  · exact hQ.abelian_index_le_omega_one_of_elementary_central_quotient hq A hC
  · exact index_le_omega_one_of_cyclic_rotation r ((by decide : 2 ∣ 8).trans hr)
      hrn hi hsq hcent A hC

/-- The intrinsic index-four bound used in the symplectic specialization of
the normal-subgroup MacWilliams–Sah bound. -/
public theorem normal_abelian_index_le_four_of_symplectic_type
    {Q : Type*} [Group Q] [Finite Q] [IsCyclic (center Q)]
    (hQ : IsPGroup 2 Q) (hsymp : IsBinarySymplecticType Q)
    (A : Subgroup Q) [A.Normal] [IsMulCommutative A]
    (hC : centralizer (A : Set Q) ≤ A)
    (hO : Nat.card (omega₁ A (p := 2)) ≤ 4) : A.index ≤ 4 :=
  (hQ.normal_abelian_index_le_omega_one_of_symplectic_type hsymp A hC).trans hO

/-- A normal abelian self-centralizer of first omega order at most four gives
the Frattini bound sixteen in a binary symplectic two-group with cyclic center. -/
public theorem frattini_card_le_sixteen_of_symplectic_type
    {Q : Type*} [Group Q] [Finite Q] [IsCyclic (center Q)]
    (hQ : IsPGroup 2 Q) (hsymp : IsBinarySymplecticType Q)
    (A : Subgroup Q) [A.Normal] [IsMulCommutative A]
    (hC : centralizer (A : Set Q) ≤ A)
    (hO : Nat.card (omega₁ A (p := 2)) ≤ 4) :
    Nat.card (Q ⧸ frattini Q) ≤ 16 :=
  (hQ.card_frattini_quotient_le_index_mul_omega_one A).trans
    (by
      simpa using Nat.mul_le_mul
        (hQ.normal_abelian_index_le_four_of_symplectic_type hsymp A hC hO) hO)

end IsPGroup
