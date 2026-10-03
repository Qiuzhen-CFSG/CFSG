module
public import Theory.GroupAction.NoCyclicNineOnSixteen
public import Theory.Representation.FaithfulSixteenPGroupNine

/-!
# Faithful three-groups on a binary module of order sixteen

A finite three-group acting faithfully by automorphisms on an elementary
abelian two-group of order sixteen is elementary abelian of order at most
nine. The given action is retained, faithfulness is expressed by the
literal full fixing subgroup, and the trivial actor group is included.

The existing faithful-sixteen prime-power calculation embeds the actor
into GL₄(2) and bounds its three-part by nine. Thus the only possible actor
orders are one, three and nine. Groups of order nine are abelian; the
source-neutral cyclic-nine exclusion rules out exponent nine, leaving
exponent three. The two smaller orders are immediate from the exponent
dividing the group order.

This is the finite-linear action calculation needed for Stellmacher
(8.6)(20), printed p.45 of `refs/files/stellmacher-n-group.pdf`, where the
actor is a residual centralizer acting on the actual fixed module. No
campaign imports or local quotient model are used in this Theory result.
-/

open scoped IsMulCommutative

public theorem three_group_faithful_sixteen_is_elementary
    {A V : Type*} [Group A] [Finite A] [Group V] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction A V]
    (hA : IsPGroup 3 A) (hV : Nat.card V = 16)
    (hfaith : fixingSubgroup A (Set.univ : Set V) = ⊥) :
    IsElementaryAbelian 3 A ∧ Nat.card A ≤ 9 := by
  let _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let _ : FaithfulSMul A V := faithfulSMul_iff.mpr (by
    intro actor hactor
    have hmem : actor ∈ fixingSubgroup A (Set.univ : Set V) := by
      rw [mem_fixingSubgroup_iff]
      exact fun point _ => hactor point
    rwa [hfaith] at hmem)
  have hcases : Nat.card A = 1 ∨ Nat.card A = 3 ∨ Nat.card A = 9 := by
    obtain ⟨n,hn⟩ := hA.exists_card_eq
    by_cases hlarge : 2 ≤ n
    · have hnine : 9 ∣ Nat.card A := by
        rw [hn]
        exact Nat.pow_dvd_pow 3 hlarge
      exact Or.inr (Or.inr
        (Representation.card_nine_of_faithful_sixteen_pGroup hA hV hnine).2)
    · have hnsmall : n ≤ 1 := by omega
      interval_cases n
      · exact Or.inl (by simpa using hn)
      · exact Or.inr (Or.inl (by simpa using hn))
  rcases hcases with hone | hthree | hnine
  · let _ : Subsingleton A := (Nat.card_eq_one_iff_unique.mp hone).1
    have hcomm : IsMulCommutative A := ⟨⟨fun _ _ => Subsingleton.elim _ _⟩⟩
    refine ⟨{ toIsMulCommutative := hcomm, exponent_dvd_p := ?_ },by omega⟩
    have hdiv := Group.exponent_dvd_nat_card (G := A)
    rw [hone] at hdiv
    exact hdiv.trans (one_dvd 3)
  · have hcomm : IsMulCommutative A := (isCyclic_of_prime_card hthree).isMulCommutative
    refine ⟨{ toIsMulCommutative := hcomm, exponent_dvd_p := ?_ },by omega⟩
    simpa only [hthree] using (Group.exponent_dvd_nat_card (G := A))
  · have hcard : Nat.card A = 3 ^ 2 := hnine
    let hcomm : IsMulCommutative A := IsPGroup.isMulCommutative_of_card_eq_prime_sq hcard
    let _ := hcomm
    have hnot := not_isCyclic_of_card_nine_of_faithful_on_card_sixteen hnine hV hfaith
    have hexponent : Monoid.exponent A = 3 :=
      (not_isCyclic_iff_exponent_eq_prime Nat.prime_three hcard).mp hnot
    exact ⟨{ toIsMulCommutative := hcomm, exponent_dvd_p := hexponent ▸ dvd_rfl },by omega⟩
