module

public import Theory.GroupTheory.InvolutionCentralizerFourCyclicComplement
public import Theory.GroupTheory.CyclicIndexTwoInvolutionAction
public import Theory.GroupTheory.DihedralPresentation

/-!
# Recognition from an involution centralizer of order four

A finite two-group with a noncentral involution whose centralizer has order
four is dihedral or has the explicit semidihedral presentation. Noncentrality
is essential: the cyclic group of order four would otherwise be a counterexample.
The conclusion uses only group equivalences and generators and relations, so
this reusable recognition theorem has no dependency on campaign definitions.

The cyclic-complement theorem supplies a cyclic subgroup of index two avoiding
the involution. Its proof justifies the commutator/Frattini count, proves the
derived subgroup cyclic, and uses consecutive square exponents to obtain the
complement. Index two gives generation by its generator and the involution.
The action theorem determines whether conjugation inverts the generator or
has semidihedral exponent. In the first case the dihedral presentation theorem
constructs the equivalence; in the second case the subgroup order and index
give the required cardinality and exponent parameters directly.

Source motivation: Stellmacher, N-Groups, Section 11, case (I), lines 2082–2087
of the repository transcription, citing Gorenstein, Finite Groups (1968),
Section 5.4.5. No maximal-class classification is assumed.
-/

universe u

private theorem closure_pair_eq_top_of_zpowers_index_two
    {G : Type u} [Group G] (a x : G)
    (hindex : (Subgroup.zpowers a).index = 2)
    (hxA : x ∉ Subgroup.zpowers a) :
    Subgroup.closure ({a, x} : Set G) = ⊤ := by
  let generated := Subgroup.closure ({a, x} : Set G)
  have haK : a ∈ generated := Subgroup.subset_closure (by simp)
  have hxK : x ∈ generated := Subgroup.subset_closure (by simp)
  have hAK : Subgroup.zpowers a ≤ generated := Subgroup.zpowers_le.mpr haK
  apply top_unique
  intro element _
  by_cases hgA : element ∈ Subgroup.zpowers a
  · exact hAK hgA
  · have hgxA : element * x ∈ Subgroup.zpowers a :=
      (Subgroup.mul_mem_iff_of_index_two hindex).mpr (by simp [hgA, hxA])
    simpa using generated.mul_mem (hAK hgxA) (generated.inv_mem hxK)

public theorem exists_dihedral_or_semidihedral_of_involution_centralizer_card_four
    {G : Type u} [Group G] [Finite G] (hG : IsPGroup 2 G)
    (x : G) (hx : orderOf x = 2) (hxZ : x ∉ Subgroup.center G)
    (hC : Nat.card (Subgroup.centralizer ({x} : Set G)) = 4) :
    (∃ m : ℕ, Nonempty (G ≃* DihedralGroup m)) ∨
      (∃ n : ℕ, 4 ≤ n ∧ Nat.card G = 2 ^ n ∧
        ∃ a b : G, orderOf a = 2 ^ (n - 1) ∧ orderOf b = 2 ∧
          b * a * b⁻¹ = a ^ (2 ^ (n - 2) - 1) ∧
          Subgroup.closure ({a, b} : Set G) = ⊤) := by
  obtain ⟨a, hindex, hxA⟩ :=
    exists_zpowers_index_two_of_involution_centralizer_card_four hG x hx hxZ hC
  obtain ⟨power, ha⟩ := hG.exists_orderOf_eq_pow a
  have hgen := closure_pair_eq_top_of_zpowers_index_two a x hindex hxA
  have hcard : Nat.card G = 2 * 2 ^ power := by
    rw [← (Subgroup.zpowers a).index_mul_card, hindex, Nat.card_zpowers, ha]
  rcases involution_conj_eq_inv_or_semidihedral_of_zpowers_index_two
    a x power ha hindex hxA hx hC with hinv | ⟨hk, hsemi⟩
  · exact Or.inl ⟨2 ^ power, dihedralGroup_equiv_of_presentation (by positivity)
      a x ha (hx ▸ pow_orderOf_eq_one x) hinv hgen hcard⟩
  · refine Or.inr ⟨power + 1, by omega, ?_, a, x, ?_, hx, ?_, hgen⟩
    · simpa [pow_succ, Nat.mul_comm] using hcard
    · simpa using ha
    · simpa [show power + 1 - 2 = power - 1 by omega] using hsemi
