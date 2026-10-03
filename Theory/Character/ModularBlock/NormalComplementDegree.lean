module

public import Theory.Character.ModularBlock.OrdinaryOddQuotient
public import Theory.Character.ModularBlock.PGroupCartan
public import Theory.GroupTheory.CoprimeQuotientSubgroups

/-!
# The principal-block degree sum with a normal two-complement

Inflation bijects the prescribed principal block with the compatible quotient
block through an odd normal subgroup. If the quotient is a two-group, all of
its ordinary characters are in that block. Transporting the degree sum along
this actual equivalence therefore gives the order of the quotient.

Source: Brauer, *Some applications of the theory of blocks of characters of
finite groups. II* (1964), §III (3.2), (3.5), applied in §VI (6.1).
-/

public section
noncomputable section

open scoped BigOperators
namespace ModularBlock.NormalComplementDegree
open PrincipalBlockConstruction CompatibleLocalBlock
variable {G : Type*} [Group G] [Finite G]

/-- The actual principal-block degree sum is the order of the two-group
quotient by an odd normal subgroup. -/
theorem sum_degree_sq (d : PrincipalCongruenceBlockData G)
    (N : Subgroup G) [N.Normal] (hN : Odd (Nat.card N))
    (hQ : IsPGroup 2 (G ⧸ N)) :
    ∑ i ∈ d.block, d.chi i (ConjClasses.mk 1) ^ 2 = (Nat.card (G ⧸ N) : ℂ) := by
  classical
  let q := compatibleQuotientPrincipalCongruenceBlockData d N
  calc
    _ = ∑ i : {i // i ∈ d.block}, d.chi i.val (ConjClasses.mk 1) ^ 2 := by
      rw [← Finset.sum_attach]
      rfl
    _ = ∑ j : {j // j ∈ q.block}, q.chi j.val (ConjClasses.mk 1) ^ 2 := by
      apply Fintype.sum_equiv (OrdinaryOddQuotient.blockEquiv d N hN)
      intro i
      rw [OrdinaryOddQuotient.blockEquiv_character d N hN i 1, map_one]
    _ = ∑ j ∈ q.block, q.chi j (ConjClasses.mk 1) ^ 2 := by
      symm
      rw [← Finset.sum_attach]
      rfl
    _ = _ := PGroupCartan.sum_degree_sq q hQ

/-- With a normal two-complement, the principal-block degree sum is the
order of any Sylow two-subgroup. The quotient map is injective on that
Sylow subgroup and its image is the whole two-group quotient. -/
theorem sum_degree_sq_eq_sylow_card (d : PrincipalCongruenceBlockData G)
    (S : Sylow 2 G) (N : Subgroup G) [N.Normal]
    (hN : Nat.Coprime 2 (Nat.card N)) (hQ : IsPGroup 2 (G ⧸ N)) :
    ∑ i ∈ d.block, d.chi i (ConjClasses.mk 1) ^ 2 = (Nat.card S : ℂ) := by
  have hcard : Nat.card (G ⧸ N) = Nat.card S := by
    let f := QuotientGroup.mk' N
    have hi : Function.Injective (f.comp (S : Subgroup G).subtype) :=
      Subgroup.injective_comp_subtype_of_coprime_ker f
        (by simpa only [f, QuotientGroup.ker_mk'] using hN) _ S.isPGroup'
    have he : Nat.card ((S : Subgroup G).map f) = Nat.card S := by
      symm
      apply Nat.card_congr
      exact (MulEquiv.ofBijective (f.subgroupMap (S : Subgroup G))
        ⟨fun a b hab => hi (congrArg Subtype.val hab), f.subgroupMap_surjective _⟩).toEquiv
    have ht : (S : Subgroup G).map f = ⊤ := by
      apply top_unique
      exact (hQ.to_subgroup ⊤).le_sylow_of_normal
        (S.mapSurjective (QuotientGroup.mk'_surjective N))
    rwa [ht, Subgroup.card_top] at he

  rw [sum_degree_sq d N (Nat.coprime_two_left.mp hN) hQ, hcard]

end ModularBlock.NormalComplementDegree
