module

public import CFSG.Quasithin.MainConverse.AlternatingSections.NineReduction.Primitive.SimpleRecognition.TripleRigidity.OrderCases.DoubleTransposition

/-!
# Excluding even order in a degree-nine triple stabilizer

An involution fixing three of nine points moves at most six points. If its
permutation is even, its cycle type is `(2,2)`. Triple transitivity would then
force a factor five in the group order by the seven-point pair-stabilizer
argument in `DoubleTransposition`. Cauchy's theorem therefore excludes even
order in the triple stabilizer whenever five does not divide the group order.

This conditional action lemma is applied with the independently proved
`FiveExclusion` result. Source context: condition K and the alternating case
in Aschbacher–Smith, *The Classification of Quasithin Groups*,
`refs/quasithin.pdf`, printed pp.4 and 482.
-/

open Equiv Equiv.Perm MulAction Subgroup
namespace CFSG.Quasithin.MainConverse.NineReduction

private theorem cycleType_involution_fixing_three (g : Perm (Fin 9))
    (hg : orderOf g = 2) (heven : g ∈ alternatingGroup (Fin 9))
    (h0 : g 0 = 0) (h1 : g 1 = 1) (h2 : g 2 = 2) : g.cycleType = {2, 2} := by
  have hs : g.support ⊆ ({0, 1, 2} : Finset (Fin 9))ᶜ := by
    intro x hx
    rw [Finset.mem_compl]
    intro h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl | rfl
    · exact (mem_support.mp hx) h0
    · exact (mem_support.mp hx) h1
    · exact (mem_support.mp hx) h2
  have hcard : g.support.card ≤ 6 := (Finset.card_le_card hs).trans (by decide)
  obtain ⟨n, hn⟩ := cycleType_prime_order (hg ▸ Nat.prime_two)
  rw [hg] at hn
  have hsum := g.sum_cycleType
  rw [hn, Multiset.sum_replicate] at hsum
  simp only [smul_eq_mul] at hsum
  have hn2 : n ≤ 2 := by omega
  have hsign := mem_alternatingGroup.mp heven
  rw [sign_of_cycleType, hn] at hsign
  interval_cases n
  · norm_num [Units.ext_iff] at hsign
  · simpa using hn
  · norm_num [Units.ext_iff] at hsign

/-- Without a factor five, an even triple-transitive degree-nine action has odd triple stabilizers. -/
public theorem nine_two_not_dvd_fixing_triple_card (G : Type*) [Group G] [Finite G]
    [MulAction G (Fin 9)] [FaithfulSMul G (Fin 9)]
    (hthree : IsMultiplyPretransitive G (Fin 9) 3)
    (heven : ∀ g : G, toPermHom G (Fin 9) g ∈ alternatingGroup (Fin 9))
    (hfive : ¬ 5 ∣ Nat.card G) :
    ¬ 2 ∣ Nat.card (fixingSubgroup G ({0, 1, 2} : Set (Fin 9))) := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  intro htwo
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 2 htwo
  let f := toPermHom G (Fin 9)
  let E : G ≃* f.range := MonoidHom.ofInjective toPerm_injective
  let X : Fin 9 →ₑ[E.toMonoidHom] Fin 9 :=
    { toFun := id, map_smul' := fun _ _ => rfl }
  have ht : IsMultiplyPretransitive f.range (Fin 9) 3 :=
    (IsPretransitive.of_embedding_congr (n := Fin 3) (f := X)
      E.surjective Function.bijective_id).mp hthree
  have ho : orderOf (f g.val) = 2 := by
    rw [orderOf_injective f toPerm_injective, Subgroup.orderOf_coe]
    exact hg
  have hfix := (mem_fixingSubgroup_iff G).mp g.property
  have hc : (f g.val).cycleType = {2, 2} :=
    cycleType_involution_fixing_three (f g.val) ho (heven g.val)
      (hfix 0 (by simp)) (hfix 1 (by simp)) (hfix 2 (by simp))
  have hd := nine_five_dvd_of_three_transitive_double_transposition f.range ht
    (show f g.val ∈ f.range from ⟨g.val, rfl⟩) hc
  exact hfive ((Nat.card_congr E.toEquiv).symm ▸ hd)

end CFSG.Quasithin.MainConverse.NineReduction
