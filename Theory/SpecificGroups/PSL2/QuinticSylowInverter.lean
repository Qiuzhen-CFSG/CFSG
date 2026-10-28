module

public import Theory.SpecificGroups.PSL2.QuinticInnerFusion
public import Theory.GroupTheory.PrimeSubgroupInvolution

/-!
# An actual Sylow inverter of a normalized five-subgroup

An odd-field PSL₂ Sylow subgroup contains a Klein four, and no Klein four
centralizes a nontrivial odd cyclic subgroup. Select an involution in the
supplied Sylow that does not centralize the supplied order-five subgroup.
Its action on that prime-order group is inversion.

Source: Aschbacher--Smith A.3.15(1), printed p.50, and 6.1.4, p.666.
-/

public section
open Subgroup GorensteinWalter
open scoped MatrixGroups
namespace Theory.PSL2

/-- The inverter is an involution in the original Sylow subgroup and acts
on the entire original five-subgroup. -/
theorem odd_quintic_sylow_inverter {F : Type*} [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) (X : Subgroup PSL(2,F))
    (hc : Nat.card X = 5) (S : Sylow 2 PSL(2,F))
    (hSX : (S : Subgroup PSL(2,F)) ≤ normalizer (X : Set PSL(2,F))) :
    ∃ t : PSL(2,F), t ∈ S ∧ IsInvolution t ∧
      ∀ x ∈ X, t*x*t⁻¹=x⁻¹ := by
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let : IsCyclic X := isCyclic_of_prime_card hc
  have hne : X ≠ ⊥ := by intro he; simp [he] at hc
  have ho : Odd (Nat.card X) := by rw [hc]; decide
  obtain ⟨n,hn,⟨e⟩⟩ := psl2_odd_hasDihedralSylowTwo_model F hF S
  obtain ⟨V,hVS,hV⟩ := exists_kleinFour_le_of_dihedral_subgroup_mulEquiv
    (S : Subgroup PSL(2,F)) hn e
  have hVC := psl2_no_kleinFour_centralizes_odd_cyclic F hF X V inferInstance hne ho hV
  obtain ⟨t,ht,htC⟩ := Set.not_subset.mp hVC
  have ht1 : t ≠ 1 := by intro he; apply htC; simp [he]
  have ht2 : t^2=1 := by
    have he := congrArg Subtype.val (hV.mul_self ⟨t,ht⟩)
    change t*t=1 at he
    simpa only [pow_two] using he
  refine ⟨t,hVS ht,⟨ht1,ht2⟩,?_⟩
  rcases centralizes_or_inverts_prime_subgroup_of_sq_eq_one X
    (hc ▸ Nat.prime_five) t ht2 (hSX (hVS ht)) with hz | hi
  · exact (htC (fun x hx => (hz x hx).symm)).elim
  · exact hi

end Theory.PSL2
