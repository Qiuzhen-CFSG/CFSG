module
public import Theory.GroupTheory.CoprimeQuotientSubgroups.PrimeLift

/-!
# Lifting elements of prime exponent

A finite surjection whose kernel has order prime to p lifts every element
of exponent dividing p to an element of the same exponent. Lift the cyclic
p-subgroup and use injectivity of the quotient map on this p-subgroup.
The literal quotient image is retained.
-/

public section
namespace Subgroup
/-- An element of prime exponent lifts with that same exponent through a coprime kernel. -/
theorem exists_prime_exponent_lift
    {G H : Type*} [Group G] [Finite G] [Group H]
    {p : ℕ} [Fact p.Prime] (f : G →* H) (hf : Function.Surjective f)
    (hker : Nat.Coprime p (Nat.card f.ker)) (g : H) (hg : g ^ p = 1) :
    ∃ x : G, f x = g ∧ x ^ p = 1 := by
  let : Finite H := Finite.of_surjective f hf
  have hp : IsPGroup p (zpowers g) := isPGroup_iff_card_dvd_pow.mpr
    ⟨1,by simpa only [pow_one,Nat.card_zpowers] using orderOf_dvd_of_pow_eq_one hg⟩
  obtain ⟨A,hA,⟨e⟩⟩ := exists_prime_subgroup_equiv_of_surjective_coprime f hf hker (zpowers g) hp
  have hAp : IsPGroup p A := hp.of_equiv e.symm
  obtain ⟨x,hx,hfx⟩ := hA.ge (mem_zpowers g)
  refine ⟨x,hfx,?_⟩
  have hi := injective_comp_subtype_of_coprime_ker f hker A hAp
  have he : (⟨x,hx⟩ : A) ^ p = 1 := by
    apply hi
    change f (x ^ p) = f 1
    rw [map_pow,hfx,hg,map_one]
  exact congrArg Subtype.val he
end Subgroup
