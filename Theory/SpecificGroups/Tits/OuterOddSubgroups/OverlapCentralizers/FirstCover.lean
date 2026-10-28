module

public import Theory.SpecificGroups.Tits.ReeLocalBlockOrders

/-!
# Five cosets of the Sylow subgroup in the first Tits parabolic

The rotation `s1 * r1` has order five. Its cyclic subgroup intersects the
Sylow two-subgroup trivially, so the 2048 times five products are distinct.
The established parabolic order 10240 then makes this a complete cover.

Source: Parrott (1972), p.683, relation VI(ii), and the marked parabolic
order proved in `ReeLocalBlockOrders`.
-/

@[expose] public section
namespace Tits.OuterOddSubgroups.OverlapCentralizers
open Subgroup ExceptionalParabolics

private theorem s1_mem : atlas1600ParrottAssignment .s1 ∈ S := by
  rw [S, atlas1600SylowTwoSubgroup_eq]
  exact subset_closure (by simp)

/-- The order-five rotation in the first marked parabolic. -/
def firstRotation : Atlas1600Group :=
  atlas1600ParrottAssignment .s1 * atlas1600ParrottAssignment .r1

private theorem firstRotation_mem : firstRotation ∈ first :=
  first.mul_mem (sylow_le_first s1_mem) reflection_mem_first

theorem firstRotation_order : orderOf firstRotation = 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  apply orderOf_eq_prime
  · simpa only [firstRotation, parrottRelator, map_pow, map_mul,
      FreeGroup.lift_apply_of] using atlas1600ParrottAssignment_relations .vi_s1_r1
  · intro h
    have hp := congrArg (fun x : Atlas1600Group => x.val 0) h
    have hv : firstRotation.val =
        Atlas1600ParrottData.s1Perm * Atlas1600ParrottData.r1Perm := by
      change (atlas1600ParrottAssignment .s1).val *
        (atlas1600ParrottAssignment .r1).val = _
      simp only [atlas1600ParrottAssignment_val, Atlas1600ParrottData.permutation]
    rw [hv] at hp
    exact (by decide +kernel :
      (Atlas1600ParrottData.s1Perm * Atlas1600ParrottData.r1Perm) 0 ≠ 0) hp

/-- Products of the certified Sylow normal forms with the five rotation powers. -/
def firstNormalForm (p : Fin 2048 × Fin 5) : first :=
  ⟨atlas1600SylowTwoNormalForm p.1 * firstRotation ^ p.2.val,
    first.mul_mem (sylow_le_first (atlas1600SylowTwoNormalForm_mem _))
      (by exact first.pow_mem firstRotation_mem _)⟩

@[simp] theorem firstNormalForm_val (p : Fin 2048 × Fin 5) :
    (firstNormalForm p).val = atlas1600SylowTwoNormalForm p.1 * firstRotation ^ p.2.val := rfl

private theorem firstNormalForm_injective : Function.Injective firstNormalForm := by
  have hd : Disjoint S (zpowers firstRotation) := disjoint_of_coprime_natCard (by
    rw [sylow_card, Nat.card_zpowers, firstRotation_order]
    decide)
  intro p q hpq
  have hmul :
      ((⟨atlas1600SylowTwoNormalForm p.1, atlas1600SylowTwoNormalForm_mem _⟩ : S),
        (⟨firstRotation ^ p.2.val, pow_mem (mem_zpowers _) _⟩ : zpowers firstRotation)) =
      ((⟨atlas1600SylowTwoNormalForm q.1, atlas1600SylowTwoNormalForm_mem _⟩ : S),
        (⟨firstRotation ^ q.2.val, pow_mem (mem_zpowers _) _⟩ : zpowers firstRotation)) :=
    mul_injective_of_disjoint hd (congrArg Subtype.val hpq)
  apply Prod.ext
  · exact atlas1600SylowTwoNormalForm_injective
      (congrArg (fun z : S × zpowers firstRotation => z.1.val) hmul)
  · apply Fin.ext
    apply pow_injOn_Iio_orderOf (x := firstRotation)
      (by simpa only [Set.mem_Iio, firstRotation_order] using p.2.isLt)
      (by simpa only [Set.mem_Iio, firstRotation_order] using q.2.isLt)
    exact congrArg (fun z : S × zpowers firstRotation => z.2.val) hmul

/-- Every element of the first parabolic has one of the five-coset normal forms. -/
theorem firstNormalForm_surjective : Function.Surjective firstNormalForm :=
  (firstNormalForm_injective.bijective_of_nat_card_le (by
    rw [ReeLocalBlockOrders.first_card, Nat.card_prod, Nat.card_fin, Nat.card_fin])).2

end Tits.OuterOddSubgroups.OverlapCentralizers
end
