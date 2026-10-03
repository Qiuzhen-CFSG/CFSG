module

public import Theory.SpecificGroups.ReeTwo.Action

/-!
# Transporting normalized core actions to root relations

An actual core homomorphism intertwining the specified five- and four-actions
supplies root 1 as the inverse four-element and the Weyl element as a²c.
This converts left conjugation to Shinoda's right-commutator convention and
verifies all complement relations without a generation hypothesis.

Source: Shinoda (1975), pp.81–83, through `RootAction` and `Action`.
-/

@[expose] public section
namespace ReeTwo
/-- Convert left conjugation by the normalized five-by-four generators to
Shinoda's right-commutator and Weyl conventions. -/
theorem root_relations_of_normalized_action
    {H : Type*} [Group H] (f : Core →* H) (a c : H)
    (ha4 : a ^ 4 = 1) (hc5 : c ^ 5 = 1) (hac : a * c * a⁻¹ = c ^ 2)
    (ha : ∀ q, a * f q * a⁻¹ = f (Core.a q))
    (hc : ∀ q, c * f q * c⁻¹ = f (Core.c q)) :
    CoreRelations (fun i => f (Core.root i)) ∧
    RootOneRelations a⁻¹ (fun i => f (Core.root i)) ∧
    (∀ i, (a ^ 2 * c) * f (Core.root i) * (a ^ 2 * c)⁻¹ =
      f (Core.root (weylRoot i))) ∧
    (((a⁻¹)⁻¹) ^ 2 * (a ^ 2 * c)) ^ 5 = 1 ∧
    ((a⁻¹)⁻¹) ^ 4 = 1 ∧
    (a⁻¹)⁻¹ * (((a⁻¹)⁻¹) ^ 2 * (a ^ 2 * c)) * ((a⁻¹)⁻¹)⁻¹ =
      (((a⁻¹)⁻¹) ^ 2 * (a ^ 2 * c)) ^ 2 := by
  have hprod : a ^ 2 * (a ^ 2 * c) = c := by
    rw [← mul_assoc, ← pow_add, show 2 + 2 = 4 from rfl, ha4, one_mul]
  refine ⟨Core.relations.map f, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    have hh := ha (Core.root i)
    rw [Core.a_root, map_mul, map_inv, map_rootWord] at hh
    simp only [rightComm, inv_inv]
    calc
      _ = (a * f (Core.root i) * a⁻¹)⁻¹ * f (Core.root i) := by group
      _ = _ := by rw [hh]; group
  · intro i
    have har : Core.a ^ 2 * Core.c = Core.r := by
      rw [Core.c, ← mul_assoc, ← pow_add, show 2 + 2 = 4 from rfl,
        Core.a_four, one_mul]
    calc
      (a ^ 2 * c) * f (Core.root i) * (a ^ 2 * c)⁻¹ =
          a * (a * (c * f (Core.root i) * c⁻¹) * a⁻¹) * a⁻¹ := by simp only [pow_two]; group
      _ = f (Core.a (Core.a (Core.c (Core.root i)))) := by rw [hc, ha, ha]
      _ = f ((Core.a ^ 2 * Core.c) (Core.root i)) := by
        congr 1
      _ = f (Core.root (weylRoot i)) := by rw [har, Core.r_root]
  · simpa only [inv_inv, hprod] using hc5
  · simpa only [inv_inv] using ha4
  · simpa only [inv_inv, hprod] using hac
end ReeTwo
