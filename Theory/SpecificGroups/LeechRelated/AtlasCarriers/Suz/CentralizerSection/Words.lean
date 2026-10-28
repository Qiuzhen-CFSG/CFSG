module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Suz
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Words for the Suz involution centralizer

The candidate involution is `(ab ab abb)^6`. Two Bray words will induce the
27-point quotient action. All words are elements of the fixed degree-1782
carrier by construction; their orders and actions are proved in `Action`.
Source: the retained ATLAS SuzG1-p1782B0 generators; application: GLS3 Table
5.3o and Aschbacher--Smith A.2.19, printed pp.40--41.
-/

@[expose] public section
namespace Sporadic.LeechRelated.Suz.CentralizerSection

@[irreducible] def a : Carrier := ⟨generatorA, Subgroup.subset_closure (by simp)⟩
@[irreducible] def b : Carrier := ⟨generatorB, Subgroup.subset_closure (by simp)⟩

theorem inclusion_a : inclusion a = generatorA := by unfold a; rfl
theorem inclusion_b : inclusion b = generatorB := by unfold b; rfl

@[irreducible] def word : Carrier := a * b * a * b * a * b ^ 2
@[irreducible] def involution : Carrier := word ^ 6
@[irreducible] def u : Carrier := b * a * b * a
@[irreducible] def v : Carrier := a * b * a * b ^ 2 * a * b * a * b ^ 2 * a * b

/-- The first Bray word, written in the original generators. -/
@[irreducible] def c : Carrier := u * (involution * u⁻¹ * involution * u)
/-- The second Bray word, written in the original generators. -/
@[irreducible] def d : Carrier := v * (involution * v⁻¹ * involution * v) ^ 2

end Sporadic.LeechRelated.Suz.CentralizerSection
