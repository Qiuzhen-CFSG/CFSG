module

public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel

/-!
# Small coordinate certificates for binary four-group fixed spaces

A list of 21 conjugators covers all nonidentity involutions in SL₃(2).
After normalizing one generator to I + E₀₂, a second independent commuting
involution fixes, together with it, eight pairs of column and row vectors.
The simultaneous pointwise fixer consists of precisely the generated four-group.
All finite assertions are checked by kernel reduction on the actual matrices;
no subgroup catalogue or external computation is assumed.

The row condition uses right multiplication, which the parent module identifies
with fixedness in the literal contragredient module using the dot product.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), the final
paragraph proving 15.3.61(2), printed p.1151.
-/

@[expose] public section
open Matrix
namespace BinaryLinearThree.FourGroupGeometry.FixedSpaces

/-- A standard binary transvection, shared by the point and line four-groups. -/
def involution : Matrix.PSL3Two.SL := ⟨!![1,0,1;0,1,0;0,0,1], by decide⟩

private def conjugators : Fin 21 → Matrix.PSL3Two.SL := ![
  ⟨!![1,0,0;0,1,0;0,0,1], by decide⟩,
  ⟨!![0,0,1;0,1,0;1,0,0], by decide⟩,
  ⟨!![0,0,1;1,0,0;0,1,0], by decide⟩,
  ⟨!![0,0,1;1,0,0;1,1,0], by decide⟩,
  ⟨!![0,1,0;0,0,1;1,0,0], by decide⟩,
  ⟨!![0,1,0;0,1,1;1,0,0], by decide⟩,
  ⟨!![0,1,0;1,0,0;0,0,1], by decide⟩,
  ⟨!![0,1,0;1,0,0;0,1,1], by decide⟩,
  ⟨!![0,1,0;1,0,0;1,0,1], by decide⟩,
  ⟨!![0,1,0;1,0,0;1,1,1], by decide⟩,
  ⟨!![1,0,0;0,0,1;0,1,0], by decide⟩,
  ⟨!![1,0,0;0,0,1;1,1,0], by decide⟩,
  ⟨!![1,0,0;0,1,0;0,1,1], by decide⟩,
  ⟨!![1,0,0;0,1,0;1,0,1], by decide⟩,
  ⟨!![1,0,0;0,1,0;1,1,1], by decide⟩,
  ⟨!![1,0,0;1,0,1;0,1,0], by decide⟩,
  ⟨!![1,0,0;1,0,1;1,1,0], by decide⟩,
  ⟨!![1,0,0;1,1,0;0,0,1], by decide⟩,
  ⟨!![1,0,0;1,1,0;0,1,1], by decide⟩,
  ⟨!![1,0,0;1,1,0;1,0,1], by decide⟩,
  ⟨!![1,0,0;1,1,0;1,1,1], by decide⟩]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
private theorem involution_test : ∀ a : Matrix.PSL3Two.SL, a ≠ 1 → a * a = 1 →
    ∃ i : Fin 21, a * conjugators i = conjugators i * involution := by decide +kernel

/-- Simultaneous fixedness of a column vector and a row vector. -/
def fixes (g : Matrix.PSL3Two.SL) (w : (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2)) : Prop :=
  g.val *ᵥ w.1 = w.1 ∧ w.2 ᵥ* g.val = w.2
instance (g : Matrix.PSL3Two.SL) (w : (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2)) :
    Decidable (fixes g w) := inferInstanceAs (Decidable (_ ∧ _))

/-- Common fixed pairs for a normalized pair of generators. -/
def pairFixed (b : Matrix.PSL3Two.SL) (w : (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2)) : Prop :=
  fixes involution w ∧ fixes b w
instance (b : Matrix.PSL3Two.SL) (w : (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2)) :
    Decidable (pairFixed b w) := inferInstanceAs (Decidable (_ ∧ _))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
/-- Two independent commuting involutions fix eight column-row pairs. -/
theorem card_pairFixed : ∀ b : Matrix.PSL3Two.SL,
    b ≠ 1 → b ≠ involution → b * b = 1 → b * involution = involution * b →
    Fintype.card {w : (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2) // pairFixed b w} = 8 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
/-- The common fixed pairs determine their acting four-group pointwise. -/
theorem mem_four_of_fixes_pairFixed : ∀ b : Matrix.PSL3Two.SL,
    b ≠ 1 → b ≠ involution → b * b = 1 → b * involution = involution * b →
    ∀ g : Matrix.PSL3Two.SL, (∀ w : (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2), pairFixed b w → fixes g w) →
      g = 1 ∨ g = involution ∨ g = b ∨ g = involution * b := by decide +kernel

/-- Every nonidentity involution is conjugate to the standard transvection. -/
theorem exists_involution_conjugator (a : Matrix.PSL3Two.SL)
    (ha : a ≠ 1) (hsq : a * a = 1) :
    ∃ g : Matrix.PSL3Two.SL, a * g = g * involution := by
  obtain ⟨i, hi⟩ := involution_test a ha hsq
  exact ⟨conjugators i, hi⟩

end BinaryLinearThree.FourGroupGeometry.FixedSpaces
