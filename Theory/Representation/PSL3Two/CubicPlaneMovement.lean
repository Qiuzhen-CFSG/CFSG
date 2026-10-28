module
public import Theory.Representation.PSL3Two.SmallModuleProperties
public import Mathlib.Data.Fintype.Card

/-!
# A nonidentity binary-three cubic cannot fix a plane

The literal fixed vectors of each nonidentity cubic in SL3(2) have at most
two elements. An injected subgroup of order four therefore cannot be fixed
pointwise. The argument retains the supplied natural coordinates.
-/
public noncomputable section
open Matrix
open scoped MatrixGroups
namespace BinaryLinearThree

private theorem fixed_count_check : ∀ a : SL(3,ZMod 2), a^3=1 → a≠1 →
    (Finset.univ.filter (fun x : Fin 3 → ZMod 2 => a.val *ᵥ x=x)).card ≤ 2 := by
  decide +kernel

/-- The actual natural fixed vectors of a nonidentity cubic have order at
most two. -/
theorem cubic_fixed_card_le_two (a : SL(3,ZMod 2)) (ha : a^3=1) (hne : a≠1) :
    Nat.card {x : Fin 3 → ZMod 2 // a.val *ᵥ x=x} ≤ 2 := by
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  exact fixed_count_check a ha hne

/-- A natural coordinate injection of an actual four cannot be pointwise
fixed by a nonidentity cubic. -/
theorem cubic_moves_injected_four
    {U : Type*} [Finite U] (hU : Nat.card U=4)
    (j : U → (Fin 3 → ZMod 2)) (hj : Function.Injective j)
    (a : SL(3,ZMod 2)) (ha : a^3=1) (hne : a≠1) :
    ∃ u, a.val *ᵥ j u≠j u := by
  by_contra hh
  push Not at hh
  let f : U → {x : Fin 3 → ZMod 2 // a.val *ᵥ x=x} := fun u => ⟨j u,hh u⟩
  have hi : Function.Injective f := fun u v he => hj (congrArg Subtype.val he)
  have hc := Nat.card_le_card_of_injective f hi
  rw [hU] at hc
  have hb := cubic_fixed_card_le_two a ha hne
  omega

end BinaryLinearThree
