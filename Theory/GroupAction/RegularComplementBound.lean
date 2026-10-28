module
public import Theory.GroupAction.RegularComplement
public import Mathlib.Data.Fintype.Option
/-!
# A free orbit at the cardinality bound

Adjoining the fixed point to a free orbit gives an injection from the
actor group plus one point. An upper bound of the same size therefore
forces equality, which supplies regularity on the complement.
-/
public section
namespace MulAction
variable {A X : Type*} [Group A] [Finite A] [Finite X] [MulAction A X]
/-- A nontrivial free orbit fills an action whose degree is at most the actor order plus one. -/
theorem card_eq_of_free_complement_of_le
    (a : X) (ha : ∀ g : A, g • a = a)
    (hfree : ∀ (g : A) (x : X), x ≠ a → g • x = x → g = 1)
    (hcard : Nat.card X ≤ Nat.card A + 1)
    (hne : ∃ x : X, x ≠ a) : Nat.card X = Nat.card A + 1 := by
  classical
  obtain ⟨x,hx⟩ := hne
  let f : Option A → X := fun g => g.elim a (fun g => g • x)
  have hnot (g : A) : g • x ≠ a := by
    intro he
    have hh := congrArg (g⁻¹ • ·) he
    exact hx (by simpa only [inv_smul_smul,ha] using hh)
  have hi : Function.Injective f := by
    intro g k he
    cases g with
    | none =>
      cases k with
      | none => rfl
      | some k => exact False.elim (hnot k he.symm)
    | some g =>
      cases k with
      | none => exact False.elim (hnot g he)
      | some k =>
        have he' : g • x = k • x := he
        have hfix : (k⁻¹*g) • x = x := by rw [mul_smul,he',inv_smul_smul]
        exact congrArg some (inv_mul_eq_one.mp (hfree _ x hx hfix)).symm
  apply le_antisymm hcard
  have hb := Nat.card_le_card_of_injective f hi
  let := Fintype.ofFinite A
  simpa only [Nat.card_eq_fintype_card,Fintype.card_option] using hb
end MulAction
