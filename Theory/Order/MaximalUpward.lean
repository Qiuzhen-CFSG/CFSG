module

public import Mathlib.Order.Preorder.Finite

/-!
# Maximal elements satisfying an upward-closed condition

An upward-closed condition inside a finite family passes to maximal overobjects.
Moreover its restricted family's maximal elements are exactly the maximal
members of the original family satisfying the condition. This is the order
argument in Aschbacher–Smith, *The Classification of Quasithin Groups*,
Lemma 1.2.9(2), printed p. 507: the faithful subfamily is upward closed by (1).
-/

namespace Theory

/-- An upward-closed condition on a family does not change its maximal elements. -/
public theorem maximal_and_iff_of_upward_closed {α : Type*} [Preorder α]
    {P Q : α → Prop} {a : α}
    (hQ : ∀ ⦃x y⦄, P x → P y → Q x → x ≤ y → Q y) :
    Maximal (fun x => P x ∧ Q x) a ↔ Maximal P a ∧ Q a := by
  constructor
  · intro h
    exact ⟨⟨h.1.1, fun _ hy hay => h.2 ⟨hy, hQ h.1.1 hy h.1.2 hay⟩ hay⟩, h.1.2⟩
  · rintro ⟨h, ha⟩
    exact ⟨⟨h.1, ha⟩, fun _ hy hay => h.2 hy.1 hay⟩

/-- A member satisfying an upward-closed condition lies below a maximal member
of the original family satisfying the same condition. -/
public theorem exists_maximal_above_of_upward_closed {α : Type*} [Preorder α] [Finite α]
    {P Q : α → Prop} {a : α}
    (hQ : ∀ ⦃x y⦄, P x → P y → Q x → x ≤ y → Q y) (ha : P a) (hQa : Q a) :
    ∃ b, a ≤ b ∧ Maximal P b ∧ Q b := by
  obtain ⟨b, hab, hb⟩ := Finite.exists_le_maximal ha
  exact ⟨b, hab, hb, hQ ha hb.1 hQa hab⟩

end Theory
