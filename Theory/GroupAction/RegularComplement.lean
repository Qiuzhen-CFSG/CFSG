module

public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Regularity on the complement of a fixed point

If a finite group fixes a point and acts freely elsewhere, and its order
is one less than the degree, its action on that complement is regular.
The orbit map is injective by freeness and surjective by counting.
-/

namespace MulAction

/-- An action free away from a fixed point is regular on its complement when
that complement has the same cardinality as the group. -/
public theorem existsUnique_smul_eq_of_free_complement
    {H X : Type*} [Group H] [Finite H] [Finite X] [MulAction H X]
    (a : X) (ha : ∀ g : H, g • a = a)
    (hfree : ∀ (g : H) (x : X), x ≠ a → g • x = x → g = 1)
    (hcard : Nat.card X = Nat.card H + 1)
    {x y : X} (hx : x ≠ a) (hy : y ≠ a) : ∃! g : H, g • x = y := by
  classical
  let f : H → {z : X // z ≠ a} := fun g => ⟨g • x, fun h => hx (by
    have he := congrArg (g⁻¹ • ·) h
    simpa only [inv_smul_smul, ha] using he)⟩
  have hf : Function.Injective f := by
    intro g k h
    have he : g • x = k • x := congrArg Subtype.val h
    have hfix : (k⁻¹ * g) • x = x := by rw [mul_smul, he, inv_smul_smul]
    have hkg := hfree (k⁻¹ * g) x hx hfix
    exact (inv_mul_eq_one.mp hkg).symm
  have hc : Nat.card {z : X // z ≠ a} = Nat.card H := by
    let := Fintype.ofFinite X
    let := Fintype.ofFinite {z : X // z ≠ a}
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
      Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card, hcard]
    omega
  have hb := (Nat.bijective_iff_injective_and_card f).mpr ⟨hf, hc.symm⟩
  obtain ⟨g, hg⟩ := hb.2 ⟨y, hy⟩
  refine ⟨g, congrArg Subtype.val hg, ?_⟩
  intro k hk
  apply hf
  exact Subtype.ext (hk.trans (congrArg Subtype.val hg).symm)

end MulAction
