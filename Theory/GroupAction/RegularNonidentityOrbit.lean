module

public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Fintype.Option

/-!
# A free action on all nonidentity elements

If a finite group acts by automorphisms on a finite group with one more
element, and every nonidentity actor fixes only the identity, then the
action is transitive on the nonidentity elements. Adjoin the identity to
one free orbit and compare cardinalities.

This elementary orbit argument is used for the root group and the moving
quotient in GLS, Volume 4, Chapter 2, Lemmas 15.6–15.7.
-/

namespace Theory.GroupAction

/-- A free orbit accounts for all nonidentity elements when the orders differ
by one. No commutativity or coprime-action theorem is needed for this count. -/
public theorem exists_smul_eq_of_free_of_card
    {K P : Type*} [Group K] [Group P] [Finite K] [Finite P]
    [MulDistribMulAction K P]
    (hcard : Nat.card P = Nat.card K + 1)
    (hfree : ∀ k : K, k ≠ 1 → ∀ x : P, k • x = x → x = 1)
    {x y : P} (hx : x ≠ 1) (hy : y ≠ 1) : ∃ k : K, k • x = y := by
  classical
  let : Fintype K := Fintype.ofFinite K
  let : Fintype P := Fintype.ofFinite P
  let f : Option K → P := fun a => a.elim 1 (fun k => k • x)
  have hnot : ∀ k : K, k • x ≠ 1 := by
    intro k hk
    exact hx ((MulDistribMulAction.toMulEquiv P k).injective
      (hk.trans (smul_one k).symm))
  have hinj : Function.Injective f := by
    intro a b hab
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some b => exact False.elim (hnot b hab.symm)
    | some a =>
      cases b with
      | none => exact False.elim (hnot a hab)
      | some b =>
        have he : (b⁻¹ * a) • x = x := by
          change a • x = b • x at hab
          rw [mul_smul, hab, inv_smul_smul]
        have hone : b⁻¹ * a = 1 := by
          by_contra hn
          exact hx (hfree _ hn _ he)
        exact congrArg some (inv_mul_eq_one.mp hone).symm
  have hc : Nat.card P ≤ Nat.card (Option K) := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_option] using hcard.le
  obtain ⟨a, ha⟩ := (hinj.bijective_of_nat_card_le hc).surjective y
  cases a with
  | none => exact False.elim (hy ha.symm)
  | some k => exact ⟨k, ha⟩

end Theory.GroupAction
