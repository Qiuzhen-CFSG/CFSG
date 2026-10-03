module
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Automorphisms fixing a point in a group of order four

An automorphism subgroup of a group of order four has order at most two
if it fixes a specified nonidentity element. It already fixes the identity,
so it preserves the remaining two-point set. Restricting the action to that
set is faithful, and its permutation group has order two.

This elementary bound requires no commutativity or exponent assumption on
the group. It supplies the normalizer-action bound in the finite-group
identification of the bounded exceptional case of Stellmacher (1.6),
journal p.18, `refs/latex/stellmacher-n-group.tex`.
-/

public theorem card_mulAut_subgroup_le_two_of_fixed_point
    {S : Type*} [Group S] [Finite S] (hS : Nat.card S = 4)
    (z : S) (hz : z ≠ 1) (H : Subgroup (MulAut S))
    (hfix : ∀ f ∈ H, f z = z) : Nat.card H ≤ 2 := by
  classical
  let _ := Fintype.ofFinite S
  let X : SubMulAction H S := {
    carrier := ({1,z} : Set S)ᶜ
    smul_mem' := by
      intro f x hx
      have hx' : x ≠ 1 ∧ x ≠ z := by simpa using hx
      change (f : MulAut S) x ∉ ({1,z} : Set S)
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      constructor
      · intro hh
        exact hx'.1 ((f : MulAut S).injective (hh.trans (map_one (f : MulAut S)).symm))
      · intro hh
        exact hx'.2 ((f : MulAut S).injective (hh.trans (hfix f f.property).symm)) }
  let ρ : H →* Equiv.Perm X := MulAction.toPermHom H X
  have hinj : Function.Injective ρ := by
    intro f g hfg
    apply Subtype.ext
    ext x
    by_cases hx1 : x = 1
    · simp [hx1]
    by_cases hxz : x = z
    · simpa only [hxz] using (hfix f f.property).trans (hfix g g.property).symm
    have hx : x ∈ X := by
      change x ∉ ({1,z} : Set S)
      simp [hx1,hxz]
    exact congrArg Subtype.val (Equiv.congr_fun hfg (⟨x,hx⟩ : X))
  have hXcard : Nat.card X = 2 := by
    change Nat.card ↥(({1,z} : Set S)ᶜ) = 2
    rw [Nat.card_eq_fintype_card, Fintype.card_compl_set]
    have hc : Fintype.card S = 4 := by simpa only [Nat.card_eq_fintype_card] using hS
    simp [hc, hz.symm]
  have hcard := Nat.card_le_card_of_injective ρ hinj
  rw [Nat.card_eq_fintype_card (α := Equiv.Perm X), Fintype.card_perm,
    ← Nat.card_eq_fintype_card, hXcard] at hcard
  exact hcard

