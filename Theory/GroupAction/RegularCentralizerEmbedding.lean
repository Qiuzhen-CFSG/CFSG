module

public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Embedding a commuting group through a regular action

Suppose `H` acts regularly on a nonempty set `S`, and a second group `J`
acts faithfully on `S` and commutes with `H`. Fixing `a ∈ S`, send `j` to
the unique `h ∈ H` with `h • a = j⁻¹ • a`. This is an injective group
homomorphism. The inverse is essential: evaluation of the commuting action
itself gives a homomorphism into the opposite group `Hᵐᵒᵖ`.

The set need only be a subset of an ambient action; this lets applications
retain their original action and literal points. Source: the regular-action
centralizer theorem, GLS, Volume 2, Chapter 1, Lemma 2.10, as used in GLS,
Volume 4, Chapter 2, Lemma 12.14(b).
-/

noncomputable section
namespace MulAction

/-- A faithful action commuting with a regular action embeds in the regular group;
the construction uses inverse evaluation to account for the opposite group. -/
public theorem exists_injective_hom_of_commuting_regular_action
    {H J X : Type*} [Group H] [Group J] [MulAction H X] [MulAction J X]
    (S : Set X) (a : X) (ha : a ∈ S)
    (hregular : ∀ b ∈ S, ∀ c ∈ S, ∃! h : H, h • b = c)
    (hpreserve : ∀ j : J, ∀ b ∈ S, j • b ∈ S)
    (hcommute : ∀ (h : H) (j : J) (b : X), h • (j • b) = j • (h • b))
    (hfaithful : ∀ j : J, (∀ b ∈ S, j • b = b) → j = 1) :
    ∃ f : J →* H, Function.Injective f := by
  classical
  have hex (j : J) : ∃! h : H, h • a = j⁻¹ • a :=
    hregular a ha (j⁻¹ • a) (hpreserve j⁻¹ a ha)
  let f : J → H := fun j => (hex j).choose
  have hf (j : J) : f j • a = j⁻¹ • a := (hex j).choose_spec.1
  have huniq (j : J) (h : H) (hh : h • a = j⁻¹ • a) : h = f j :=
    (hex j).choose_spec.2 h hh
  let φ : J →* H :=
    { toFun := f
      map_one' := (huniq 1 1 (by simp)).symm
      map_mul' := by
        intro j k
        symm
        apply huniq
        rw [mul_smul, hf k, hcommute, hf j, ← mul_smul, mul_inv_rev] }
  refine ⟨φ, φ.ker_eq_bot_iff.mp ?_⟩
  apply le_antisymm _ bot_le
  intro j hj
  change φ j = 1 at hj
  have hja : j • a = a := by
    have hh := hf j
    change φ j • a = j⁻¹ • a at hh
    rw [hj, one_smul] at hh
    exact (inv_smul_eq_iff.mp hh.symm).symm
  apply hfaithful j
  intro b hb
  obtain ⟨h, hh, _⟩ := hregular a ha b hb
  rw [← hh, ← hcommute, hja]

end MulAction

