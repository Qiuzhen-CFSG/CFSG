module
public import Theory.GroupAction.AutomorphismFixerCardinality.Transport
public import Mathlib.GroupTheory.Sylow
/-!
# Cardinality bounds for pointwise Sylow fixers

If every pointwise Sylow fixer is conjugation by an element of that Sylow,
the fixer group is an image of its center. The bound transfers to every Sylow
by conjugacy. This supplies the ordinary binary linear and Tits model bounds
in Aschbacher–Smith 15.1.22(**), printed p.1099.
-/
public section
open Subgroup
namespace Theory.GroupAction
variable {X : Type*} [Group X] [Finite X]

theorem sylow_fixer_card_le_center_of_inner (P : Sylow 2 X)
    (hinner : ∀ a : MulAut X, (∀ x ∈ P, a x = x) → ∃ g ∈ P, a = MulAut.conj g)
    (A : Subgroup (MulAut X)) (hfix : ∀ a ∈ A, ∀ x ∈ P, a x = x) :
    Nat.card A ≤ Nat.card (center P) := by
  let f : center P →* MulAut X := MulAut.conj.comp
    ((P : Subgroup X).subtype.comp (center P).subtype)
  have hle : A ≤ f.range := by
    intro a ha
    obtain ⟨g,hg,he⟩ := hinner a (hfix a ha)
    have hc : (⟨g,hg⟩ : P) ∈ center P := by
      apply mem_center_iff.mpr
      intro x
      apply Subtype.ext
      have hh := hfix a ha x x.property
      rw [he, MulAut.conj_apply] at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    exact ⟨⟨⟨g,hg⟩,hc⟩,he.symm⟩
  exact (card_le_of_le hle).trans
    (Nat.card_le_card_of_surjective f.rangeRestrict f.rangeRestrict_surjective)

theorem sylow_fixer_card_le_of_standard (P : Sylow 2 X) (n : ℕ)
    (hb : ∀ A : Subgroup (MulAut X), (∀ a ∈ A, ∀ x ∈ P, a x = x) → Nat.card A ≤ n)
    (Q : Sylow 2 X) (A : Subgroup (MulAut X))
    (hfix : ∀ a ∈ A, ∀ x ∈ Q, a x = x) : Nat.card A ≤ n := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq X Q P
  have hp : (Q : Subgroup X).map (MulAut.conj g).toMonoidHom = P :=
    congrArg Sylow.toSubgroup hg
  exact automorphism_fixer_card_le_of_equiv (MulAut.conj g) Q P hp n hb A hfix
end Theory.GroupAction
