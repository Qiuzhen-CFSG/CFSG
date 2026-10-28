module

public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.FourNormalizers.Geometry

/-!
# Selecting the four-group fixed by a transposition

Conjugate the transposition to (56), and transport the marked four-group.
Its normalizer is the transposition fixed subgroup. A Sylow two-subgroup
centralized by the transposition normalizes this four-group; Sylow maximality
then puts the four-group inside it.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined 1 March 2004 manuscript, printed pp.567–570.
-/

@[expose] public section

open Subgroup GLS3.Chapter5
namespace AlternatingSix.ShadowLocal.FourNormalizers

theorem fixed_subgroup_map (β α : AutA6) :
    (automorphismFixedSubgroup β).map α.toMonoidHom =
      automorphismFixedSubgroup (α * β * α⁻¹) := by
  ext x
  rw [mem_map_equiv]
  change β (α.symm x) = α.symm x ↔ α (β (α.symm x)) = x
  rw [← α.injective.eq_iff, α.apply_symm_apply]

/-- A transposition centralizing a Sylow two-subgroup selects a four-group
whose entire A₆ normalizer it fixes. -/
theorem exists_four_normalizer_eq_fixed (Q : Sylow 2 A6)
    (σ : Equiv.Perm (Fin 6)) (hσ : σ.IsSwap)
    (hfix : ∀ q ∈ (Q : Subgroup A6), permutationAction σ q = q) :
    ∃ E : Subgroup A6, IsKleinFour E ∧ E ≤ (Q : Subgroup A6) ∧
      normalizer (E : Set A6) = automorphismFixedSubgroup (permutationAction σ) := by
  obtain ⟨a, b, hab, rfl⟩ := hσ
  obtain ⟨g, hg⟩ := isConj_iff.mp (Equiv.Perm.isConj_swap (by decide : (4 : Fin 6) ≠ 5) hab)
  let α := permutationAction g
  let E := standardFour.map α.toMonoidHom
  let e := standardFour.equivMapOfInjective α.toMonoidHom α.injective
  have hE : IsKleinFour E := {
    card_four := (Nat.card_congr e.toEquiv).symm.trans IsKleinFour.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv e).symm.trans IsKleinFour.exponent_two }
  have hα : α * permutationAction tailSwap * α⁻¹ = permutationAction (Equiv.swap a b) := by
    change permutationAction g * permutationAction tailSwap * (permutationAction g)⁻¹ = _
    rw [← map_inv, ← map_mul, ← map_mul]
    exact congrArg permutationAction hg
  have hN : normalizer (E : Set A6) =
      automorphismFixedSubgroup (permutationAction (Equiv.swap a b)) := by
    change normalizer (standardFour.map α.toMonoidHom : Set A6) = _
    rw [← map_equiv_normalizer_eq, standard_normalizer_eq_fixed, fixed_subgroup_map, hα]
  have hQN : (Q : Subgroup A6) ≤ normalizer (E : Set A6) := by
    rw [hN]
    exact hfix
  have hp : IsPGroup 2 E := IsPGroup.of_card (show Nat.card E = 2 ^ 2 from hE.card_four)
  have hsup : (Q : Subgroup A6) ⊔ E = (Q : Subgroup A6) :=
    Q.is_maximal' (Q.isPGroup'.to_sup_of_normal_right' hp hQN) le_sup_left
  exact ⟨E, hE, sup_eq_left.mp hsup, hN⟩
end AlternatingSix.ShadowLocal.FourNormalizers
