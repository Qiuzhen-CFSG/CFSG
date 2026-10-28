module
public import Theory.SpecificGroups.Tits.AutomorphismTwoRank.FourthPower
public import Theory.SpecificGroups.ReeF4.SubfieldTitsEmbedding
public import Theory.SpecificGroups.SymplecticFour.TwoPower

/-!
# Tits and Ree F₄ exclusion from symplectic four-space

The certified Sylow normal form 257 in the Atlas Tits carrier has nontrivial
fourth power. Its membership in a two-group gives a two-power relation, and
the Parrott--Atlas equivalence transports both facts to the actual presented
Tits group. Every two-power element of Sp₄ in characteristic two has fourth
power one, so no faithful homomorphism from this group can exist.

The actual Tits subgroup in every concrete Ree F₄ model gives the same
exclusion by composition. No finiteness assumption on the target field or
centralizer condition is needed.

Sources: Parrott (1972), §5, p.683, via the certified Sylow word;
Aschbacher--Smith G.4.1, printed p.342, for the exceptional-family inspection.
-/

public section
namespace Theory.SpecificGroups.SymplecticFour.NativeTits
open Tits

private theorem exists_two_power_witness :
    ∃ (x : ParrottGroup) (k : ℕ), x ^ (2 ^ k) = 1 ∧ x ^ 4 ≠ 1 := by
  let x : atlas1600SylowTwoSubgroup :=
    ⟨atlas1600SylowTwoNormalForm 257, atlas1600SylowTwoNormalForm_mem 257⟩
  have hp : IsPGroup 2 atlas1600SylowTwoSubgroup :=
    IsPGroup.of_card (n := 11) (by norm_num [atlas1600SylowTwoSubgroup_card])
  obtain ⟨k, hk⟩ := hp x
  have hk' : (x : Atlas1600Group) ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  refine ⟨parrottFiniteImageEquiv.symm x, k, ?_, ?_⟩
  · simpa only [map_pow, map_one] using congrArg parrottFiniteImageEquiv.symm hk'
  · intro h
    have h' := congrArg parrottFiniteImageEquiv h
    simp only [map_pow, MulEquiv.apply_symm_apply, map_one] at h'
    exact AutomorphismTwoRank.FourthPower.sylow_word_fourth_ne_one h'

variable {F : Type*} [Field F] [CharP F 2]

/-- The actual Parrott Tits group has no faithful symplectic four-space action
in characteristic two. -/
theorem model_not_injective (j : ParrottGroup →* Sp F) : ¬ Function.Injective j := by
  intro hj
  obtain ⟨x, k, hx, hx4⟩ := exists_two_power_witness
  have hjx : j x ^ (2 ^ k) = 1 := by rw [← map_pow, hx, map_one]
  apply hx4
  apply hj
  simpa only [map_pow, map_one] using
    TwoPower.pow_four_eq_one_of_pow_two_pow_eq_one (j x) k hjx

/-- The concrete Tits subgroup excludes every Ree F₄ model from a faithful
symplectic four-space action in characteristic two. -/
theorem ree_model_not_injective (m : ℕ) (j : ReeF4.Model m →* Sp F) :
    ¬ Function.Injective j := by
  intro hj
  obtain ⟨f, hf⟩ := ReeF4.Subfield.exists_tits_embedding m
  exact model_not_injective (j.comp f) (hj.comp hf)

end Theory.SpecificGroups.SymplecticFour.NativeTits
