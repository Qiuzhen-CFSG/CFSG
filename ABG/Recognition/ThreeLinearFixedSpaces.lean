module

public import ABG.Recognition.ThreeLinearCharacters
public import ABG.Recognition.ThreeLinearIndexBounds
public import Theory.Representation.GeneratedSubgroupInvariants

/-!
# The fixed-space intersection step in Wong's linear branch

The genuine degree-twelve representation of the shared character catalog has
no global fixed vectors, by orthogonality to the principal character. Thus
subgroups with fixed-space dimensions three and two, lying over a common
subgroup with fixed-space dimension four, generate a proper subgroup.

This module supplies the representation-theoretic implication in Wong (1964),
Theorem 6(b), p.110. The construction of the subgroups and the computation of
their fixed-space dimensions are separate group-theoretic inputs.
-/

namespace ABG
open BenderGlauberman
noncomputable section

variable {G : Type*} [Group G] [Finite G]

/-- Wong's order-36 count forces all eight elements of order three to belong
to the class with character value three, and gives a three-dimensional fixed
space. The integer dimension is supplied by the actual representation. -/
public theorem ThreeLinearCharacterData.order36_fixed_dimension
    (c : ThreeLinearCharacterData G) (M : Subgroup G) [Fintype M]
    (hcard : Nat.card M = 36) (n : ℕ) (hn : n ≤ 8)
    (hsum : ∑ x : M, c.decomposition.χ 5 (x : G) = 84 + 3 * (n : ℂ)) :
    n = 8 ∧
      Module.finrank ℂ (Representation.invariants (c.sixthRepresentation.comp M.subtype)) = 3 := by
  let : Invertible (Nat.card M : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have havg := Representation.card_inv_mul_sum_char_eq_finrank
    (c.sixthRepresentation.comp M.subtype)
  have hχ (x : M) : Representation.character (c.sixthRepresentation.comp M.subtype) x =
      c.decomposition.χ 5 (x : G) := by
    rw [c.sixthRepresentation_character]
    rfl
  simp_rw [hχ] at havg
  rw [hcard, hsum] at havg
  norm_num only [Nat.cast_ofNat] at havg
  have heq : (84 : ℂ) + 3 * (n : ℂ) =
      36 * (Module.finrank ℂ (Representation.invariants (c.sixthRepresentation.comp M.subtype)) : ℂ) := by
    linear_combination 36 * havg
  have heqNat : 84 + 3 * n =
      36 * Module.finrank ℂ (Representation.invariants (c.sixthRepresentation.comp M.subtype)) := by
    exact_mod_cast heq
  omega

/-- The nonprincipal catalog character affords a representation with no
global fixed vectors. -/
public theorem ThreeLinearCharacterData.sixth_invariants_eq_bot
    (c : ThreeLinearCharacterData G) : c.sixthRepresentation.invariants = ⊥ := by
  let : Fintype G := Fintype.ofFinite G
  let : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have horth := irreducibleCharacters_orthogonal (c.decomposition.irreducible 5)
    isLinearCharacter_one.1 (c.decomposition.nontrivial 5)
  have hzero : (Module.finrank ℂ c.sixthRepresentation.invariants : ℂ) = 0 := by
    rw [← Representation.card_inv_mul_sum_char_eq_finrank,
      ← c.sixthRepresentation_character]
    simpa only [characterProduct, Pi.one_apply, mul_one] using horth
  exact Submodule.finrank_eq_zero.mp (by exact_mod_cast hzero)

/-- Wong's dimensions `3 + 2 > 4` make the generated subgroup proper. -/
public theorem ThreeLinearCharacterData.sup_ne_top_of_fixed_dimensions
    (c : ThreeLinearCharacterData G) (M C T : Subgroup G)
    (hTM : T ≤ M) (hTC : T ≤ C)
    (hM : Module.finrank ℂ (Representation.invariants (c.sixthRepresentation.comp M.subtype)) = 3)
    (hC : Module.finrank ℂ (Representation.invariants (c.sixthRepresentation.comp C.subtype)) = 2)
    (hT : Module.finrank ℂ (Representation.invariants (c.sixthRepresentation.comp T.subtype)) = 4) :
    M ⊔ C ≠ ⊤ := by
  apply c.sixthRepresentation.sup_ne_top_of_invariants_dimension
    c.sixth_invariants_eq_bot M C T hTM hTC
  rw [hM, hC, hT]
  decide

/-- The actual generated subgroup from Wong's fixed-space configuration has
index thirteen or thirty-nine. -/
public theorem ThreeLinearCharacterData.sup_index_alternatives
    [IsSimpleGroup G] (c : ThreeLinearCharacterData G) (M C T : Subgroup G)
    (hTM : T ≤ M) (hTC : T ≤ C)
    (hMcard : Nat.card M = 36) (hCcard : Nat.card C = 48)
    (hM : Module.finrank ℂ (Representation.invariants (c.sixthRepresentation.comp M.subtype)) = 3)
    (hC : Module.finrank ℂ (Representation.invariants (c.sixthRepresentation.comp C.subtype)) = 2)
    (hT : Module.finrank ℂ (Representation.invariants (c.sixthRepresentation.comp T.subtype)) = 4) :
    (M ⊔ C).index = 13 ∨ (M ⊔ C).index = 39 := by
  exact index_thirteen_or_thirtynine_of_subgroup_orders c.group_order M C (M ⊔ C)
    hMcard hCcard le_sup_left le_sup_right
    (c.sup_ne_top_of_fixed_dimensions M C T hTM hTC hM hC hT)

end
end ABG
