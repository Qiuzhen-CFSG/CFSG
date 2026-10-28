module

public import ABG.Recognition.ThreeMathieuCharacterValues
public import Theory.Representation.GeneratedSubgroupInvariants
public import Theory.Representation.CharacterFixedDimension

/-!
# The fixed-space intersection in Wong's Mathieu branch

The first character of the shared catalog affords a representation of degree
ten with no global fixed vectors. Character sums on subgroups compute their
fixed dimensions. Dimensions `3 + 2 > 4` over a common subgroup imply that
the quaternion subgroup and the Sylow-five normalizer generate a proper
subgroup. The local subgroup construction supplies these character sums.

Source: Wong (1964), Theorem 6(a), pp.107–108,
DOI 10.1017/S1446788700022771.
-/

namespace ABG
open BenderGlauberman
open scoped BigOperators
noncomputable section

variable {G : Type*} [Group G] [Finite G] (c : ThreeGlobalDegreeData G)

/-- An actual representation affording the same first character used in the
class census, without choosing a new character catalog. -/
public theorem ThreeGlobalDegreeData.exists_first_mathieu_representation
    (hG : Nat.card G = 7920) :
    ∃ ρ : Representation ℂ G (Fin 10 → ℂ),
      Representation.IsIrreducible ρ ∧ c.decomposition.χ 0 = ρ.character := by
  obtain ⟨n, ρ, hρ, hχ⟩ := c.decomposition.irreducible 0
  have hn : n = 10 := by
    have h := c.first_character_identity hG
    rw [hχ, Representation.char_one] at h
    simp only [Module.finrank_pi, Fintype.card_fin] at h
    exact_mod_cast h
  subst n
  exact ⟨ρ, hρ, hχ⟩

variable (ρ : Representation ℂ G (Fin 10 → ℂ))
    (hχ : c.decomposition.χ 0 = ρ.character)

include hχ

/-- Orthogonality to the principal character rules out global fixed vectors. -/
public theorem ThreeGlobalDegreeData.first_mathieu_invariants_eq_bot :
    ρ.invariants = ⊥ := by
  let : Fintype G := Fintype.ofFinite G
  let : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have horth := irreducibleCharacters_orthogonal (c.decomposition.irreducible 0)
    isLinearCharacter_one.1 (c.decomposition.nontrivial 0)
  have hzero : (Module.finrank ℂ ρ.invariants : ℂ) = 0 := by
    rw [← Representation.card_inv_mul_sum_char_eq_finrank, ← hχ]
    simpa only [characterProduct, Pi.one_apply, mul_one] using horth
  exact Submodule.finrank_eq_zero.mp (by exact_mod_cast hzero)

/-- Compute a subgroup's fixed dimension using the catalog's character sum. -/
public theorem ThreeGlobalDegreeData.first_mathieu_fixed_dimension
    (H : Subgroup G) [Fintype H] (d : ℕ)
    (hsum : ∑ x : H, c.decomposition.χ 0 (x : G) = (Nat.card H : ℂ) * (d : ℂ)) :
    Module.finrank ℂ (Representation.invariants (ρ.comp H.subtype)) = d := by
  apply Representation.finrank_invariants_eq_of_sum_character
  simpa only [hχ, Representation.character, MonoidHom.comp_apply, Subgroup.subtype_apply] using hsum

/-- Wong's dimensions force the generated subgroup to be proper. -/
public theorem ThreeGlobalDegreeData.mathieu_sup_ne_top_of_fixed_dimensions
    (Q N F : Subgroup G) (hFQ : F ≤ Q) (hFN : F ≤ N)
    (hQ : Module.finrank ℂ (Representation.invariants (ρ.comp Q.subtype)) = 3)
    (hN : Module.finrank ℂ (Representation.invariants (ρ.comp N.subtype)) = 2)
    (hF : Module.finrank ℂ (Representation.invariants (ρ.comp F.subtype)) = 4) :
    Q ⊔ N ≠ ⊤ := by
  apply ρ.sup_ne_top_of_invariants_dimension
    (c.first_mathieu_invariants_eq_bot ρ hχ) Q N F hFQ hFN
  rw [hQ, hN, hF]
  decide

end
end ABG
