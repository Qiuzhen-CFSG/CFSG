module

public import Theory.Character.AbelianLinearCharacters

/-!
# Twisting complex characters by linear characters

Scalar multiplication of the representing operators realizes the pointwise
product with a complex homomorphism. The homomorphism has unit norm on a
finite group, so twisting preserves the character norm and irreducibility.

This is the elementary linear-character twist used in Lyons,
*A Characterization of the Group U₃(4)* (1972), Lemma 4, p. 381.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
attribute [local instance] Fintype.ofFinite
namespace Representation
variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
/-- Scalar twist on the original representation space. -/
def linearTwist (ρ : Representation ℂ G V) (χ : G →* ℂ) : Representation ℂ G V :=
  { toFun := fun g => χ g • ρ g
    map_one' := by simp
    map_mul' := by intro g h; simp [smul_smul, mul_comm] }
/-- The character of the scalar twist is the pointwise product. -/
theorem linearTwist_character [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (χ : G →* ℂ) (g : G) :
    (linearTwist ρ χ).character g = χ g * ρ.character g := by
  simp [character, linearTwist]
end Representation
namespace MonoidHom
variable {G : Type*} [Group G]
/-- The class function of a complex one-dimensional character. -/
def characterClass (χ : G →* ℂ) : ConjClassFunction G :=
  toConjClassFunction χ (by
    intro g h
    simp only [map_mul]
    rw [mul_comm (χ h) (χ g), mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one])
@[simp] theorem characterClass_apply (χ : G →* ℂ) (g : G) :
    χ.characterClass (ConjClasses.mk g) = χ g := rfl
/-- Finite-group linear characters take values of unit norm. -/
theorem apply_mul_star [Finite G] (χ : G →* ℂ) (g : G) :
    χ g * star (χ g) = 1 := by
  obtain ⟨n, ρ, _, he⟩ := χ.isLinearCharacter.1
  have hi : χ g⁻¹ = star (χ g) := by
    rw [he]
    exact Representation.representation_character_inv_eq_star_character ρ g
  rw [← hi, ← map_mul, mul_inv_cancel, map_one]
end MonoidHom
namespace IsIrreducibleConjCharacter
variable {G : Type*} [Group G] [Finite G]
/-- A linear twist of a genuine irreducible character is genuinely irreducible. -/
theorem linearTwist {φ : ConjClassFunction G} (hφ : IsIrreducibleConjCharacter φ)
    (χ : G →* ℂ) : IsIrreducibleConjCharacter (χ.characterClass * φ) := by
  classical
  constructor
  · obtain ⟨n, ρ, hr⟩ := hφ.1
    refine ⟨n, ρ.linearTwist χ, ?_⟩
    ext c
    obtain ⟨g, rfl⟩ := ConjClasses.exists_rep c
    rw [hr]
    change χ g * ρ.character g = (ρ.linearTwist χ).character g
    exact (Representation.linearTwist_character ρ χ g).symm
  · rw [← hφ.2]
    unfold classFunctionInner
    congr 1
    apply Finset.sum_congr rfl
    intro g _
    simp only [Pi.mul_apply, MonoidHom.characterClass_apply, star_mul]
    calc
      χ g * φ (ConjClasses.mk g) * (star (φ (ConjClasses.mk g)) * star (χ g)) =
          (χ g * star (χ g)) * (φ (ConjClasses.mk g) * star (φ (ConjClasses.mk g))) := by ring
      _ = _ := by rw [χ.apply_mul_star, one_mul]
end IsIrreducibleConjCharacter
