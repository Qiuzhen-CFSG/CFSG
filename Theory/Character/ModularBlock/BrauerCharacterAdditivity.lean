module

public import Theory.Character.ModularBlock.BrauerCharacterBasis
public import Theory.LinearAlgebra.CharpolySubquotient

/-!
# Additivity of genuine Brauer values

Characteristic polynomials multiply across an invariant subspace and its
quotient. Their root multisets therefore add, with multiplicity, and summing
the prescribed cyclotomic lifts gives additivity of the Brauer value.
This argument retains the integral multiplicities, even in characteristic two.

This is the exact-sequence step of modular character decomposition for the
root-lift definition in `BrauerCharacterBasis.lean`. No splitting of the
representation or lifting of residue-field traces is used.
-/

public section

noncomputable section
namespace ModularBlock.BrauerCharacter
open PrincipalBlockConstruction BrauerCoefficientExtension
variable {G : Type*} [Group G] [Finite G]
variable (d : PrincipalCongruenceBlockData G)
variable {V : Type*} [AddCommGroup V] [Module (splittingField d) V]
  [FiniteDimensional (splittingField d) V]
variable (ρ : Representation (splittingField d) G V)

/-- Root multiplicities give additivity before mapping the lifts to the complex numbers. -/
theorem integralValue_subquotient (S : Subrepresentation ρ) (g : G) :
    integralValue d ρ g = integralValue d S.toRepresentation g +
      integralValue d (ρ.quotient S.toSubmodule S.apply_mem_toSubmodule) g := by
  unfold integralValue
  change ((ρ g).charpoly.roots.map (eigenvalueLift d)).sum =
    (((ρ g).restrict (S.apply_mem_toSubmodule g)).charpoly.roots.map
      (eigenvalueLift d)).sum +
    ((S.toSubmodule.mapQ S.toSubmodule (ρ g)
      (S.apply_mem_toSubmodule g)).charpoly.roots.map (eigenvalueLift d)).sum
  rw [LinearMap.charpoly_eq_charpoly_mul_charpoly S.toSubmodule (ρ g)
    (S.apply_mem_toSubmodule g),
    Polynomial.roots_mul (mul_ne_zero (LinearMap.charpoly_monic _).ne_zero
      (LinearMap.charpoly_monic _).ne_zero), Multiset.map_add, Multiset.sum_add]

/-- Genuine Brauer values add across a submodule and its quotient. -/
theorem value_subquotient (S : Subrepresentation ρ) (g : G) :
    value d ρ g = value d S.toRepresentation g +
      value d (ρ.quotient S.toSubmodule S.apply_mem_toSubmodule) g := by
  exact congrArg Subtype.val (integralValue_subquotient d ρ S g)

/-- The zero-dimensional module has zero Brauer value. -/
theorem value_eq_zero_of_subsingleton [Subsingleton V] (g : G) :
    value d ρ g = 0 := by
  have h : ρ g = 0 := Subsingleton.elim _ _
  simp [value, integralValue, h, Module.finrank_eq_zero_of_subsingleton]

end ModularBlock.BrauerCharacter
