module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.Inputs

/-!
# Right-coset conventions for the literal principal series

Mathlib acts by `g · [t ⊗ a] = [t * g⁻¹ ⊗ a]`. If a coset transition
is `t * g⁻¹ = b * s`, the new coefficient is `χ(b)⁻¹ * a`.
Both inversions matter when comparing right-action diagnostic matrices
with this left representation. These formulas are on the actual induction
quotient, so they can be used to verify a coordinate identification.

This is the convention check for the principal-series approach to
Guralnick–Malle, *Classification of 2F-modules I*, Proposition 4.3.
-/

public section

open BenderSuzuki.MatrixGroups
namespace Representation.SU3.FiveSmallModules.Degrees

section Conventions
open scoped MonoidAlgebra
variable {K G : Type*} [Field K] [Group G]

/-- The coinvariant relation uses the inverse character on a left Borel factor. -/
theorem induced_mk_subgroup_mul (B : Subgroup G) (χ : B →* Kˣ)
    (b : B) (g : G) (a : K) :
    IndV.mk B.subtype (scalarCharacter χ) ((b : G) * g) a =
      IndV.mk B.subtype (scalarCharacter χ) g ((χ b : K)⁻¹ * a) := by
  simpa [IndV.mk, ofMulAction_single] using
    (Coinvariants.mk_tmul_inv ((leftRegular K G).comp B.subtype) (scalarCharacter χ)
      (MonoidAlgebra.single g (1 : K)) a b).symm

/-- A right-coset transition for the literal Mathlib induced representation. -/
theorem induced_rightCoset_formula (B : Subgroup G) (χ : B →* Kˣ)
    (g t s : G) (b : B) (h : t * g⁻¹ = (b : G) * s) (a : K) :
    ind B.subtype (scalarCharacter χ) g (IndV.mk B.subtype (scalarCharacter χ) t a) =
      IndV.mk B.subtype (scalarCharacter χ) s ((χ b : K)⁻¹ * a) := by
  rw [ind_mk, h, induced_mk_subgroup_mul]
end Conventions


/-- The transition formula specialized to the Borel and induction module
used by `PrincipalSeriesFiltrations`. -/
theorem principal_series_rightCoset_formula
    {F K : Type*} [Field F] [Field K] (J : HermitianForm 3 F)
    (χ : standardBorel J →* Kˣ) (g t s : standardGroup J)
    (b : standardBorel J) (h : t * g⁻¹ = (b : standardGroup J) * s) (a : K) :
    ind (standardBorel J).subtype (scalarCharacter χ) g
        (IndV.mk (standardBorel J).subtype (scalarCharacter χ) t a) =
      IndV.mk (standardBorel J).subtype (scalarCharacter χ) s ((χ b : K)⁻¹ * a) :=
  induced_rightCoset_formula (standardBorel J) χ g t s b h a

end Representation.SU3.FiveSmallModules.Degrees
