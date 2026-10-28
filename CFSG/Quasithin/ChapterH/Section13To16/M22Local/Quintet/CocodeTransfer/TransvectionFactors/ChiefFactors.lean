module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Quintet.CocodeTransfer.TransvectionFactors.ChiefFactors

/-!
# The chief factors of the outer M22 cocode flag

The displacement pairing restricted to the actual inner kernel identifies
V6/V2 equivariantly with its dual. Its earlier H.14 irreducibility, the two
one-dimensional factors, and the earlier top-section irreducibility give
all four covers in the lattice of Q-invariant subspaces.

This is the conditional chiefness step of Aschbacher--Smith H.15.4(1),
printed p.400, using H.14.3(2), printed p.397 (1 March 2004 manuscript).
The earlier conjugation and top-section premises remain explicit.
-/

@[expose] public section
noncomputable section
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterH.Section13To16
open MathieuCode MathieuCode.M22Quintet
open MathieuCode.M22Quintet.CocodeTransfer

variable [IsElementaryAbelian 2 K]

/-- The literal four-dimensional factor, marked by the actual displacement pairing. -/
def m22Quintet_inner_factor_duality (D : SextetTransvectionInputs) :
    (V6 ⧸ (V2.comap V6.subtype)) ≃ₗ[ZMod 2] Module.Dual (ZMod 2) (Additive A0) :=
  innerFactorDuality D

theorem m22Quintet_inner_factor_duality_equivariant
    (D : SextetTransvectionInputs) (I : InnerInputs)
    (g : Q) (v : V6 ⧸ (V2.comap V6.subtype)) :
    m22Quintet_inner_factor_duality D
        ((innerFixedSubrepresentation I).quotientRepresentation g v) =
      (innerConjugation I).dual g (m22Quintet_inner_factor_duality D v) :=
  innerFactorDuality_equivariant D I g v

theorem m22Quintet_inner_factor_dimension (D : SextetTransvectionInputs) (I : InnerInputs) :
    Module.finrank (ZMod 2) (V6 ⧸ (V2.comap V6.subtype)) = 4 :=
  finrank_innerFactor D I

theorem m22Quintet_inner_factor_irreducible (D : SextetTransvectionInputs) (I : InnerInputs)
    [Representation.IsIrreducible (innerConjugation I)] :
    Representation.IsIrreducible (innerFixedSubrepresentation I).quotientRepresentation :=
  innerFactor_irreducible D I

variable (D : SextetTransvectionInputs) (I : InnerInputs)
  [Representation.IsIrreducible V6Subrepresentation.quotientRepresentation]
  [Representation.IsIrreducible (innerConjugation I)]

/-- A value of the existing native flag interface, with every cover proved. -/
def m22Quintet_cocode_chief_flag : DualAction.CocodeFlag := cocodeChiefFlag D I

theorem m22Quintet_cocode_chief_covers :
    (⊥ : Subrepresentation DualAction.cocodeAction) ⋖ V1Subrepresentation D I ∧
    V1Subrepresentation D I ⋖ V2Subrepresentation I ∧
    V2Subrepresentation I ⋖ V6Subrepresentation ∧
    V6Subrepresentation ⋖ (⊤ : Subrepresentation DualAction.cocodeAction) :=
  cocode_chief_covers D I

/-- All four literal induced actions are irreducible under the earlier source inputs. -/
theorem m22Quintet_cocode_chief_factors_irreducible :
    Representation.IsIrreducible (V1Subrepresentation D I).toRepresentation ∧
    Representation.IsIrreducible (firstSection D I).quotientRepresentation ∧
    Representation.IsIrreducible (innerFixedSubrepresentation I).quotientRepresentation ∧
    Representation.IsIrreducible V6Subrepresentation.quotientRepresentation :=
  cocode_chief_factors_irreducible D I

end CFSG.Quasithin.ChapterH.Section13To16
