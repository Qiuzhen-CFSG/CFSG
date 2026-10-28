module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.Quotient.B4Extraction.ComponentInputs
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.Quotient.B4Extraction.SplitModels.Coordinates

/-!
# Opposite marked constituent models

These predicates specify the natural and contragredient identifications of
the two actual summands for one fixed GL₄(2) marking. They form the common
interface between the graph-twist calculation and direct-sum assembly in
the split branch of Aschbacher–Smith 13.8.25, printed pp.959–960.
They assert no classification or existence theorem.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OrthogonalQuotient.B4Extraction.SplitModels
open Representation FourStructure.ChiefFactors
variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
  {ρ : Representation (ZMod 2) H U} {K : Subgroup H}

/-- The contragredient constituent, using the specified GL₄(2) marking. -/
def IsDual {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (σ : Representation (ZMod 2) K E) (eK : K ≃* BinaryLinear.GL FourSpace) : Prop :=
  ∃ e : E ≃ₗ[ZMod 2] Module.Dual (ZMod 2) FourSpace,
    ∀ k v, e (σ k v) = (naturalAction eK).dual k (e v)

/-- Opposite constituents, with no choice of a second actor marking. -/
def OppositeModels (d : RestrictionSplit ρ K)
    (eK : K ≃* BinaryLinear.GL FourSpace) : Prop :=
  (IsNatural d.left.toRepresentation eK ∧ IsDual d.right.toRepresentation eK) ∨
    (IsDual d.left.toRepresentation eK ∧ IsNatural d.right.toRepresentation eK)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OrthogonalQuotient.B4Extraction.SplitModels
