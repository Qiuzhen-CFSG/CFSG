module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.OrdinarySource.CubicOrder
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.Notation
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalResidualCard

/-!
# The full permutation image of the ordinary source residual

Residual transport takes the actual O²(N_LT(V₁)) onto the embedded A₄
in the six-letter action. Its image has order twelve, although its quotient
by its own two-core has order three. Keeping these quotients distinct is
necessary when computing the centralizer of all of L/O₂(L).

Source: Aschbacher–Smith, Notation 13.2.1, p.877; used to check the literal
local centralizer/index assertions in 13.8.20, p.954/PDF p.971.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.Ordinary.NaturalImage
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open NaturalResidualCard BinaryPermutation Representation.BinaryOffender

open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.OrdinarySource
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G] [Finite G] {L T W W₁ : Subgroup G}

/-- The actual permutation homomorphism restricted to the source L₁. -/
def onePermutation (d : NaturalSetup L T W W₁) : one L T W₁ →* S :=
  d.permutation.comp (inclusion ((one_le L T W₁).trans inf_le_left))

/-- The literal source residual has full permutation image of order twelve. -/
theorem onePermutation_range_card (d : NaturalSetup L T W W₁) :
    Nat.card (onePermutation d).range = 12 := by
  let M := parabolic L T W₁
  let f : M →* S := d.permutation.comp (inclusion inf_le_left)
  have he : (onePermutation d).range = (pResidual 2 M).map f := by
    ext g
    constructor
    · rintro ⟨⟨x, y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y.val, y, hy, rfl⟩, rfl⟩
  have hm : (pResidual 2 M).map f = (pResidual 2 f.range).map f.range.subtype := by
    calc
      _ = ((pResidual 2 M).map f.rangeRestrict).map f.range.subtype := by
        rw [map_map]; rfl
      _ = _ := by rw [map_pResidual_of_surjective 2 f.rangeRestrict f.rangeRestrict_surjective]
  rw [he, hm]
  have hr : f.range = d.permutation.range ⊓
      subspaceStabilizer (naturalRepresentation (Fin 6)) d.point := d.line_normalizer_image
  rw [hr]
  exact point_residual_card d.permutation.range d.alternating_le_range d.point d.point_dim

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.Ordinary.NaturalImage
