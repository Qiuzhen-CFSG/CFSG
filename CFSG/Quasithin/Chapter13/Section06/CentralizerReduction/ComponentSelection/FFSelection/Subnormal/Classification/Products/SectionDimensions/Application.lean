module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Subnormal.Classification.Products
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Subnormal.Classification.Products.SectionDimensions

/-!
# Applying the S₃ section comparisons to the cubic bounds

The two section premises of the product deductions are discharged here on the
actual offender representation. Coprime lifting and the ambient orbit count
remain those of `Products.lean`. Only the independently owned factor-placement
and normal-cubic-catalogue premises remain for the final assembly.

Source: Aschbacher–Smith B.5.6(3),(5), printed p.105; 13.6.10, printed p.928.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Subnormal.Classification
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors

universe u w
variable {D : Type u} [Group D] [Finite D]
    {W : Type w} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (ρ : Representation (ZMod 2) D W)

/-- B.5.6(3)'s section comparison is proved; its group geometry and catalogue
remain with the product-bounds assembly owner. -/
theorem twoFactors_bounds_of_geometry
    {A : Subgroup D} {S : Sylow 2 D} {C : Subgroup D}
    (h : CubicHypothesis ρ A S C)
    (hc : SourceTwoFactorCase (offenderRepresentation ρ))
    (hposition : Products.CubicFactorPosition hc.first hc.second)
    (hcatalogue : Products.NormalCubicCatalogue (offenderSubgroup ρ)) :
    CubicBounds ρ A :=
  twoFactors_bounds_of_geometry_and_sections ρ h hc hposition hcatalogue
    (Products.cubicFactorSections (offenderRepresentation ρ))

/-- B.5.6(5)'s internal fixed-quotient comparison is proved, retaining the
actual second factor and restricted Sylow in the remaining group premise. -/
theorem hyperplane_bounds_of_geometry
    {A : Subgroup D} {S : Sylow 2 D} {C : Subgroup D}
    (h : CubicHypothesis ρ A S C)
    (hc : HyperplaneCase (offenderRepresentation ρ))
    (hposition : ∀ (B : Subgroup (offenderSubgroup ρ))
      (R : Sylow 2 (offenderSubgroup ρ)), B.IsSubnormal → Nat.card B = 3 →
      (R : Subgroup (offenderSubgroup ρ)) ≤ normalizer (B : Set (offenderSubgroup ρ)) →
      B.Normal ∧ B ≤ hc.second ∧ Nonempty (hc.second ≃* Equiv.Perm (Fin 3)))
    (hcatalogue : Products.NormalCubicCatalogue (offenderSubgroup ρ)) :
    CubicBounds ρ A :=
  hyperplane_bounds_of_geometry_and_sections ρ h hc hposition hcatalogue
    (Products.cubicHyperplaneSections (offenderRepresentation ρ))

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Subnormal.Classification
