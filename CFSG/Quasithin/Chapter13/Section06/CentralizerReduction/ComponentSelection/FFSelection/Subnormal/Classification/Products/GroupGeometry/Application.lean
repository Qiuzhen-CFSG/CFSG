module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Subnormal.Classification.Products
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Subnormal.Classification.Products.GroupGeometry

/-!
# Product deductions with all group geometry discharged

These applications supply normality, actual S₃-factor placement and the
normal cubic catalogue to the two B.5.6 deductions. Only the independent
section-dimension contracts remain. The final assembly owner must supply
those contracts before claiming the unconditional Chapter 13 bounds.

Source: Aschbacher–Smith, B.5.6(3),(5), printed p.105, and 13.6.10, p.928.
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

/-- The two-factor deduction now requires only the section comparison. -/
theorem twoFactors_bounds_of_sections
    {A : Subgroup D} {S : Sylow 2 D} {C : Subgroup D}
    (h : CubicHypothesis ρ A S C)
    (hc : SourceTwoFactorCase (offenderRepresentation ρ))
    (hsections : Products.CubicFactorSections (offenderRepresentation ρ)) :
    CubicBounds ρ A :=
  twoFactors_bounds_of_geometry_and_sections ρ h hc
    (Products.twoFactors_cubic_position _ hc)
    (Products.twoFactors_normal_catalogue _ hc) hsections

/-- The hyperplane deduction now requires only its internal section comparison. -/
theorem hyperplane_bounds_of_sections
    {A : Subgroup D} {S : Sylow 2 D} {C : Subgroup D}
    (h : CubicHypothesis ρ A S C)
    (hc : HyperplaneCase (offenderRepresentation ρ))
    (hsections : Products.CubicHyperplaneSections (offenderRepresentation ρ)) :
    CubicBounds ρ A :=
  hyperplane_bounds_of_geometry_and_sections ρ h hc
    (Products.hyperplane_cubic_position _ hc)
    (Products.hyperplane_normal_catalogue _ hc) hsections

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Subnormal.Classification
