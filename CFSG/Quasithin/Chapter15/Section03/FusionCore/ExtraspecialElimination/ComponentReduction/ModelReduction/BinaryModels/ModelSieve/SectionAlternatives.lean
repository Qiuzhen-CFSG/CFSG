module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ModelSieve.Carriers
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ModelSieve.HexSection

/-!
# Component alternatives retaining the exceptional section

The triple-cover branch retains a literal irreducible section of the source
representation and an intertwining map to the hexacode. The other branches
retain the group information used by this sieve. Excluding larger fields
reduces the Lie alternatives to the exact binary carriers, without discarding
the exceptional section.

These are output predicates and a terminal field sieve. They do not assert
that the appendix classification applies or construct its output. In particular,
the group-only `BorelInner.ComponentModel` is insufficient to construct the
triple-cover branch here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.4.2(8),
B.5.1(1), B.5.5(1)(iv), and the model list in 15.3.49(l), printed p.1144.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ModelSieve

variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]

/-- The pre-sieve component list, retaining the actual exceptional module. -/
inductive ComponentSectionAlternative (ρ : Representation (ZMod 2) D V)
    (C : Subgroup D) : Prop
  | lie (e : ℕ) (model : BorelInner.LieComponentModel C e)
  | alternating_seven (model : Nonempty (C ≃* alternatingGroup (Fin 7)))
  | triple_cover (sectionModel : Nonempty (HexSection ρ C))

/-- The binary endpoints, with the same exceptional source section. -/
inductive BinarySectionAlternative (ρ : Representation (ZMod 2) D V)
    (C : Subgroup D) : Prop
  | linear (n : ℕ) (lower : 3 ≤ n) (upper : n ≤ 5)
      (model : Nonempty (C ≃* Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2)))
  | alternating_six (model : Nonempty (C ≃* alternatingGroup (Fin 6)))
  | triple_cover (sectionModel : Nonempty (HexSection ρ C))
  | alternating_seven (model : Nonempty (C ≃* alternatingGroup (Fin 7)))
  | g2_derived (model : Nonempty (C ≃* commutator (Atlas.G2.Model (ZMod 2))))

/-- Forget only the representation information, retaining the actual carriers. -/
theorem ComponentSectionAlternative.componentModel
    {ρ : Representation (ZMod 2) D V} {C : Subgroup D}
    (h : ComponentSectionAlternative ρ C) : BorelInner.ComponentModel C := by
  cases h with
  | lie e model => exact .lie e model
  | alternating_seven model => exact .alternating_seven model
  | triple_cover sectionModel =>
    exact .triple_alternating_six (sectionModel.map HexSection.groupEquiv)

/-- Read the binary group carrier from the section-preserving conclusion. -/
theorem BinarySectionAlternative.componentModel
    {ρ : Representation (ZMod 2) D V} {C : Subgroup D}
    (h : BinarySectionAlternative ρ C) : BinaryComponentModel C := by
  cases h with
  | linear n lo hi model => exact .linear n lo hi model
  | alternating_six model => exact .alternating_six model
  | triple_cover sectionModel => exact .triple_cover (sectionModel.map HexSection.groupEquiv)
  | alternating_seven model => exact .alternating_seven model
  | g2_derived model => exact .g2_derived model

/-- Exclude the larger fields and transport each surviving Lie carrier.
The triple-cover branch returns its original intertwining witness unchanged. -/
theorem ComponentSectionAlternative.sieve
    {ρ : Representation (ZMod 2) D V} {C : Subgroup D}
    (h : ComponentSectionAlternative ρ C) (hfield : NoLargerField C) :
    BinarySectionAlternative ρ C := by
  cases h with
  | alternating_seven model => exact .alternating_seven model
  | triple_cover sectionModel => exact .triple_cover sectionModel
  | lie e model =>
    have he : ¬ 1 < e := fun he => hfield e he model
    cases model with
    | linear_two lower F hF iso => omega
    | linear_three lower F hF iso =>
      have heq : e = 1 := by omega
      have hc : Nat.card F = 2 := by simpa only [heq, pow_one] using hF
      exact .linear 3 (by decide) (by decide)
        (iso.map (fun f => f.trans (linearThreeEquivBinary hc)))
    | symplectic lower F hF iso =>
      have heq : e = 1 := by omega
      have hc : Nat.card F = 2 := by simpa only [heq, pow_one] using hF
      exact .alternating_six (iso.map (fun f => f.trans (symplecticDerivedEquivSix hc)))
    | g2 lower F hF iso =>
      have heq : e = 1 := by omega
      have hc : Nat.card F = 2 := by simpa only [heq, pow_one] using hF
      exact .g2_derived (iso.map (fun f => f.trans (g2DerivedEquivBinary hc)))
    | binary_linear heq n hn iso => exact .linear n (by omega) (by omega) iso

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ModelSieve
