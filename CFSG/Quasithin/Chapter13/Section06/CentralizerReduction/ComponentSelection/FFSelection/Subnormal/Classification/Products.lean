module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Subnormal.Classification.Setup
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Subnormal.Classification.Products.Contracts
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Subnormal.Classification.Products.Coprime
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Subnormal.Classification.Products.Orbit
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Subnormal.Classification.Products.GroupGeometry
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Subnormal.Classification.Products.SectionDimensions

/-!
# The two B.5.6 product deductions

Coprime averaging lifts the dimensions of the actual sections to the original
moved space. Counting the normal cubics of J bounds the normalizer in D.
The group geometry and section identifications are proved in the imported
modules and discharged in `twoFactors_bounds` and `hyperplane_bounds`.

Subnormality and the actual restricted Sylow give normality and S₃-factor
placement. The section comparison retains every natural,
double-natural and exceptional possibility, and both hyperplane subcases.
The marked applications construct the cubic hypotheses from the actual Chapter
13 objects. No splitting of V is introduced. The conditional assembly APIs
remain available independently of the completed product deductions.

Source: Aschbacher–Smith, B.5.6(3),(5), printed p.105; 13.6.10, printed p.928.
-/

@[expose] public section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Subnormal.Classification
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors

namespace Products
variable {E W : Type*} [Group E] [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) E W)

private theorem factor_moved_le {F : Subgroup E} {U : Subrepresentation σ}
    (hc : SourceFactorCase σ F U) : moved σ F ≤ U.toSubmodule := by
  cases hc with
  | natural he _ => exact he.ge
  | doubleNatural _ _ he _ => exact he.ge
  | exceptional he _ => exact he

end Products

universe u w
variable {D : Type u} [Group D] [Finite D]
    {W : Type w} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (ρ : Representation (ZMod 2) D W)

/-- Conditional assembly for B.5.6(3). The group and section contracts are
discharged by their producers in `twoFactors_bounds` below. -/
theorem twoFactors_bounds_of_geometry_and_sections
    {A : Subgroup D} {S : Sylow 2 D} {C : Subgroup D}
    (h : CubicHypothesis ρ A S C)
    (hc : SourceTwoFactorCase (offenderRepresentation ρ))
    (hposition : Products.CubicFactorPosition hc.first hc.second)
    (hcatalogue : Products.NormalCubicCatalogue (offenderSubgroup ρ))
    (hsections : Products.CubicFactorSections (offenderRepresentation ρ)) :
    CubicBounds ρ A := by
  obtain ⟨R, _, hR, _⟩ := h.internal_sylow
  obtain ⟨hn, hp⟩ := hposition (A.subgroupOf (offenderSubgroup ρ)) R
    (h.subnormal.subgroupOf) h.internal_card hR
  refine ⟨?_, Products.offender_index_le_two ρ h hn hcatalogue⟩
  rcases hp with ⟨hle, he⟩ | ⟨hle, he⟩
  · exact Products.moved_eq_two_of_factor_section ρ A h hc.first hc.firstSpace hle
      (Products.factor_moved_le _ hc.firstCase)
      (hsections _ _ hc.firstCase he)
  · exact Products.moved_eq_two_of_factor_section ρ A h hc.second hc.secondSpace hle
      (Products.factor_moved_le _ hc.secondCase)
      (hsections _ _ hc.secondCase he)

/-- Conditional assembly for B.5.6(5). The group producer excludes its first
SL₃(2) factor, leaving the actual second-factor section in `hyperplane_bounds`. -/
theorem hyperplane_bounds_of_geometry_and_sections
    {A : Subgroup D} {S : Sylow 2 D} {C : Subgroup D}
    (h : CubicHypothesis ρ A S C)
    (hc : HyperplaneCase (offenderRepresentation ρ))
    (hposition : ∀ (B : Subgroup (offenderSubgroup ρ))
      (R : Sylow 2 (offenderSubgroup ρ)), B.IsSubnormal → Nat.card B = 3 →
      (R : Subgroup (offenderSubgroup ρ)) ≤ normalizer (B : Set (offenderSubgroup ρ)) →
      B.Normal ∧ B ≤ hc.second ∧ Nonempty (hc.second ≃* Equiv.Perm (Fin 3)))
    (hcatalogue : Products.NormalCubicCatalogue (offenderSubgroup ρ))
    (hsections : Products.CubicHyperplaneSections (offenderRepresentation ρ)) :
    CubicBounds ρ A := by
  obtain ⟨R, _, hR, _⟩ := h.internal_sylow
  obtain ⟨hn, hle, he⟩ := hposition (A.subgroupOf (offenderSubgroup ρ)) R
    (h.subnormal.subgroupOf) h.internal_card hR
  exact ⟨Products.moved_eq_two_of_internal_section ρ A h hc.second hc.secondSpace hle
      hc.secondSpace_eq.ge (hsections _ _ hc.secondCase he),
    Products.offender_index_le_two ρ h hn hcatalogue⟩

/-- B.5.6(3) gives both cubic bounds on the original action and ambient
group. Sylow normalization supplies the actual factor placement, and
coprime averaging lifts the plane bound from V/C_V(J). -/
theorem twoFactors_bounds
    {A : Subgroup D} {S : Sylow 2 D} {C : Subgroup D}
    (h : CubicHypothesis ρ A S C)
    (hc : SourceTwoFactorCase (offenderRepresentation ρ)) : CubicBounds ρ A :=
  twoFactors_bounds_of_geometry_and_sections ρ h hc
    (Products.twoFactors_cubic_position _ hc)
    (Products.twoFactors_normal_catalogue _ hc)
    (Products.cubicFactorSections (offenderRepresentation ρ))

/-- B.5.6(5) gives both cubic bounds, retaining both second-factor cases
and the quotient by that factor's own fixed space. The SL₃(2) first factor
is excluded by its trivial three-core, without assuming cubic normality. -/
theorem hyperplane_bounds
    {A : Subgroup D} {S : Sylow 2 D} {C : Subgroup D}
    (h : CubicHypothesis ρ A S C)
    (hc : HyperplaneCase (offenderRepresentation ρ)) : CubicBounds ρ A :=
  hyperplane_bounds_of_geometry_and_sections ρ h hc
    (Products.hyperplane_cubic_position _ hc)
    (Products.hyperplane_normal_catalogue _ hc)
    (Products.cubicHyperplaneSections (offenderRepresentation ρ))

section Application
variable {G : Type u} [Group G] [Finite G] {L V : Subgroup G}
    (s : A5Module.Marking L V)
    [IsElementaryAbelian 2 (internalUv (A5Module.markedZ s) (A5Module.markedV s))]
local notation "z₀" => A5Module.markedZ s
local notation "v₀" => A5Module.markedV s
local notation "ρ₀" => uvRepresentation z₀ v₀ (A5Module.markedZ_mem_Gv s)
local notation "A₀" => starImage z₀ v₀ (Lv L v₀)
local notation "J₀" => offenderSubgroup ρ₀

/-- Literal Chapter 13 use of the conditional two-factor deduction.
Its additional geometry and section inputs remain proof obligations. -/
theorem marked_twoFactors_bounds_of_geometry_and_sections (T : Subgroup G)
    (S : Sylow 2 (Gv v₀))
    (hS : (S : Subgroup (Gv v₀)).map (Gv v₀).subtype = Tv T v₀)
    (hT : Tv T v₀ ≤ normalizer (Lv L v₀ : Set G))
    (hcore : pCore 2 (Gstar z₀ v₀) = ⊥)
    (hcard : Nat.card (Lv L v₀ ⧸ pCore 2 (Lv L v₀)) = 3)
    (hfull : A₀ = ⁅A₀, starImage z₀ v₀ (Stellmacher.elementaryAbelianMaxJ (Tv T v₀))⁆)
    (hs : (A₀).IsSubnormal)
    (hc : SourceTwoFactorCase (offenderRepresentation ρ₀))
    (hposition : Products.CubicFactorPosition hc.first hc.second)
    (hcatalogue : Products.NormalCubicCatalogue J₀)
    (hsections : Products.CubicFactorSections (offenderRepresentation ρ₀)) :
    CubicBounds ρ₀ A₀ :=
  twoFactors_bounds_of_geometry_and_sections ρ₀
    (marked_cubic_hypothesis s T S hS hT hcore hcard hfull hs)
    hc hposition hcatalogue hsections

/-- Literal Chapter 13 use of the conditional hyperplane deduction.
The actual second factor, quotient and restricted Sylow are retained. -/
theorem marked_hyperplane_bounds_of_geometry_and_sections (T : Subgroup G)
    (S : Sylow 2 (Gv v₀))
    (hS : (S : Subgroup (Gv v₀)).map (Gv v₀).subtype = Tv T v₀)
    (hT : Tv T v₀ ≤ normalizer (Lv L v₀ : Set G))
    (hcore : pCore 2 (Gstar z₀ v₀) = ⊥)
    (hcard : Nat.card (Lv L v₀ ⧸ pCore 2 (Lv L v₀)) = 3)
    (hfull : A₀ = ⁅A₀, starImage z₀ v₀ (Stellmacher.elementaryAbelianMaxJ (Tv T v₀))⁆)
    (hs : (A₀).IsSubnormal)
    (hc : HyperplaneCase (offenderRepresentation ρ₀))
    (hposition : ∀ (B : Subgroup J₀) (R : Sylow 2 J₀),
      B.IsSubnormal → Nat.card B = 3 →
      (R : Subgroup J₀) ≤ normalizer (B : Set J₀) →
      B.Normal ∧ B ≤ hc.second ∧ Nonempty (hc.second ≃* Equiv.Perm (Fin 3)))
    (hcatalogue : Products.NormalCubicCatalogue J₀)
    (hsections : Products.CubicHyperplaneSections (offenderRepresentation ρ₀)) :
    CubicBounds ρ₀ A₀ :=
  hyperplane_bounds_of_geometry_and_sections ρ₀
    (marked_cubic_hypothesis s T S hS hT hcore hcard hfull hs)
    hc hposition hcatalogue hsections

/-- The literal Chapter 13 two-factor application, with all product geometry
and section comparisons discharged. This supplies the twoFactors branch
of `bounds_of_remaining_cases` for the same marked action and subgroup. -/
theorem marked_twoFactors_bounds (T : Subgroup G)
    (S : Sylow 2 (Gv v₀))
    (hS : (S : Subgroup (Gv v₀)).map (Gv v₀).subtype = Tv T v₀)
    (hT : Tv T v₀ ≤ normalizer (Lv L v₀ : Set G))
    (hcore : pCore 2 (Gstar z₀ v₀) = ⊥)
    (hcard : Nat.card (Lv L v₀ ⧸ pCore 2 (Lv L v₀)) = 3)
    (hfull : A₀ = ⁅A₀, starImage z₀ v₀ (Stellmacher.elementaryAbelianMaxJ (Tv T v₀))⁆)
    (hs : (A₀).IsSubnormal)
    (hc : SourceTwoFactorCase (offenderRepresentation ρ₀)) : CubicBounds ρ₀ A₀ :=
  twoFactors_bounds ρ₀
    (marked_cubic_hypothesis s T S hS hT hcore hcard hfull hs) hc

/-- The literal Chapter 13 hyperplane application, with no remaining product
premise beyond the source alternative. This supplies the hyperplane branch
of `bounds_of_remaining_cases` for the same marked action and subgroup. -/
theorem marked_hyperplane_bounds (T : Subgroup G)
    (S : Sylow 2 (Gv v₀))
    (hS : (S : Subgroup (Gv v₀)).map (Gv v₀).subtype = Tv T v₀)
    (hT : Tv T v₀ ≤ normalizer (Lv L v₀ : Set G))
    (hcore : pCore 2 (Gstar z₀ v₀) = ⊥)
    (hcard : Nat.card (Lv L v₀ ⧸ pCore 2 (Lv L v₀)) = 3)
    (hfull : A₀ = ⁅A₀, starImage z₀ v₀ (Stellmacher.elementaryAbelianMaxJ (Tv T v₀))⁆)
    (hs : (A₀).IsSubnormal)
    (hc : HyperplaneCase (offenderRepresentation ρ₀)) : CubicBounds ρ₀ A₀ :=
  hyperplane_bounds ρ₀
    (marked_cubic_hypothesis s T S hS hT hcore hcard hfull hs) hc

end Application
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Subnormal.Classification
