/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.HexacodeNonsplit

/-!
# HexacodeAutomorphismPackage

The even hexacode automorphism group maps onto the alternating coordinate group with
central cyclic kernel of order three. This module assembles the proved generators,
kernel, orders, conjugation, and nonsplitting results into one interface.

Source: `Atlas/Codes/HexacodeAutomorphismPackage.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

namespace Atlas.Codes

def hexEvenZ : HexEvenAutomorphisms := ⟨hexZ,hexSign_Z⟩

theorem hexEvenZ_order : orderOf hexEvenZ = 3 := by
  apply orderOf_eq_prime
  · apply Subtype.ext; exact hexZ_cube
  · intro h; exact hexZ_ne_one (congrArg Subtype.val h)

theorem hexEvenCoordinate_kernel : hexEvenCoordinate.ker = Subgroup.zpowers hexEvenZ := by
  apply le_antisymm
  · intro g hg
    have hp : hexCoordinateSixHom g.val = 1 := congrArg Subtype.val hg
    rcases hex_kernel_trichotomy g.val ((hexSix_eq_one _).mp hp) with h | h | h
    · have hh : g = 1 := Subtype.ext h
      rw [hh]; exact Subgroup.one_mem _
    · have hh : g = hexEvenZ := Subtype.ext h
      rw [hh]; exact Subgroup.mem_zpowers _
    · have hh : g = hexEvenZ ^ 2 := Subtype.ext h
      rw [hh]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  · apply Subgroup.zpowers_le.mpr
    apply Subtype.ext
    exact hexZ_six

theorem hexEven_kernel_card : Nat.card hexEvenCoordinate.ker = 3 := by
  rw [hexEvenCoordinate_kernel,Nat.card_zpowers,hexEvenZ_order]

/-- Conclusions about the actual full monomial stabilizer of the existing hexacode. -/
structure HexacodeAutomorphismPackage : Prop where
  faithful : Function.Injective hexAction
  coordinate_surjective : Function.Surjective hexCoordinateSixHom
  coordinate_kernel : hexCoordinateSixHom.ker = Subgroup.zpowers hexZ
  kernel_order : orderOf hexZ = 3
  kernel_cardinality : Nat.card hexCoordinateHom.ker = 3
  generation : Subgroup.closure hexGeneratingSet = ⊤
  order : Nat.card HexAutomorphisms = 2160
  even_conjugation : ∀ g, hexSign g = 1 → g * hexZ * g⁻¹ = hexZ
  odd_conjugation : ∀ g, hexSign g = -1 → g * hexZ * g⁻¹ = hexZ⁻¹
  even_order : Nat.card HexEvenAutomorphisms = 1080
  even_surjective : Function.Surjective hexEvenCoordinate
  even_kernel : hexEvenCoordinate.ker = Subgroup.zpowers hexEvenZ
  even_kernel_central : ∀ (g : HexEvenAutomorphisms) (k : hexCoordinateSixHom.ker),
    Commute g.val k.val
  even_nonsplit : ¬ ∃ s : alternatingGroup (Fin 6) →* HexEvenAutomorphisms,
    hexEvenCoordinate.comp s = MonoidHom.id _
  nonsplit : ¬ ∃ s : Equiv.Perm (Fin 6) →* HexAutomorphisms,
    hexCoordinateSixHom.comp s = MonoidHom.id _

theorem hexacode_automorphism_package : HexacodeAutomorphismPackage where
  faithful := hexAction_injective
  coordinate_surjective := hexCoordinateSix_surjective
  coordinate_kernel := hexCoordinateSix_kernel
  kernel_order := hexZ_order
  kernel_cardinality := hex_kernel_card
  generation := hexAutomorphisms_generated
  order := hexAutomorphisms_card
  even_conjugation := hex_conjugation_even
  odd_conjugation := hex_conjugation_odd
  even_order := hexEven_card
  even_surjective := hexEvenCoordinate_surjective
  even_kernel := hexEvenCoordinate_kernel
  even_kernel_central := hex_even_kernel_central
  even_nonsplit := hexEven_no_section
  nonsplit := hex_no_section

end Atlas.Codes
