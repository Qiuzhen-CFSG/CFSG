/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.HexacodeOrder
public import Theory.AtlasPort.OtherSporadic.Codes.HexacodeFaithful
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# HexacodeConjugation

Coordinate parity determines whether a hexacode automorphism centralizes or inverts the
order-three coordinate kernel. Conjugation of the explicit generators proves this rule
and gives the even subgroup map onto the alternating group.

Source: `Atlas/Codes/HexacodeConjugation.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

namespace Atlas.Codes

def hexSign : HexAutomorphisms →* ℤˣ := Equiv.Perm.sign.comp hexCoordinateSixHom

@[simp] theorem hexSign_Z : hexSign hexZ = 1 := by simp [hexSign]
@[simp] theorem hexSign_lift (k : Fin 5) : hexSign (hexLift k) = -1 := by
  simp only [hexSign, MonoidHom.comp_apply, hexLift_six]
  apply Equiv.Perm.sign_swap
  exact Fin.ne_of_val_ne (by simp)

theorem hex_conjugation_zpow (g : HexAutomorphisms) :
    MulAut.conj g hexZ = hexZ ^ (hexSign g : ℤ) := by
  have hg : g ∈ Subgroup.closure hexGeneratingSet := by rw [hexAutomorphisms_generated]; trivial
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | ⟨k,rfl⟩
    · simp [MulAut.conj_apply]
    · simpa only [MulAut.conj_apply, hexSign_lift, Units.val_neg, Units.val_one,
        zpow_neg_one] using hexLift_inverts k
  | one => simp
  | mul x y hx hy ihx ihy =>
    rw [map_mul]
    change MulAut.conj x (MulAut.conj y hexZ) = _
    rw [ihy, map_zpow, ihx, ← zpow_mul, map_mul, Units.val_mul]
  | inv x hx ih =>
    apply (MulAut.conj x).injective
    have hh : MulAut.conj x (MulAut.conj x⁻¹ hexZ) = hexZ := by
      change (MulAut.conj x * MulAut.conj x⁻¹) hexZ = hexZ
      rw [← map_mul, mul_inv_cancel, map_one]; rfl
    rw [hh, map_zpow, ih, ← zpow_mul, map_inv]
    rcases Int.units_eq_one_or (hexSign x) with h | h <;> simp [h]

theorem hex_conjugation_even (g : HexAutomorphisms) (hg : hexSign g = 1) :
    g * hexZ * g⁻¹ = hexZ := by
  simpa only [MulAut.conj_apply, hg, Units.val_one, zpow_one] using hex_conjugation_zpow g

theorem hex_conjugation_odd (g : HexAutomorphisms) (hg : hexSign g = -1) :
    g * hexZ * g⁻¹ = hexZ⁻¹ := by
  simpa only [MulAut.conj_apply, hg, Units.val_neg, Units.val_one, zpow_neg_one]
    using hex_conjugation_zpow g

abbrev HexEvenAutomorphisms := hexSign.ker

def hexEvenCoordinate : HexEvenAutomorphisms →* alternatingGroup (Fin 6) where
  toFun g := ⟨hexCoordinateSixHom g.val, g.prop⟩
  map_one' := by apply Subtype.ext; exact map_one _
  map_mul' _ _ := by apply Subtype.ext; exact map_mul _ _ _

theorem hexEvenCoordinate_surjective : Function.Surjective hexEvenCoordinate := by
  intro σ
  obtain ⟨g,hg⟩ := hexCoordinateSix_surjective σ.val
  refine ⟨⟨g,?_⟩,Subtype.ext hg⟩
  change Equiv.Perm.sign (hexCoordinateSixHom g) = 1
  rw [hg]
  exact σ.prop

theorem hex_even_kernel_central (g : HexEvenAutomorphisms) (k : hexCoordinateSixHom.ker) :
    Commute g.val k.val := by
  have hz : Commute g.val hexZ := by
    change _ = _
    exact (mul_inv_eq_iff_eq_mul).mp (hex_conjugation_even g.val g.prop)
  rcases hex_kernel_trichotomy k.val ((hexSix_eq_one _).mp k.prop) with h | h | h
  · rw [h]; exact Commute.one_right _
  · rw [h]; exact hz
  · rw [h]; exact hz.pow_right 2

end Atlas.Codes
