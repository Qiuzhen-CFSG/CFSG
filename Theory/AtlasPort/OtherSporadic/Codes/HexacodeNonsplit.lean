/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.HexacodeConjugation

/-!
# HexacodeNonsplit

The coordinate extensions of the hexacode automorphism groups do not split. Explicit
lifts of commuting disjoint coordinate three-cycles have a nontrivial scalar commutator,
and changing the lifts cannot remove that obstruction.

Source: `Atlas/Codes/HexacodeNonsplit.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

namespace Atlas.Codes
open scoped commutatorElement

def hexX : HexAutomorphisms := hexLift 0 * hexLift 1
def hexY : HexAutomorphisms := hexLift 3 * hexLift 4

theorem hexX_coordinate : hexCoordinateSixHom hexX = Equiv.swap 0 1 * Equiv.swap 1 2 := by
  simp [hexX]
theorem hexY_coordinate : hexCoordinateSixHom hexY = Equiv.swap 3 4 * Equiv.swap 4 5 := by
  simp [hexY]

@[simp] theorem hexX_even : hexSign hexX = 1 := by simp [hexX]
@[simp] theorem hexY_even : hexSign hexY = 1 := by simp [hexY]

theorem hexXY_coordinate_commute : Commute (hexCoordinateSixHom hexX) (hexCoordinateSixHom hexY) := by
  rw [hexX_coordinate, hexY_coordinate]
  change _ = _
  apply Equiv.ext
  intro i
  revert i
  decide

theorem hexXY_commutator : ⁅hexX,hexY⁆ = hexZ ^ 2 := by
  apply Subtype.ext
  apply Monomial.ext
  · apply Equiv.ext
    intro i
    revert i
    decide
  · funext i
    apply LinearEquiv.ext
    intro u
    revert i u
    decide

theorem hexZ_square_ne_one : hexZ ^ 2 ≠ 1 := by
  intro h
  have hh := congrArg (fun g : HexAutomorphisms => g.val.localMap (hexPos 0) a) h
  exact (by decide : c ≠ a) hh

theorem hexXY_not_commute : ¬ Commute hexX hexY := by
  intro h
  exact hexZ_square_ne_one (hexXY_commutator.symm.trans (commutatorElement_eq_one_iff_commute.mpr h))

/-- Central kernel elements cannot turn these two lifts into commuting lifts. -/
theorem hexXY_lifts_not_commute (x y : HexAutomorphisms)
    (hx : hexCoordinateSixHom x = hexCoordinateSixHom hexX)
    (hy : hexCoordinateSixHom y = hexCoordinateSixHom hexY) : ¬ Commute x y := by
  intro hxy
  have hxe : hexSign x = 1 := by change Equiv.Perm.sign (hexCoordinateSixHom x) = 1; rw [hx]; exact hexX_even
  have hye : hexSign y = 1 := by change Equiv.Perm.sign (hexCoordinateSixHom y) = 1; rw [hy]; exact hexY_even
  let k := x * hexX⁻¹
  let l := y * hexY⁻¹
  have hk : k ∈ hexCoordinateSixHom.ker := by
    change hexCoordinateSixHom (x * hexX⁻¹) = 1
    rw [map_mul,map_inv,hx,mul_inv_cancel]
  have hl : l ∈ hexCoordinateSixHom.ker := by
    change hexCoordinateSixHom (y * hexY⁻¹) = 1
    rw [map_mul,map_inv,hy,mul_inv_cancel]
  have hky : Commute k y := (hex_even_kernel_central ⟨y,hye⟩ ⟨k,hk⟩).symm
  have hXy : Commute hexX y := by
    have hh := hky.inv_left.mul_left hxy
    simpa [k, mul_assoc] using hh
  have hXl : Commute hexX l := hex_even_kernel_central ⟨hexX,hexX_even⟩ ⟨l,hl⟩
  have hh := hXl.inv_right.mul_right hXy
  apply hexXY_not_commute
  simpa [l, mul_assoc] using hh

theorem hexEven_no_section : ¬ ∃ s : alternatingGroup (Fin 6) →* HexEvenAutomorphisms,
    hexEvenCoordinate.comp s = MonoidHom.id _ := by
  rintro ⟨s,hs⟩
  let x : alternatingGroup (Fin 6) := ⟨hexCoordinateSixHom hexX,hexX_even⟩
  let y : alternatingGroup (Fin 6) := ⟨hexCoordinateSixHom hexY,hexY_even⟩
  have hxy : Commute x y := by
    change _ = _
    apply Subtype.ext
    exact hexXY_coordinate_commute.eq
  have hx : hexCoordinateSixHom (s x).val = hexCoordinateSixHom hexX :=
    congrArg Subtype.val (DFunLike.congr_fun hs x)
  have hy : hexCoordinateSixHom (s y).val = hexCoordinateSixHom hexY :=
    congrArg Subtype.val (DFunLike.congr_fun hs y)
  exact hexXY_lifts_not_commute _ _ hx hy ((hxy.map s).map hexSign.ker.subtype)

theorem hex_no_section : ¬ ∃ s : Equiv.Perm (Fin 6) →* HexAutomorphisms,
    hexCoordinateSixHom.comp s = MonoidHom.id _ := by
  rintro ⟨s,hs⟩
  have hx := DFunLike.congr_fun hs (hexCoordinateSixHom hexX)
  have hy := DFunLike.congr_fun hs (hexCoordinateSixHom hexY)
  exact hexXY_lifts_not_commute _ _ hx hy (hexXY_coordinate_commute.map s)

theorem hexSign_surjective : Function.Surjective hexSign := by
  intro u
  rcases Int.units_eq_one_or u with rfl | rfl
  · exact ⟨1,map_one _⟩
  · exact ⟨hexLift 0,hexSign_lift 0⟩

theorem hexEven_card : Nat.card HexEvenAutomorphisms = 1080 := by
  have h := hexSign.ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hexSign_surjective,
    Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup ℤˣ) ≃* ℤˣ).toEquiv,
    hexAutomorphisms_card] at h
  have hc : Nat.card ℤˣ = 2 := by simp [Nat.card_eq_fintype_card]
  rw [hc] at h
  change Nat.card HexEvenAutomorphisms * 2 = 2160 at h
  omega

end Atlas.Codes
