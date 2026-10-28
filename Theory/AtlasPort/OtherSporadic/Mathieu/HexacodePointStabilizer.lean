/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.KleinianLocalGeneration
public import Theory.AtlasPort.OtherSporadic.Mathieu.Mathieu24Order

/-!
# HexacodePointStabilizer

The stabilizer of a hexacode coordinate maps onto the full isometry group of its
alphabet. The scalar supplies a three-cycle and an odd coordinate lift supplies an
inverter, so the local generation criterion proves surjectivity.

Source: `Atlas/Mathieu/HexacodePointStabilizer.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes

/-- The inverse image of the natural S5 coordinate stabilizer. -/
def hexPointStabilizer (i : HexIndex) : Subgroup HexAutomorphisms where
  carrier := {g | g.val.perm i = i}
  one_mem' := rfl
  mul_mem' := by
    intro g h hg hh
    change g.val.perm (h.val.perm i) = i
    rw [hh,hg]
  inv_mem' := by
    intro g hg
    exact (Equiv.symm_apply_eq _).mpr hg.symm

theorem hexPointStabilizer_fixed (i : HexIndex) (g : hexPointStabilizer i) : g.val.val.perm i = i := g.prop

theorem hexPointStabilizer_inv_fixed (i : HexIndex) (g : hexPointStabilizer i) :
    g.val.val.perm.symm i = i := (Equiv.symm_apply_eq _).mpr g.prop.symm

/-- Local linear action on the alphabet at a fixed coordinate. -/
def hexPointLocal (i : HexIndex) : hexPointStabilizer i →* KIsometry where
  toFun g := g.val.val.localMap i
  map_one' := rfl
  map_mul' g h := by
    change (g.val.val*h.val.val).localMap i = g.val.val.localMap i*h.val.val.localMap i
    rw [Monomial.mul_local,hexPointStabilizer_inv_fixed]

def hexPointZ (i : HexIndex) : hexPointStabilizer i := ⟨hexZ,rfl⟩

theorem hexPointZ_cycle (i : HexIndex) :
    hexPointLocal i (hexPointZ i) = localKappa ∨ hexPointLocal i (hexPointZ i) = localKappa⁻¹ := by
  change (if i.2 = 0 then localKappa else localKappa⁻¹) = localKappa ∨
    (if i.2 = 0 then localKappa else localKappa⁻¹) = localKappa⁻¹
  split_ifs <;> simp

theorem hexSign_coordinate (g : HexAutomorphisms) : hexSign g = Equiv.Perm.sign (hexCoordinateHom g) :=
  Equiv.Perm.sign_permCongr hexIndexEquiv (hexCoordinateHom g)

theorem hexPoint_odd_exists (i : HexIndex) : ∃ g : hexPointStabilizer i, hexSign g.val = -1 := by
  have hp : ∀ i : HexIndex, ∃ j k, j ≠ i ∧ k ≠ i ∧ j ≠ k := by decide
  obtain ⟨j,k,hji,hki,hjk⟩ := hp i
  obtain ⟨g,hg⟩ := hexCoordinateHom_surjective (Equiv.swap j k)
  have hi : g ∈ hexPointStabilizer i := by
    change hexCoordinateHom g i = i
    rw [hg]
    exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hji) (Ne.symm hki)
  refine ⟨⟨g,hi⟩,?_⟩
  rw [hexSign_coordinate,hg,Equiv.Perm.sign_swap hjk]

/-- A local three-cycle and an odd coordinate lift give the whole GL2(2). -/
theorem hexPointLocal_surjective (i : HexIndex) : Function.Surjective (hexPointLocal i) := by
  obtain ⟨x,hx⟩ := hexPoint_odd_exists i
  have he : x * hexPointZ i * x⁻¹ = (hexPointZ i)⁻¹ :=
    Subtype.ext (hex_conjugation_odd x.val hx)
  have hl := congrArg (hexPointLocal i) he
  simp only [map_mul,map_inv] at hl
  apply MonoidHom.range_eq_top.mp
  exact klein_subgroup_full_of_inverter _ _ _ (hexPointZ_cycle i)
    ⟨hexPointZ i,rfl⟩ ⟨x,rfl⟩ hl

end Atlas.Codes
