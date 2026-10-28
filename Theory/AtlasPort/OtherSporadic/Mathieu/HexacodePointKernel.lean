/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.HexacodePointOrders

/-!
# HexacodePointKernel

A hexacode point-stabilizer element acting trivially on the local alphabet has even
coordinate sign and a faithful coordinate action. The scalar-kernel classification and
the order-three letter cycles prove both assertions.

Source: `Atlas/Mathieu/HexacodePointKernel.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes

theorem klein_cycle_ne_one (P : KIsometry) (hP : P = localKappa ∨ P = localKappa⁻¹) : P ≠ 1 := by
  intro he
  rcases hP with rfl | rfl
  all_goals exact (by decide : _ ≠ _) (LinearEquiv.congr_fun he a)

theorem klein_cycle_square_ne_one (P : KIsometry) (hP : P = localKappa ∨ P = localKappa⁻¹) : P^2 ≠ 1 := by
  intro he
  rcases hP with rfl | rfl
  all_goals exact (by decide : _ ≠ _) (LinearEquiv.congr_fun he a)

theorem klein_cycle_ne_inverse (P : KIsometry) (hP : P = localKappa ∨ P = localKappa⁻¹) : P ≠ P⁻¹ := by
  intro he
  rcases hP with rfl | rfl
  all_goals exact (by decide : _ ≠ _) (LinearEquiv.congr_fun he a)

theorem hexPointKernel_even (i : HexIndex) (g : hexPointKernel i) : hexSign g.val.val = 1 := by
  rcases Int.units_eq_one_or (hexSign g.val.val) with he | he
  · exact he
  · exfalso
    have hg : g.val * hexPointZ i * g.val⁻¹ = (hexPointZ i)⁻¹ :=
      Subtype.ext (hex_conjugation_odd g.val.val he)
    have hl := congrArg (hexPointLocal i) hg
    have h1 : hexPointLocal i g.val = 1 := g.prop
    rw [map_mul,map_mul,map_inv,map_inv,h1,one_mul,inv_one,mul_one] at hl
    exact klein_cycle_ne_inverse _ (hexPointZ_cycle i) hl

theorem hexPointKernel_coordinate_one (i : HexIndex) (g : hexPointKernel i)
    (hg : hexCoordinateHom g.val.val = 1) : g = 1 := by
  have hl : hexPointLocal i g.val = 1 := g.prop
  rcases hex_kernel_trichotomy g.val.val hg with he | he | he
  · exact Subtype.ext (Subtype.ext he)
  · have hp : g.val = hexPointZ i := Subtype.ext he
    rw [hp] at hl
    exact False.elim (klein_cycle_ne_one _ (hexPointZ_cycle i) hl)
  · have hp : g.val = (hexPointZ i)^2 := Subtype.ext he
    rw [hp,map_pow] at hl
    exact False.elim (klein_cycle_square_ne_one _ (hexPointZ_cycle i) hl)

/-- The faithful coordinate representation of the local kernel. -/
def hexPointKernelCoordinate (i : HexIndex) : hexPointKernel i →* Equiv.Perm HexIndex :=
  hexCoordinateHom.comp ((hexPointStabilizer i).subtype.comp (hexPointKernel i).subtype)

theorem hexPointKernelCoordinate_injective (i : HexIndex) :
    Function.Injective (hexPointKernelCoordinate i) := by
  apply (hexPointKernelCoordinate i).ker_eq_bot_iff.mp
  apply bot_unique
  intro g hg
  exact hexPointKernel_coordinate_one i g hg

end Atlas.Codes
