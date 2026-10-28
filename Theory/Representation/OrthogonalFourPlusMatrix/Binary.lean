module

public import Theory.Representation.OrthogonalFourPlusMatrix.Action
public import Theory.Representation.SL2FourNaturalOrbits.Model
public import Theory.Representation.BinaryOffender.Defs

/-!
# The binary determinant module over F₄

This fixes one concrete field and the literal `SL₂(4) × SL₂(4)` action on
matrices. Its binary action is faithful and has dimension eight. The
coordinate equivalence is the restriction of the determinant isometry in
`Action`, retaining the same underlying vectors and group elements.

The comparison with the existing elementary orthogonal carrier is deliberately
separate. These definitions are shared by that comparison and the intrinsic
matrix calculations used in Aschbacher–Smith 13.8.16(1), printed pp.952–953.
-/

@[expose] public noncomputable section
namespace ClassicalOrthogonal.FourPlusMatrix.Binary

abbrev F := Representation.SL2FourNatural.F
abbrev V := Mat (F := F)
abbrev G := PairSL (F := F)

/-- Restriction of the actual matrix action to F₂, with invertibility retained. -/
def linearAction : G →* (V ≃ₗ[ZMod 2] V) where
  toFun g := (matrixHom g).restrictScalars (ZMod 2)
  map_one' := by
    apply LinearEquiv.ext
    intro v
    exact LinearEquiv.congr_fun matrixHom.map_one v
  map_mul' g h := by
    apply LinearEquiv.ext
    intro v
    exact LinearEquiv.congr_fun (matrixHom.map_mul g h) v

/-- The binary representation of the two actual special linear factors. -/
def action : Representation (ZMod 2) G V where
  toFun g := (linearAction g).toLinearMap
  map_one' := congrArg LinearEquiv.toLinearMap linearAction.map_one
  map_mul' g h := congrArg LinearEquiv.toLinearMap (linearAction.map_mul g h)

@[simp] theorem action_apply (g : G) (v : V) :
    action g v = g.1.val * v * g.2⁻¹.val := rfl

@[simp] theorem linearAction_apply (g : G) (v : V) : linearAction g v = action g v := rfl

/-- Restricting scalars does not lose faithfulness. -/
theorem action_injective : Function.Injective action := by
  intro g h he
  apply matrixHom_injective
  apply LinearEquiv.ext
  intro v
  exact congrArg (fun f : Module.End (ZMod 2) V => f v) he

/-- Determinant coordinates, restricted to the binary field. -/
def binaryCoordinates : VectorD 2 F ≃ₗ[ZMod 2] V :=
  (coordinates (F := F)).restrictScalars (ZMod 2)

/-- The same coordinate map intertwines the actual isometry action. -/
theorem binaryCoordinates_equivariant (g : G) (v : VectorD 2 F) :
    binaryCoordinates ((toOrthogonal g).val v) = action g (binaryCoordinates v) :=
  toOrthogonal_coordinates g v

/-- The concrete coefficient field has binary dimension two. -/
theorem finrank_field : Module.finrank (ZMod 2) F = 2 := by
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F)
  rw [Nat.card_eq_fintype_card, Representation.SL2FourNatural.card_field,
    Nat.card_eq_fintype_card, ZMod.card] at h
  exact (Nat.pow_right_injective (by decide : 1 < (2 : ℕ))
    (show 2 ^ 2 = 2 ^ Module.finrank (ZMod 2) F from h)).symm

/-- The determinant module has binary dimension eight. -/
theorem finrank_binary : Module.finrank (ZMod 2) V = 8 := by
  change Module.finrank (ZMod 2) (Fin 2 → Fin 2 → F) = 8
  rw [Module.finrank_pi_fintype, Module.finrank_pi_fintype]
  simp only [Fin.sum_univ_two]
  rw [finrank_field]
  norm_num

end ClassicalOrthogonal.FourPlusMatrix.Binary
