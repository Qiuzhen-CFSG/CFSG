/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/LeechModTwoAction.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.

CFSG adaptation: module/public-import boundaries, relocated imports, and
exposed definition bodies preserving upstream cross-module reduction.
Adapted for CFSG Lean 4.33.0.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.LeechQuadraticSpace

/-!
The full Leech isometry group acts on the binary quadratic space.
The lattice action descends through doubling and preserves the reduced norm and pairing.

The definitions and public statements follow the ATLAS source cited above.
-/

@[expose] public section

noncomputable section
namespace Atlas.Lattices
open Atlas.Codes

def leechModTwoMap (g : LeechIsometryGroup) : LeechModTwo →+ LeechModTwo :=
  QuotientAddGroup.lift twiceLeech (leechReduction.comp g.val.toAddEquiv.toAddMonoidHom) (by
    rintro x ⟨y,rfl⟩
    change leechReduction (g.val ((2 : ℕ) • y)) = 0
    rw [map_nsmul]
    exact (leechReduction_eq_zero _).mpr ⟨g.val y,rfl⟩)

theorem leechModTwoMap_reduce (g : LeechIsometryGroup) (x : leech) :
    leechModTwoMap g (leechReduction x) = leechReduction (g.val x) := rfl

theorem leechModTwoMap_one (a : LeechModTwo) : leechModTwoMap 1 a = a := by
  obtain ⟨x,rfl⟩ := leechReduction_surjective a
  rfl

theorem leechModTwoMap_mul (g h : LeechIsometryGroup) (a : LeechModTwo) :
    leechModTwoMap (g*h) a = leechModTwoMap g (leechModTwoMap h a) := by
  obtain ⟨x,rfl⟩ := leechReduction_surjective a
  rfl

def leechModTwoIsometry (g : LeechIsometryGroup) : LeechModTwo ≃ₗ[Bit] LeechModTwo where
  toFun := leechModTwoMap g
  invFun := leechModTwoMap g⁻¹
  left_inv a := by rw [← leechModTwoMap_mul,inv_mul_cancel,leechModTwoMap_one]
  right_inv a := by rw [← leechModTwoMap_mul,mul_inv_cancel,leechModTwoMap_one]
  map_add' := (leechModTwoMap g).map_add
  map_smul' := ZMod.map_smul (leechModTwoMap g)

def leechModTwoRepresentation : LeechIsometryGroup →* (LeechModTwo ≃ₗ[Bit] LeechModTwo) where
  toFun := leechModTwoIsometry
  map_one' := by ext a; exact leechModTwoMap_one a
  map_mul' g h := by ext a; exact leechModTwoMap_mul g h a

theorem leechModTwoRepresentation_reduce (g : LeechIsometryGroup) (x : leech) :
    leechModTwoRepresentation g (leechReduction x) = leechReduction (g.val x) := rfl

theorem leechModTwoRepresentation_quadratic (g : LeechIsometryGroup) (a : LeechModTwo) :
    leechQuadratic (leechModTwoRepresentation g a) = leechQuadratic a := by
  obtain ⟨x,rfl⟩ := leechReduction_surjective a
  rw [leechModTwoRepresentation_reduce,leechQuadratic_reduce,leechQuadratic_reduce]
  exact congrArg (fun n : ℤ => ((n / 16 : ℤ) : Bit)) (g.prop x x)

theorem leechModTwoRepresentation_polar (g : LeechIsometryGroup) (a b : LeechModTwo) :
    leechPolar (leechModTwoRepresentation g a) (leechModTwoRepresentation g b) = leechPolar a b := by
  obtain ⟨x,rfl⟩ := leechReduction_surjective a
  obtain ⟨y,rfl⟩ := leechReduction_surjective b
  rw [leechModTwoRepresentation_reduce,leechModTwoRepresentation_reduce,leechPolar_reduce,leechPolar_reduce]
  exact congrArg (fun n : ℤ => ((n / 8 : ℤ) : Bit)) (g.prop x y)

structure ModTwoQuadraticConstruction : Prop where
  card : Nat.card LeechModTwo = 2 ^ 24
  dimension : Module.finrank Bit LeechModTwo = 24
  surjective : Function.Surjective leechReduction
  kernel : ∀ x, leechReduction x = 0 ↔ ∃ y, (2 : ℕ) • y = x
  quadratic_formula : ∀ x, leechQuadratic (leechReduction x) = (leechHalfNorm x : Bit)
  polar_formula : ∀ x y, leechPolar (leechReduction x) (leechReduction y) = (leechIntegralPairing x y : Bit)
  polar_identity : ∀ a b, leechQuadratic (a+b) = leechQuadratic a + leechQuadratic b + leechPolar a b
  nondegenerate : ∀ a, (∀ b, leechPolar a b = 0) → a = 0
  action_compatible : ∀ g x, leechModTwoRepresentation g (leechReduction x) = leechReduction (g.val x)
  action_preserves_quadratic : ∀ g a, leechQuadratic (leechModTwoRepresentation g a) = leechQuadratic a

theorem leech_mod_two_quadratic_constructed : ModTwoQuadraticConstruction where
  card := leechModTwo_card
  dimension := leechModTwo_finrank
  surjective := leechReduction_surjective
  kernel := leechReduction_eq_zero
  quadratic_formula := leechQuadratic_reduce
  polar_formula := leechPolar_reduce
  polar_identity := leechQuadratic_add
  nondegenerate := leechPolar_nondegenerate
  action_compatible := leechModTwoRepresentation_reduce
  action_preserves_quadratic := leechModTwoRepresentation_quadratic

end Atlas.Lattices
