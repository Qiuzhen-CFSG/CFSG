module

public import Theory.Mathieu.M22.TripleCover
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RepresentationTheory.Irreducible

/-!
# The binary twelve-dimensional action of the triple Mathieu cover

The genuine matrix carrier acts on column vectors. The action is faithful
because a matrix is determined by its linear map. The distinguished central
element satisfies X² + X + 1 = 0 as an operator; this retains the scalar
action needed for the later four-element field structure.

Source: Aschbacher–Smith, H.12.1(1–2), printed pp.393–394, citing James
(1973), Lemma 8.3. These construction lemmas do not assert the classification
of other irreducible modules.
-/

@[expose] public section

namespace Sporadic.Mathieu.M22TripleCover

open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open scoped Matrix

abbrev BinarySpace := Fin 12 → ZMod 2

/-- The actual column action of the concrete triple cover. -/
noncomputable def binaryRepresentation : Representation (ZMod 2) M22TripleCover BinarySpace :=
  Matrix.toLinAlgEquiv'.toMonoidHom.comp
    ((Units.coeHom Matrix12).comp derivedGroup.subtype)

theorem binaryRepresentation_apply (g : M22TripleCover) (v : BinarySpace) :
    binaryRepresentation g v = ((g : Matrix12ˣ) : Matrix12) *ᵥ v := rfl

theorem binaryRepresentation_faithful : Function.Injective binaryRepresentation := by
  intro g h he
  apply Subtype.ext
  apply Units.ext
  exact Matrix.toLinAlgEquiv'.injective he

theorem binarySpace_finrank : Module.finrank (ZMod 2) BinarySpace = 12 := by
  simp [BinarySpace]

/-- The nonidentity central scalar has minimal polynomial X² + X + 1. -/
theorem scalar_operator_quadratic :
    binaryRepresentation scalar ^ 2 + binaryRepresentation scalar + 1 = 0 := by
  have hm : ((scalarUnit : Matrix12) ^ 2 + (scalarUnit : Matrix12) + 1) = 0 := by
    rw [← Units.val_pow_eq_pow_val, coe_scalarUnit_sq, coe_scalarUnit]
    ext i j
    simp only [Matrix.add_apply, Matrix.one_apply, Matrix.zero_apply]
    have hadd (a b : ZMod 2) : a + (b + a) + b = 0 := by
      revert a b
      decide +kernel
    exact hadd _ _
  have h := congrArg (Matrix.toLinAlgEquiv' : Matrix12 ≃ₐ[ZMod 2] _) hm
  have hs : binaryRepresentation scalar = Matrix.toLinAlgEquiv' (scalarUnit : Matrix12) := rfl
  rw [hs]
  simpa only [map_add, map_pow, map_one, map_zero] using h

/-- No nonzero vector is fixed by the order-three central scalar. -/
theorem scalar_fixed_iff (v : BinarySpace) : binaryRepresentation scalar v = v ↔ v = 0 := by
  constructor
  · intro hv
    have h := congrArg (fun f : Module.End (ZMod 2) BinarySpace => f v)
      scalar_operator_quadratic
    have hchar : v + v = 0 := by
      have htwo : (2 : ZMod 2) = 0 := rfl
      simpa only [two_smul, zero_smul] using congrArg (fun a : ZMod 2 => a • v) htwo
    change binaryRepresentation scalar (binaryRepresentation scalar v) +
      binaryRepresentation scalar v + v = 0 at h
    simpa only [hv, hchar, zero_add] using h
  · rintro rfl
    exact map_zero _

end Sporadic.Mathieu.M22TripleCover
