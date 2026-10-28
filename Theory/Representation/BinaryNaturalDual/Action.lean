module

public import Theory.Representation.BinaryNaturalDual
public import Theory.SpecificGroups.BinaryLinear.NaturalDualFlag
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.RepresentationTheory.Basic

/-!
# Coordinate specification of the natural-plus-dual action

The linear group acts naturally on the first summand and contragrediently
on the second. The dot product identifies the natural coordinates with
their dual, so exchanging the two coordinates defines an involution
preserving evaluation.

`CoordinateAction` specifies an extension to the actual automorphism group
by its values on inner automorphisms and inverse transpose. It contains
no orbit, stabilizer, or subgroup-classification assumptions. Existence
of this extension and comparison with an arbitrary source module are
separate obligations for the H.9 model construction.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), H.9,
printed pp.389–392; the graph automorphism is ordinary inverse transpose.
-/

@[expose] public section

namespace BinaryNaturalDual
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- The actual natural and contragredient representation. -/
def naturalDualRepresentation : Representation (ZMod 2) (BinaryLinear.GL V) (Space V) :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp BinaryLinear.NaturalDualFlag.action

@[simp] theorem naturalDualRepresentation_apply (g : BinaryLinear.GL V) (v : Space V) :
    naturalDualRepresentation g v = (g v.1, g.symm.dualMap v.2) := by
  apply Prod.ext
  · exact BinaryLinear.NaturalDualFlag.action_fst g v
  · ext x
    exact BinaryLinear.NaturalDualFlag.action_snd g v x

/-- The marked natural-plus-dual coordinate space. -/
abbrev CoordinateSpace (n : ℕ) := Space (BinaryLinear.OuterCyclic.Space n)

/-- The coordinate operator extending inverse transpose. -/
def coordinateSwap (n : ℕ) : CoordinateSpace n ≃ₗ[ZMod 2] CoordinateSpace n :=
  (LinearEquiv.prodComm (ZMod 2) _ _).trans
    ((dotProductEquiv (ZMod 2) (Fin n)).symm.prodCongr
      (dotProductEquiv (ZMod 2) (Fin n)))

theorem coordinateSwap_apply (n : ℕ) (v : CoordinateSpace n) :
    coordinateSwap n v =
      ((dotProductEquiv (ZMod 2) (Fin n)).symm v.2,
        dotProductEquiv (ZMod 2) (Fin n) v.1) := rfl

theorem coordinateSwap_involutive (n : ℕ) : Function.Involutive (coordinateSwap n) := by
  intro v
  simp only [coordinateSwap_apply, LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]

theorem coordinateSwap_quadratic (n : ℕ) (v : CoordinateSpace n) :
    quadratic (coordinateSwap n v) = quadratic v := by
  change dotProduct v.1 ((dotProductEquiv (ZMod 2) (Fin n)).symm v.2) = v.2 v.1
  rw [dotProduct_comm]
  exact LinearMap.congr_fun ((dotProductEquiv (ZMod 2) (Fin n)).apply_symm_apply v.2) v.1

/-- A representation of the actual automorphism group with specified
inner and graph actions. Its existence is not assumed as a source theorem. -/
structure CoordinateAction (n : ℕ) where
  representation : Representation (ZMod 2)
    (MulAut (BinaryLinear.OuterCyclic.LinearGroup n)) (CoordinateSpace n)
  on_inner : ∀ (g : BinaryLinear.OuterCyclic.LinearGroup n) (v : CoordinateSpace n),
    representation (MulAut.conj g) v = naturalDualRepresentation g v
  on_graph : ∀ v : CoordinateSpace n,
    representation (BinaryLinear.OuterCyclic.graphLinear n) v = coordinateSwap n v

end BinaryNaturalDual
