module
public import Theory.Representation.AlternatingSevenConjugatePair
public import Theory.Representation.SpecialLinearNatural
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
public import Mathlib.GroupTheory.Perm.ViaEmbedding

/-!
# The binary four-space for the alternating seven-letter group

Embed A₇ in A₈ by fixing the eighth letter, use the actual exceptional
A₈ ≃ PSL₄(2) comparison, and invert the central quotient SL₄(2) ≃ PSL₄(2).
The resulting faithful action on column vectors is the natural four-space.
Conjugating by the transposition (0 1) defines the second action.

This module publishes the actual actions and their faithfulness. Irreducibility,
inequivalence, and their extension to a conjugate pair remain separate proofs.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
H.8, printed p.389/PDF p.400. The exceptional comparison is the attributed
ATLAS port imported above; no comparison is inferred from group orders alone.
-/

@[expose] public section

open scoped MatrixGroups
open Representation
namespace Representation.AlternatingSevenConjugatePair.Model
noncomputable section
abbrev Four := Fin 4 → ZMod 2
abbrev Eight := Four × Four

/-- The first seven letters in the eight-letter set. -/
def letterEmbedding : Fin 7 ↪ Fin 8 := ⟨Fin.castSucc, Fin.castSucc_injective 7⟩

/-- The literal point-stabilizer embedding fixing the last letter. -/
def alternatingEmbedding : alternatingGroup (Fin 7) →* alternatingGroup (Fin 8) where
  toFun a := ⟨Equiv.Perm.viaEmbeddingHom letterEmbedding a, by
    classical
    rw [Equiv.Perm.mem_alternatingGroup]
    rw [Equiv.Perm.viaEmbeddingHom_apply]
    simpa only [Equiv.Perm.viaEmbedding, Equiv.Perm.sign_extendDomain] using
      (show Equiv.Perm.sign a.val = 1 from a.property)⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ a.val b.val)

theorem alternatingEmbedding_injective : Function.Injective alternatingEmbedding := by
  intro a b h
  apply Subtype.ext
  exact Equiv.Perm.viaEmbeddingHom_injective letterEmbedding (congrArg Subtype.val h)

/-- The embedding obtained from the actual A₈–SL₄(2) comparison. -/
def linearEmbedding : alternatingGroup (Fin 7) →* SL(4, ZMod 2) :=
  Atlas.Order20160A8.sl4TwoEquivPSL.symm.toMonoidHom.comp
    (Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.toMonoidHom.comp alternatingEmbedding)

theorem linearEmbedding_injective : Function.Injective linearEmbedding :=
  Atlas.Order20160A8.sl4TwoEquivPSL.symm.injective.comp
    (Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.injective.comp alternatingEmbedding_injective)

/-- The restricted natural four-dimensional binary representation. -/
def natural : Representation (ZMod 2) (alternatingGroup (Fin 7)) Four :=
  (specialLinearNatural 4).comp linearEmbedding

theorem natural_apply (a : alternatingGroup (Fin 7)) (v : Four) :
    natural a v = Matrix.mulVec (linearEmbedding a).val v := rfl

theorem natural_faithful : Function.Injective natural := by
  intro a b h
  apply linearEmbedding_injective
  apply Matrix.SpecialLinearGroup.toLin'_injective
  apply LinearEquiv.ext
  intro v
  exact congrArg (fun f : Module.End (ZMod 2) Four => f v) h

def transposition : Equiv.Perm (Fin 7) := Equiv.swap 0 1

theorem transposition_sq : transposition ^ 2 = 1 := by decide

/-- Conjugation by the odd involution (0 1). -/
def outer : MulAut (alternatingGroup (Fin 7)) where
  toFun a := ⟨transposition * a.val * transposition, by
    change Equiv.Perm.sign _ = 1
    simp only [map_mul, show Equiv.Perm.sign transposition = -1 by decide,
      show Equiv.Perm.sign a.val = 1 from a.property]
    decide⟩
  invFun a := ⟨transposition * a.val * transposition, by
    change Equiv.Perm.sign _ = 1
    simp only [map_mul, show Equiv.Perm.sign transposition = -1 by decide,
      show Equiv.Perm.sign a.val = 1 from a.property]
    decide⟩
  left_inv a := by
    apply Subtype.ext
    change transposition * (transposition * a.val * transposition) * transposition = a.val
    simp [transposition, mul_assoc]
  right_inv a := by
    apply Subtype.ext
    change transposition * (transposition * a.val * transposition) * transposition = a.val
    simp [transposition, mul_assoc]
  map_mul' a b := by
    apply Subtype.ext
    change transposition * (a.val * b.val) * transposition =
      (transposition * a.val * transposition) * (transposition * b.val * transposition)
    simp [transposition, mul_assoc]

/-- The outer conjugate of the restricted natural module. -/
def outerNatural : Representation (ZMod 2) (alternatingGroup (Fin 7)) Four :=
  natural.comp outer.toMonoidHom

theorem outerNatural_faithful : Function.Injective outerNatural :=
  natural_faithful.comp outer.injective

/-- The product (0 1 2)(3 4 5), fixing the seventh letter. -/
def doubleThreeCycle : alternatingGroup (Fin 7) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 3 4 * Equiv.swap 4 5, by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide⟩

theorem doubleThreeCycle_order : orderOf doubleThreeCycle = 3 :=
  orderOf_eq_prime (by decide : doubleThreeCycle ^ 3 = 1) (by decide)

theorem doubleThreeCycle_cycleType :
    (doubleThreeCycle : Equiv.Perm (Fin 7)).cycleType = {3, 3} := by decide

theorem four_dimension : Module.finrank (ZMod 2) Four = 4 := by simp [Four]
theorem eight_dimension : Module.finrank (ZMod 2) Eight = 8 := by
  simp [Eight, Module.finrank_prod]
end
end Representation.AlternatingSevenConjugatePair.Model
