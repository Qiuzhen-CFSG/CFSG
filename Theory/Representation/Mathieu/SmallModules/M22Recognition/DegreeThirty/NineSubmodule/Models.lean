module

public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.Restriction
public import Theory.Representation.HermitianTensorThree.ImageOuter.Models
public import Mathlib.RepresentationTheory.Induced

/-!
# The two Hermitian point modules and their M22 inductions

The Hermitian matrices over GF(4) have binary dimension nine and action
X ↦ g X σ(g)ᵀ, where σ squares each entry. The kernel calculation identifies the action image
with the literal central quotient PSL(3,4). This module and its dual are
transported to the native point stabilizer using its actual isomorphism.
Both are then induced along that stabilizer's inclusion in M22.

These are concrete candidate modules for the degree-table step in
Guralnick–Malle I, Proposition 5.1, pp.15–16. Their completeness and the
small degrees of their induced heads are separate obligations. The
Hermitian construction is Aschbacher–Smith H.4.4, printed p.381.
-/

@[expose] public noncomputable section
open Representation Sporadic.Mathieu
namespace Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule
namespace Models
open HermitianTensorThree

abbrev HermitianSpace := HermitianTensorThree.Space 1

def imageBinaryAction : Representation (ZMod 2) (Image 1) HermitianSpace where
  toFun g := (imageAction 1 g).toAddMonoidHom.toZModLinearMap 2
  map_one' := by
    apply LinearMap.ext
    intro X
    exact congrArg (fun f => f X) (imageAction 1).map_one
  map_mul' g h := by
    apply LinearMap.ext
    intro X
    exact congrArg (fun f => f X) ((imageAction 1).map_mul g h)

/-- The projective Hermitian action, with its actual central quotient marking. -/
def hermitian : Representation (ZMod 2) Matrix.PSL3Four.PSL HermitianSpace :=
  imageBinaryAction.comp
    (ImageOuter.imageEquivPSL 1 (by decide)).symm.toMonoidHom

abbrev Space : Bool → Type
  | false => HermitianSpace
  | true => Module.Dual (ZMod 2) HermitianSpace

instance spaceAddCommGroup (b : Bool) : AddCommGroup (Space b) := by
  cases b <;> dsimp [Space] <;> infer_instance

instance spaceModule (b : Bool) : Module (ZMod 2) (Space b) := by
  cases b <;> dsimp [Space] <;> infer_instance

instance spaceFiniteDimensional (b : Bool) : FiniteDimensional (ZMod 2) (Space b) := by
  cases b <;> dsimp [Space] <;> infer_instance

/-- The two projective tensor orientations. -/
def projective : (b : Bool) → Representation (ZMod 2) Matrix.PSL3Four.PSL (Space b)
  | false => hermitian
  | true => hermitian.dual

abbrev pointGroup := MulAction.stabilizer M22 (0 : Fin 22)

/-- Transport to the literal stabilizer, using its actual PSL(3,4) identification. -/
def pointAction (b : Bool) : Representation (ZMod 2) pointGroup (Space b) :=
  (projective b).comp (MathieuCode.m22PointStabilizerEquiv 0).toMonoidHom

abbrev InducedSpace (b : Bool) := Representation.IndV pointGroup.subtype (pointAction b)

/-- Induction along the actual point-stabilizer inclusion in M22. -/
def induced (b : Bool) : Representation (ZMod 2) M22 (InducedSpace b) :=
  Representation.ind pointGroup.subtype (pointAction b)

theorem finrank_space (b : Bool) : Module.finrank (ZMod 2) (Space b) = 9 := by
  cases b
  · simpa using HermitianTensorThree.finrank_binary 1
  · change Module.finrank (ZMod 2) (Module.Dual (ZMod 2) HermitianSpace) = 9
    rw [Subspace.dual_finrank_eq]
    simpa using HermitianTensorThree.finrank_binary 1

theorem hermitian_mk (g : Matrix.PSL3Four.SL) (X : HermitianSpace) :
    hermitian (QuotientGroup.mk g) X = binaryAction 1 g X := by
  change imageAction 1 ((ImageOuter.imageEquivPSL 1 (by decide)).symm
    (QuotientGroup.mk g)) X = action 1 g X
  rw [← ImageOuter.imageEquivPSL_toImage 1 (by decide) g]
  simp only [MulEquiv.symm_apply_apply, imageAction_toImage]

/-- These induced spaces are finite-dimensional, before any head calculation. -/
instance inducedFiniteDimensional (b : Bool) :
    FiniteDimensional (ZMod 2) (InducedSpace b) := by
  dsimp [InducedSpace, Representation.IndV]
  infer_instance

end Models
/-- A condition on the maximal quotients of two fixed concrete induced modules.
Its proof is the remaining finite representation calculation. -/
def SmallInducedHeads : Prop :=
  ∀ (b : Bool) (N : Subrepresentation (Models.induced b)), IsCoatom N →
    Module.finrank (ZMod 2) (Models.InducedSpace b ⧸ N.toSubmodule) = 1 ∨
    Module.finrank (ZMod 2) (Models.InducedSpace b ⧸ N.toSubmodule) = 10 ∨
    30 < Module.finrank (ZMod 2) (Models.InducedSpace b ⧸ N.toSubmodule)

end Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule
