module

public import Theory.Representation.Mathieu.SmallModules.Models
public import Theory.Mathieu.M23.Properties.Simplicity
public import Theory.Representation.SimpleHeadQuotient
public import Mathlib.RepresentationTheory.Induced

/-!
# Induced ten-dimensional point modules for M23

The actual stabilizer of point 9 in M23 is isomorphic to M22. Transport each
native ten-dimensional M22 module along an explicit marking, then induce
along the literal stabilizer inclusion. Keeping the marking is necessary:
small-module recognition permits a group automorphism.

The maximal quotients of these fixed induced modules are the finite
calculation used by `M23DegreeSpectrum`. No completeness or quotient-degree
assertion is made by their construction.

Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 5.1,
M23 paragraph, manuscript p.16; Aschbacher--Smith H.13.1 and K.4.
-/

@[expose] public noncomputable section
open Representation Sporadic.Mathieu MathieuCode
namespace Representation.MathieuSmall.M23DegreeSpectrum
namespace Models

abbrev pointGroup := MulAction.stabilizer M23 (9 : Fin 23)

abbrev Space : Bool → Type
  | false => M22Cocode
  | true => M22Code

instance spaceAddCommGroup (b : Bool) : AddCommGroup (Space b) := by
  cases b <;> dsimp [Space] <;> infer_instance

instance spaceModule (b : Bool) : Module (ZMod 2) (Space b) := by
  cases b <;> dsimp [Space] <;> infer_instance

instance spaceFiniteDimensional (b : Bool) : FiniteDimensional (ZMod 2) (Space b) := by
  cases b <;> dsimp [Space] <;> infer_instance

/-- The two native M22 actions, before choosing a stabilizer marking. -/
def action : (b : Bool) → Representation (ZMod 2) M22 (Space b)
  | false => m22CocodeRepresentation
  | true => m22CodeRepresentation

/-- The literal point-stabilizer action with its supplied marking. -/
def pointAction (e : pointGroup ≃* M22) (b : Bool) :
    Representation (ZMod 2) pointGroup (Space b) :=
  (action b).comp e.toMonoidHom

abbrev InducedSpace (e : pointGroup ≃* M22) (b : Bool) :=
  Representation.IndV pointGroup.subtype (pointAction e b)

/-- Induction along the inclusion in the native M23, retaining both actions. -/
def induced (e : pointGroup ≃* M22) (b : Bool) :
    Representation (ZMod 2) M23 (InducedSpace e b) :=
  Representation.ind pointGroup.subtype (pointAction e b)

theorem finrank_space (b : Bool) : Module.finrank (ZMod 2) (Space b) = 10 := by
  cases b
  · exact finrank_m22Cocode
  · exact finrank_m22Code

instance inducedFiniteDimensional (e : pointGroup ≃* M22) (b : Bool) :
    FiniteDimensional (ZMod 2) (InducedSpace e b) := by
  dsimp [InducedSpace, Representation.IndV]
  infer_instance

end Models

/-- The outstanding calculation concerns maximal quotients of concrete
inductions, not arbitrary representations or an assumed degree table. -/
def SmallInducedHeads : Prop :=
  ∀ (e : Models.pointGroup ≃* M22) (b : Bool)
    (N : Subrepresentation (Models.induced e b)), IsCoatom N →
    Module.finrank (ZMod 2) (Models.InducedSpace e b ⧸ N.toSubmodule) = 11 ∨
    24 < Module.finrank (ZMod 2) (Models.InducedSpace e b ⧸ N.toSubmodule)

end Representation.MathieuSmall.M23DegreeSpectrum
