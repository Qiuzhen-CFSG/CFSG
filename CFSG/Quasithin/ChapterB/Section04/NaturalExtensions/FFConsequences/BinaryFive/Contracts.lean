module

public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.BinaryFive.Coordinates
public import Mathlib.GroupTheory.Complement

/-!
# The remaining geometric contracts in dimension five

The four-group witness uses the splitting owner's literal quotient-axis
definition. The end-node alternative uses a four-space and a complementary
line in the marked natural module. Their simultaneous stabilizer must be
a complement to the intrinsic two-core inside the actual maximal parabolic;
its action on the four-space is required to be the full faithful linear
action. Thus this contract specifies a genuine embedded Levi complement.

These are definitions of the remaining geometric conclusions, not proofs
of those conclusions. Source: Aschbacher–Smith, B.4.9(2)(i),(iv), printed
pp.94–95, combined manuscript of 1 March 2004.
-/

@[expose] public section
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.DoubleNatural.BinaryFive
open QuasisimpleSource BinaryLinear BinaryLinear.OuterCyclic
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {F : BinaryField} {ρ : Representation (ZMod 2) G V}

/-- A quadratic common-axis four-group on the original extension. It need
not be contained in the initially given offender. -/
def HasQuadraticAxisFour (d : DoubleNatural F 5 ρ) : Prop :=
  ∃ E : Subgroup G, QuadraticSplitting.IsAxisFour d E ∧ IsQuadratic ρ E

/-- Simultaneous stabilizers of a four-space and its complementary line
give the actual block-diagonal subgroup, rather than an abstract group tag. -/
def endNodeLevi (W K : Submodule (ZMod 2) (Space 5)) : Subgroup (LinearGroup 5) :=
  parabolic W ⊓ parabolic K

/-- Restriction to the four-space is the intended natural action of the Levi. -/
def endNodeAction (W K : Submodule (ZMod 2) (Space 5)) :
    endNodeLevi W K →* BinaryLinear.GL W :=
  (SmallParabolicLevi.subspaceAction W).comp (Subgroup.inclusion inf_le_left)

/-- The exact end-node containment, retaining an embedded Levi and its
faithful natural action, with the complement computed inside the parabolic. -/
def EndNodePlacement (d : DoubleNatural F 5 ρ) (hF : F.degree = 1)
    (A : Subgroup G) : Prop :=
  ∃ W K : Submodule (ZMod 2) (Space 5),
    Module.finrank (ZMod 2) W = 4 ∧ Module.finrank (ZMod 2) K = 1 ∧
    IsCompl W K ∧ IsCoatom (parabolic W) ∧
    (pCore 2 (parabolic W)).IsComplement'
      ((endNodeLevi W K).subgroupOf (parabolic W)) ∧
    Function.Bijective (endNodeAction W K) ∧
    A.map (groupEquiv d hF).toMonoidHom ≤ endNodeLevi W K

/-- The interior-node alternative, including actual maximality and the
identification of the unipotent radical with the embedded two-core. -/
def InteriorPlacement (d : DoubleNatural F 5 ρ) (hF : F.degree = 1)
    (A : Subgroup G) : Prop :=
  ∃ W : Submodule (ZMod 2) (Space 5),
    (Module.finrank (ZMod 2) W = 2 ∨ Module.finrank (ZMod 2) W = 3) ∧
    IsCoatom (parabolic W) ∧
    A.map (groupEquiv d hF).toMonoidHom ≤ radical W ∧
    radical W = (pCore 2 (parabolic W)).map (parabolic W).subtype

/-- Every clause of the two parabolic alternatives in B.4.9(2)(iv). -/
def DualAlternatives (d : DoubleNatural F 5 ρ) (hF : F.degree = 1)
    (A : Subgroup G) : Prop :=
  (rank A = 4 ∧ EndNodePlacement d hF A) ∨
    ((rank A = 5 ∨ rank A = 6) ∧ InteriorPlacement d hF A)

end CFSG.Quasithin.ChapterB.NaturalExtensions.DoubleNatural.BinaryFive
