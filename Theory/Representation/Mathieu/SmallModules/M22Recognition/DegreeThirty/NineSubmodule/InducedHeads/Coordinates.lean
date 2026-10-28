module

public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.NineSubmodule.Models
public import Theory.AlgebraicGroup.Representations.Coinduction.RightQuotient
public import Mathlib.RepresentationTheory.FiniteIndex

/-!
# Right-coset coordinates for the two nine-space inductions

Induction from the literal M22 point stabilizer agrees with coinduction because
its index is finite. Evaluating equivariant functions on right-coset
representatives gives 22 copies of the nine-dimensional Hermitian module (or
its dual). Thus both induced modules have binary dimension 198. The action
formula retains the right multiplication convention of Mathlib induction.

These coordinates prepare concrete filtration certificates for the degree-table
step in Guralnick--Malle I, Proposition 5.1, pp.15--16. No decomposition or
irreducibility assertion is made here.
-/

@[expose] public noncomputable section
open Representation Sporadic.Mathieu
namespace Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads
abbrev Cosets := Quotient (QuotientGroup.rightRel Models.pointGroup)
abbrev CoordinateSpace (b : Bool) := Cosets → Models.Space b

/-- The actual induced action in right-coset coordinates. -/
def coordinateAction (b : Bool) : Representation (ZMod 2) M22 (CoordinateSpace b) :=
  Theory.AlgebraicGroup.Representation.coindRightQuotient Models.pointGroup
    (Rep.of (Models.pointAction b))

/-- Evaluate a coinduced function on the chosen right-coset representatives. -/
def coindCoordinateEquiv (b : Bool) :
    (Representation.coind Models.pointGroup.subtype (Models.pointAction b)).Equiv
      (coordinateAction b) := by
  refine Representation.Equiv.mk
    (Theory.AlgebraicGroup.Representation.coindVEquivRightQuotientPi
      Models.pointGroup (Rep.of (Models.pointAction b))) ?_
  intro g
  ext x q
  change x.val (q.out * g) = _
  dsimp [coordinateAction, Theory.AlgebraicGroup.Representation.coindRightQuotient]
  rw [LinearEquiv.symm_apply_apply]
  rfl

/-- An intertwining equivalence from the literal induction, not a character comparison. -/
def inducedCoordinateEquiv (b : Bool) :
    (Models.induced b).Equiv (coordinateAction b) := by
  classical
  exact (Representation.equivOfIso
    (Rep.indCoindIso (Rep.of (Models.pointAction b)))).trans (coindCoordinateEquiv b)

/-- Coordinate action, with the subgroup correction attached to right multiplication. -/
theorem coordinateAction_apply (b : Bool) (g : M22) (v : CoordinateSpace b) (q : Cosets) :
    coordinateAction b g v q =
      Models.pointAction b
        (Theory.AlgebraicGroup.Subgroup.rightCosetCorrection Models.pointGroup (q.out * g))
        (v (Quotient.mk (QuotientGroup.rightRel Models.pointGroup) (q.out * g))) := by
  exact Theory.AlgebraicGroup.Representation.coindRightQuotient_apply _ _ _ _ _

/-- The actual point stabilizer has 22 right cosets. -/
theorem card_cosets : Nat.card Cosets = 22 := by
  let : MulAction.IsPretransitive M22 (Fin 22) := m22_isPretransitive
  calc
    Nat.card Cosets = Nat.card (M22 ⧸ Models.pointGroup) :=
      Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel Models.pointGroup)
    _ = Models.pointGroup.index := rfl
    _ = 22 := by
      rw [MulAction.index_stabilizer_of_transitive]
      simp

/-- There are 22 independent nine-dimensional coordinate blocks. -/
theorem finrank_coordinateSpace (b : Bool) :
    Module.finrank (ZMod 2) (CoordinateSpace b) = 198 := by
  classical
  let : Fintype Cosets := Fintype.ofFinite Cosets
  rw [Module.finrank_pi_fintype]
  simp only [Models.finrank_space, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [← Nat.card_eq_fintype_card, card_cosets]

/-- The dimension comparison applies to the original quotient-tensor induction. -/
theorem finrank_inducedSpace (b : Bool) :
    Module.finrank (ZMod 2) (Models.InducedSpace b) = 198 := by
  rw [(inducedCoordinateEquiv b).toLinearEquiv.finrank_eq, finrank_coordinateSpace]

end Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads
