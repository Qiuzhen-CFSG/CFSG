module

public import Theory.Representation.Mathieu.M23DegreeSpectrum.Models
public import Theory.AlgebraicGroup.Representations.Coinduction.RightQuotient
public import Mathlib.RepresentationTheory.FiniteIndex

/-!
# The 230-dimensional M23 inductions in right-coset coordinates

Induction equals coinduction at finite index. Evaluation on right-coset
representatives identifies each marked point-module induction with 23
copies of its ten-dimensional binary space. The intertwining equivalence
and action formula retain Mathlib's right multiplication convention.

These coordinates support the remaining finite calculation of simple
quotients for GM02 Proposition 5.1, M23 paragraph, manuscript p.16.
They do not assert a composition-factor or head calculation.
-/

@[expose] public noncomputable section
open Representation Sporadic.Mathieu
namespace Representation.MathieuSmall.M23DegreeSpectrum.Coordinates

abbrev Cosets := Quotient (QuotientGroup.rightRel Models.pointGroup)
abbrev Space (b : Bool) := Cosets → Models.Space b

/-- The actual induced action in right-coset coordinates. -/
def action (e : Models.pointGroup ≃* M22) (b : Bool) :
    Representation (ZMod 2) M23 (Space b) :=
  Theory.AlgebraicGroup.Representation.coindRightQuotient Models.pointGroup
    (Rep.of (Models.pointAction e b))

/-- Evaluation of a coinduced function on chosen right-coset representatives. -/
def coindEquiv (e : Models.pointGroup ≃* M22) (b : Bool) :
    (Representation.coind Models.pointGroup.subtype (Models.pointAction e b)).Equiv
      (action e b) := by
  refine Representation.Equiv.mk
    (Theory.AlgebraicGroup.Representation.coindVEquivRightQuotientPi
      Models.pointGroup (Rep.of (Models.pointAction e b))) ?_
  intro g
  ext x q
  change x.val (q.out * g) = _
  dsimp [action, Theory.AlgebraicGroup.Representation.coindRightQuotient]
  rw [LinearEquiv.symm_apply_apply]
  rfl

/-- An equivariant comparison with the literal quotient-tensor induction. -/
def inducedEquiv (e : Models.pointGroup ≃* M22) (b : Bool) :
    (Models.induced e b).Equiv (action e b) := by
  classical
  exact (Representation.equivOfIso
    (Rep.indCoindIso (Rep.of (Models.pointAction e b)))).trans (coindEquiv e b)

/-- Right multiplication includes the actual subgroup correction. -/
theorem action_apply (e : Models.pointGroup ≃* M22) (b : Bool)
    (g : M23) (v : Space b) (q : Cosets) :
    action e b g v q =
      Models.pointAction e b
        (Theory.AlgebraicGroup.Subgroup.rightCosetCorrection Models.pointGroup (q.out * g))
        (v (Quotient.mk (QuotientGroup.rightRel Models.pointGroup) (q.out * g))) := by
  exact Theory.AlgebraicGroup.Representation.coindRightQuotient_apply _ _ _ _ _

/-- The literal stabilizer has 23 right cosets. -/
theorem card_cosets : Nat.card Cosets = 23 := by
  let : MulAction.IsPretransitive M23 (Fin 23) := m23_isPretransitive
  calc
    Nat.card Cosets = Nat.card (M23 ⧸ Models.pointGroup) :=
      Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel Models.pointGroup)
    _ = Models.pointGroup.index := rfl
    _ = 23 := by
      rw [MulAction.index_stabilizer_of_transitive]
      simp

/-- There are 23 independent ten-dimensional binary blocks. -/
theorem finrank_space (b : Bool) : Module.finrank (ZMod 2) (Space b) = 230 := by
  classical
  let : Fintype Cosets := Fintype.ofFinite Cosets
  rw [Module.finrank_pi_fintype]
  simp only [Models.finrank_space, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [← Nat.card_eq_fintype_card, card_cosets]

/-- The dimension belongs to the original induction for every marking. -/
theorem finrank_inducedSpace (e : Models.pointGroup ≃* M22) (b : Bool) :
    Module.finrank (ZMod 2) (Models.InducedSpace e b) = 230 := by
  rw [(inducedEquiv e b).toLinearEquiv.finrank_eq, finrank_space]

end Representation.MathieuSmall.M23DegreeSpectrum.Coordinates
