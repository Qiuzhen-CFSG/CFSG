module

public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.Coordinates
public import Theory.Representation.FactorDegreeFiltration
public import Theory.Representation.FactorDegreeFiltration.FiniteDual
public import Theory.AlgebraicGroup.Representations.Coinduction.RightQuotientDual

/-!
# Transfer between the two Hermitian induced filtrations

The two point actions are literal binary contragredients through the same
point-stabilizer marking. The sum of evaluation pairings over right cosets
identifies their coordinate actions as duals. Combining this with the actual
induction/coinduction coordinate maps also compares the original inductions.
Reversing a finite filtration through duality therefore transfers every set
of allowed simple-factor degrees from the false orientation to the true one.

This discharges the second filtration input of the induced-head argument,
conditional on the independently constructed first filtration. It does not
assert that first filtration or identify a head with a socle.

Source application: Guralnick--Malle, Classification of 2F-modules I,
Proposition 5.1, pp.15--16; Aschbacher--Smith, Chapter K, pp.451--452,457.
-/

@[expose] public noncomputable section

namespace Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule
open Representation Sporadic.Mathieu
namespace InducedHeads

/-- Both point modules use the same actual point-stabilizer marking. -/
theorem pointAction_dual : (Models.pointAction false).dual = Models.pointAction true := by
  ext g φ v
  change φ (Models.hermitian ((MathieuCode.m22PointStabilizerEquiv 0) g⁻¹) v) =
    φ (Models.hermitian (((MathieuCode.m22PointStabilizerEquiv 0) g)⁻¹) v)
  rw [map_inv]

/-- The sum of evaluation pairings on right cosets identifies the two
coordinate modules as contragredient representations. -/
def coordinateDualEquiv :
    (coordinateAction true).Equiv (coordinateAction false).dual := by
  change (Theory.AlgebraicGroup.Representation.coindRightQuotient Models.pointGroup
    (Rep.of (Models.pointAction true))).Equiv _
  rw [← pointAction_dual]
  exact Theory.AlgebraicGroup.Representation.rightQuotientDualEquiv
    Models.pointGroup (Models.pointAction false)

/-- Actual induction commutes with duality for these marked point modules. -/
def inducedDualEquiv : (Models.induced true).Equiv (Models.induced false).dual :=
  ((inducedCoordinateEquiv true).trans coordinateDualEquiv).trans
    (inducedCoordinateEquiv false).contragredient

/-- The same factor-degree condition transfers on the literal induced spaces. -/
theorem inducedFiltration_true_of_false {D : Set ℕ}
    (h : FactorDegreeFiltration D (Models.induced false)) :
    FactorDegreeFiltration D (Models.induced true) :=
  h.dual.of_equiv inducedDualEquiv.symm

end InducedHeads

/-- Transfer the checked Hermitian filtration to the induction of the dual
Hermitian point module. The original filtration remains an explicit input. -/
theorem coordinateFiltration_true_of_false {D : Set ℕ}
    (h : FactorDegreeFiltration D (InducedHeads.coordinateAction false)) :
    FactorDegreeFiltration D (InducedHeads.coordinateAction true) :=
  h.dual.of_equiv InducedHeads.coordinateDualEquiv.symm

end Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule
