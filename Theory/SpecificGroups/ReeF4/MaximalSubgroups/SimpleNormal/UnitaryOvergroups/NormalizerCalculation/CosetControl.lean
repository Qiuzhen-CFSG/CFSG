module

public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.SimpleNormal.UnitaryOvergroups.NormalizerCalculation.Geometry
public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.SimpleNormal.UnitaryOvergroups.NormalizerCalculation.CosetControl.MatrixGeometry

/-!
# Conditional coset control for the projective unitary normalizer

The matrix reduction cancels the common field part of two outside elements.
The ambient centralizer containment then lifts the resulting unitary action
back to the supplied projective extension. The two geometric inputs remain
explicit: this module does not yet assert `unitaryNormalizerCosetControl`.

Source: Malle, J. Algebra 139 (1991), 52–69,
DOI 10.1016/0021-8693(91)90283-E; PGU₃(q):2 is case 7 of the unconditional
list in the proof of Theorem 5 of arXiv:0910.4758, p.3.
-/

namespace ReeF4.MaximalSubgroups.SimpleNormal

/-- Conditional assembly from the ambient centralizer containment and concrete
semilinear action formulas. Both Ree matrix obligations remain to be proved. -/
public theorem unitaryNormalizerCosetControl_of_matrix_actions
    (hCentralizer : UnitaryNormalizerCentralizerControl)
    (hActions : UnitaryNormalizerSemilinearActions) : UnitaryNormalizerCosetControl := by
  intro m hm M hM hsolv hR S hSn hSs hSa hC F _ _ J hcard hconj e E t ht htH x hx hxH
  exact E.outside_coset_control
    (hCentralizer m hm M hM hsolv hR S hSn hSs hSa hC F J hcard hconj e E)
    (hActions m hm M hM hsolv hR S hSn hSs hSa hC F J hcard hconj e E)
    ⟨t, ht⟩ ⟨x, hx⟩ htH hxH

end ReeF4.MaximalSubgroups.SimpleNormal
