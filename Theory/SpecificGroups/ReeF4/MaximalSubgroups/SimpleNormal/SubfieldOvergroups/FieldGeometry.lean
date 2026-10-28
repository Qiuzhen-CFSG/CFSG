module

public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.SimpleNormal.SubfieldOvergroups.FieldGeometry.Strict
public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.SimpleNormal.SubfieldOvergroups.FieldGeometry.BruhatDescent

/-!
# Field geometry for the Ree subfield overgroups

`strictSubfieldInclusions` proves every strict inclusion in the published
contract, including the binary lower endpoint and the ambient upper endpoint.
The descent components recover the coefficient field, positive root
coordinates, and diagonal torus parameters. Restricted Bruhat uniqueness
assembles them into `subfieldDescent_of_normalizerWords`, conditional only on
the normalizer's Weyl action and triangular torus kernel. Once those two
intrinsic calculations are supplied, this module will assemble the
unconditional `subfieldDescent` contract.

Source: Malle, J. Algebra 139 (1991), 52–69,
DOI 10.1016/0021-8693(91)90283-E; arXiv:0910.4758, proof of Theorem 5,
case 10. The source uses the full smaller Ree group, including ²F₄(2).
-/
