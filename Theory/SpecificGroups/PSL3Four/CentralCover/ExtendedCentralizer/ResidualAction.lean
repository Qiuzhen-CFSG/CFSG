module

public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.Geometry
public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.ResidualAction.Projection
public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.ResidualAction.LiftDefect
public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.ResidualAction.CenterControl

/-!
# Residual action and centralizer lifting in the four-cover

The linear E₉ residual projects faithfully to an actual Sylow three-subgroup
of PSL₃(4). A bound of eighteen for its projective pointwise fixer implies
that the residual-action kernel modulo E₉ is a two-group.

The chosen graph-field involution has nonidentity projective image. Its
centralizer-lifting defect is a central commutator, constant on projective
fibers. Thus fullness of the projective action alone does not establish
fullness of the action in the cover.

An alternative odd-core argument uses the normal central four: an order bound
of 144 on its centralizer inside C_I(w) suffices to identify the odd core
with the linear E₉ residual. The projective fixer and cover centralizer bounds
are explicit remaining model calculations, not assertions of this module.

Source: Aschbacher--Smith, 15.3.38, printed pp.1136--1137, manuscript of
1 March 2004.
-/
