module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Parabolic.Plane
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Parabolic.Residual
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Parabolic.Centralizer
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Parabolic.Structure
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Parabolic.Choice
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Parabolic.Exchange
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Parabolic.PointNode
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Parabolic.NodeExchange
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Parabolic.RankTen
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Parabolic.ResidualLocal
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Parabolic.RankFive

/-!
# Original plane and residual preparation for the terminal parabolics

The natural-three marking constructs the original elementary plane E and
identifies VI with the I-orbit of its first coordinate. The literal action
kernel gives I/O₂(I) ≃ SL₅(2), so the cubic rank and outer-group argument
identifies I and I^t with the residuals of the two point centralizers.
The plane residual and common point Sylow generate the actual point-join
centralizer of E. Thus this centralizer is t-invariant and coincides with
the centralizer in the conjugate point join. Its image under the original
action map is a proper flag parabolic. The actual centralizer is maximal
in the point join, and its intrinsic two-core quotient is L₄(2) in rank
five and S₃ × L₃(2) in rank ten. It escapes M and contains an actual
minimal parabolic over the prescribed point Sylow outside M. Exactly three
rank-one nodes lie between the point Sylow and this centralizer, and t
permutes them. The actual Pc = C_L(u) C_T(v) is an index-three cover
inside M, and the original natural action proves Pc is moved by t.
Consequently the escaping node is unique and fixed by t, and gives a
genuine exchange-fixed minimal parabolic in the original point join.

This completes these preliminary assertions on the supplied LinearFiveData.
The solvable join of Pc and its conjugate contradicts the middle-parabolic
diagram in rank ten. Thus the actual orbit has rank five.
The original moving node P_f is now constructed in L C_T(v), and
P P_f has actual two-core quotient S₃ × S₃. Both P_f and its conjugate
normalize O²(P). Its nontrivial two-core supplies a genuine two-local
overgroup, proving the SQTK cubic-rank upper bound on the residual product.
The moving cubic factors lift together to an elementary nine-group disjoint
from the plane centralizer. Its join with the original residual has three-rank
at least three, contradicting that upper bound. Thus LinearFiveExclusionAt is
proved, with no remaining actor, centralizer, or parabolic premise.
The owner qt-d-10-nona5-point-constrained retains the earlier preparation
and model reduction constructing LinearFiveData in final assembly.

Source: Aschbacher--Smith, 10.2.9, printed pp.752--753.
-/
