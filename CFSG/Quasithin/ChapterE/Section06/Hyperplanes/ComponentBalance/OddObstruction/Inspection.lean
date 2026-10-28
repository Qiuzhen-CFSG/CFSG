module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.Contracts
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction.Detection
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction.Inspection.Geometry
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction.Inspection.Reduction

/-!
# Model inspection for the detected component in E.6.19

`Geometry` constructs the faithful induced action containing the inner group,
with an order-two subgroup fixing the actual Sylow intersection pointwise.
`Reduction` eliminates alternatives (3) and (5), excludes Suzuki parameters,
and reduces the other alternatives to small classical models, Sp₄(4)′,
A₆ and its perfect three-cover, or the desired A₇ models. Perfect central
quotient transport retains all the specified covers and the acting group.

The odd-core calculations for the three non-seven families remain necessary
for final assembly. This module does not yet assert `IsSeven` for the detected
component, and does not assume those calculations as additional source inputs.
Detection and lifting of the supplied component are independent obligations.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8,
printed pp.247–248 (PDF pp.258–259), and E.6.19, printed p.252 (PDF p.263).
-/
