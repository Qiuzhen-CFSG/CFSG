module

public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.SourceGeometry
public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.FamilyAction
public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.LocalAssembly
public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.ParabolicAssembly

/-!
# Marked G₂ module geometry and local actions

`Assembly.source_marked_geometry` combines all eight clauses of 14.7.55
for the actual natural and trace-zero Weyl representations. The local
orders, Sylow action and earlier commutator identities construct the
marked singular point and doubly singular line. The full and derived
actors, their centralizers, fixed and moved spaces, offender family,
residual action, and commutator-family equality retain their literal
quotient interpretation. `SourceGeometry` distinguishes the incidence
hexagon from its point collinearity graph and applies the constructed
geometry to the 14.7.53 endpoint.

`LocalAssembly.source_marked_local_geometry` includes the faithful ambient
inclusion H ↪ G. It discharges every 14.7.55 input to the complete 14.7.56
local-action theorem: the lifted pencil is exactly V^Y and exactly the
ambient conjugates containing V₂, and the local vertex has the full
stabilizer action on its span. Fixing the family means normalizing each
member, not fixing all its vectors. Here Y is O²(C_H(V₂)).

The ambient pencil returned by that theorem feeds
`ParabolicAssembly.source_marked_parabolics`, proving 14.7.57 with the
marked line parabolic, its radical and, for the full G₂(2) actor, the
three A*-conjugates. Its A* is the centralizer of this same literal
quotient pencil span. Relative normality and the starred quotient maps
are retained throughout.

These are conditional source deductions. The parent 14.7.53 assembly
owns the genuine Section 14.7 setup, the equivariant identification in
14.7.54, and the stated earlier local identities. Precise earlier B.4.6
premises remain explicit, with producer qt-b-04-g2. No conclusion of
14.7.55–57 is an additional input to their combined source pipeline.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
pp.1066–1067; the endpoint application uses pp.1068–1069.
-/
