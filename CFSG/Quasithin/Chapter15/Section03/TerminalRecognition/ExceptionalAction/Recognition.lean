module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.Target
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.SourceGeometry
public import Theory.Representation.HexacodeAction.Field
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.AmbientGeometry
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.PlaneNormalizer

/-!
# Coordinates and marked geometry for terminal recognition

The concrete hexacode has a compatible three-dimensional four-element-field
structure, with its even cover acting in the special linear group and an
explicit odd involution acting by Frobenius. The source geometry is transported
from the ambient group to `G₀`, retaining the particular definite plane and
its binary dimension inside the normal-closure module.

The genuine full classifiers on the original pre-intersection input now
construct `HexacodeCoordinates` in the non-S₃ branch. The intersection
discharges the Thompson residual and surviving quotient premises; the
representation recognizer includes the odd coset. The ambient geometry
adapter constructs the marked-plane configuration from aligned earlier
local data, preserving the Sylow subgroup, conjugator and subgroup maps.
Both specified definite planes have full weight and are scalar-stable in
the same coordinates. The existing stabilizer calculation and quotient
lifting then give an A₅ quotient of their actual normalizers in J(G₀).

These are conditional implications from the genuine earlier local geometry
and classifier witnesses. Their source construction, core centrality,
the S₃ contradiction and the final solvability contradiction remain with
the source assembly of Theorem 15.3.1.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, printed
p.1155 (PDF p.1172), with the covering and field conventions of A.3.5 and K.1.3.
-/
