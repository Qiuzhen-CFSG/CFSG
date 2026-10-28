module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.ImageCases.Estimates
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.ImageCases.Representation

/-!
# The order-two image estimates in the first pairing argument

This entry point exposes `ImageCases.small_image_estimate`, proved in
`Representation`, for the assembly of the two image cases. Its hypotheses are
the earlier local source, geometry, module and normalization facts, universal
initial facts, the contrary commutator bound, the two `BoundsAt` clauses, and
the image-order equality `(Q R p.a).relIndex (V R p.c) = 2`.

The proof selects a moving neighbor whose commutator with the critical endpoint
escapes `fixedCore R p.c`. The actual natural section and the triple bound make
a nonzero commutator row injective modulo the literal fixed preimage. Applying
this to `V R p.c ⊓ Q R p.a` transfers its quotient-index lower bound of four to
the commutator image. At the starting vertex, the radius commutator lies outside
the fixed preimage and centralizes that intersection. The natural-section
kernel dichotomy therefore gives the whole-V commutator containment.

All quotient calculations retain the subgroup intersections, and normality is
relative to the finite vertex stabilizers. The selected moving witness, the
commutator-image lower bound, and the whole-V containment are conclusions of
the exported theorem.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.3.2)(2), the last paragraph of printed p.883 and the second paragraph
of printed p.884, specialized to the binary case.
-/
