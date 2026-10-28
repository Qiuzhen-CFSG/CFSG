module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.EmbeddingReduction.Assembly

/-!
# Embedding and residual reduction for the contrary Sylow overgroup

`PlacedX.embedding_residual_reduction` establishes the two source configurations
for the actual H-normal closure K of X, proves K = O^{3′}(H), and replaces H by KU.
It retains I-containment, local-family membership, the actual Sylow U, global
maximal Sylow order, and the Sylow assertion in the new core normalizer. Both
component configurations and the raw placed configuration survive replacement.

The binary branch includes actual PSL₄(2)/PSL₅(2) models and the full automorphism
quotient. Its residual proof uses the proved centerlessness, rank and outer order
directly. The exchanged branch retains the actual two-component product and
complement factorization, with relative component normality, and verifies both
premises of source 1.2.2(a).

The universal corrected local 1.3.4, full 1.2.1(3), and exact 1.2.2(a) are explicit
earlier-result parameters for the source assembly owner. This conditional
reduction does not assert the final Sylow theorem 15.4.20 or use 15.4.21–23.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
printed pp.504, 509–511 and pp.1163–1164.
-/
