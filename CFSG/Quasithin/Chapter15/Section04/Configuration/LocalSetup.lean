module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.Transfer
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.Hyperplanes
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.Geometry

/-!
# Construction of the local inputs to Section 15.4

This module collects the pre-identification construction for Aschbacher–Smith,
*The Classification of Quasithin Groups*, combined manuscript (1 March 2004),
15.4.14–20, printed pp.1161–1164.

The full first assertion of 15.4.17 is proved from QTKE and its stated local
hypotheses. The other current exports are intermediate proofs for the
hyperplane calculation, relative normalizers and outside factors, and the
core-normalizer specialization of the eventual Sylow theorem.

The source hyperplanes, the restriction on `s(Y)`, Baumann normalizer control,
15.4.17(2), the central geometry in 15.4.19, and the Sylow conclusion in 15.4.20
remain to be assembled. In particular this module does not yet construct
`Source.LocalData` and does not assert completion of 15.4.14–20.
-/
