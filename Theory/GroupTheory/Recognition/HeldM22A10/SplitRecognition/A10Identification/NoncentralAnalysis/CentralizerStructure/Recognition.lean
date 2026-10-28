module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Core
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Section
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Coordinates
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.SourceChecks
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.Lift
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.NoEight
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.Quotient

/-!
# Recognition of the lifted core in Held's noncentral centralizer

The inverse image of the supplied quotient core is a central extension by
<mu>. Its derived subgroup, viewed inside C, is the canonical candidate for
A. The current results construct this lift and its exact quotient, exclude
elements of order eight in C, and identify C/A as D8 once the derived map
A → M is bijective. The conditional A6 section assembly uses actual subgroup
and quotient equivalences.

Three mathematical inputs remain for the unconditional recognition theorem:
the A6/PSL2(7) dichotomy for M, injectivity of the derived map (central
splitting), and the faithful-action argument excluding PSL2(7). No existence
of these inputs is asserted by this module. The last argument must recover
the source actors and their compatible normalizations before using the
order-eight obstruction.

Source: D. Held, "A Characterization of some multiply transitive permutation
groups, I", Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, proof of Lemma 4.2, pp.234--235.
-/
