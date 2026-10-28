module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Section
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Coordinates
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.SourceChecks
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Quotient
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Sylow
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Core

/-!
# Construction of the noncentral involution centralizer section

The proved setup distinguishes C = C_G(mu) from Q = C/<mu> and from the
eventual quotient C/A. Nonfusion makes the known order-64 subgroup C_C(pi)
a Sylow subgroup of C and identifies its image with the order-32 Sylow
subgroup C_Q(p).

The remaining assembly has two obligations. The transfer argument must
construct `QuotientCore D e` in Q. The recognition and lifting argument
must turn that intermediate subgroup into an actual `AlternatingSixSection C`,
using only the original local data and nonfusion in addition to the core.
This module does not yet assert the existence of that section.

Source: D. Held, "A Characterization of some multiply transitive permutation
groups, I", Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, proof of Lemma 4.2, pp.233--235.
-/
