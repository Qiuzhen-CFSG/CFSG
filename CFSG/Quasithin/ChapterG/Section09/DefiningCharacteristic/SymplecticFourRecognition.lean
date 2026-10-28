module

public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.Models
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.OrbitDegrees
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.ComponentBounds

/-!
# Toward the symplectic-four alternative of G.9.3

The target is the binary natural representation of the actual derived
symplectic matrix group. `Models` proves its faithfulness, field transport
and binary dimension. `ComponentBounds` proves the smallest-parameter
full automorphism bound through the actual A₆ equivalence, and transfers
model rank bounds to the original actor and original module.

`OrbitDegrees` proves the numerical gap from periodic tensor parameters:
16n, or 8n for an even field exponent. Deriving those parameters for every
nonbinary irreducible and constructing its natural-module equivalence
remain representation-theoretic obligations. The nonbinary automorphism
bound is supplied by the separate `SymplecticFour.EvenTwoRank` development
once its geometric premises have been discharged. The smallest derived
group also requires its own recognition argument under the original ambient
hypotheses. No theorem in this module asserts that these obligations are
complete.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), G.9.3(9),
printed pp.354,356--357; GLS volume 3, Examples 2.8.10(d).
-/
