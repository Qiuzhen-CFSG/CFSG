module

public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.ThreeConjugates.Reduction
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.ThreeConjugates.StableImage
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.ThreeConjugates.ImageTransfer
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.ThreeConjugates.Generation
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.ThreeConjugates.ImageData
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.ThreeConjugates.CoordinateInterface
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.ThreeConjugates.Assembly

/-!
# Cyclic-three conjugates in a binary FF action

`ThreeConjugates.threeConjugates_of_solvableFF` proves the two internal-product
conclusions of Aschbacher–Smith B.1.12 (printed p. 73, PDF p. 84), conditional
only on the permitted universal valid B.1.8 theorem. It constructs compatible
multiplicative equivalences, actual SL₂(2) quotient factors, their prescribed
odd cores, and the transitive conjugation action induced by T.

The imported reductions prove relative solvability, K₀=O₃(H)=O²(H), faithful
fixed-space transfer, and identification of the kernel with O₂(M) inside M.
Coordinate recognition and ambient factor permutation are discharged by their
proved producers. The parent B.1.8/B.1.12 task retains the unconditional
assembly and must supply `ThreeConjugates.SolvableFFTheorem`.
-/
