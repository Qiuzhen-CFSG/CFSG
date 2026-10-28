module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Assembly
public import Theory.Representation.HigmanSims.Twenty.Marked

/-!
# Exact exterior-square row-section certificates for the small binary HS models

The exterior coordinates are ordered (j,k), with k<j, first by j and then k,
as in `Binary/source/section56.json` and `section132.json`. A certificate gives
independent kernel and lifted rows, a right inverse of their concatenation,
and the two literal marked invariance identities. These are finite linear
algebra obligations, independent of constructing the action on the dual of
the row quotient. No certificate or carrier descent is asserted by this file.

Source and attribution: `../source/README.md`, ATLAS HSG1-f2r20B0,
HSG1-f2r56B0 and HSG1-f2r132B0. The permutation generators keep the inverted
right-permutation convention of `Twenty.Marked`.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Small

/-- The literal coordinate order in the supplied exterior-square certificates. -/
def exteriorPairs : Array (Fin 20 × Fin 20) := #[
  (1, 0),
  (2, 0),
  (2, 1),
  (3, 0),
  (3, 1),
  (3, 2),
  (4, 0),
  (4, 1),
  (4, 2),
  (4, 3),
  (5, 0),
  (5, 1),
  (5, 2),
  (5, 3),
  (5, 4),
  (6, 0),
  (6, 1),
  (6, 2),
  (6, 3),
  (6, 4),
  (6, 5),
  (7, 0),
  (7, 1),
  (7, 2),
  (7, 3),
  (7, 4),
  (7, 5),
  (7, 6),
  (8, 0),
  (8, 1),
  (8, 2),
  (8, 3),
  (8, 4),
  (8, 5),
  (8, 6),
  (8, 7),
  (9, 0),
  (9, 1),
  (9, 2),
  (9, 3),
  (9, 4),
  (9, 5),
  (9, 6),
  (9, 7),
  (9, 8),
  (10, 0),
  (10, 1),
  (10, 2),
  (10, 3),
  (10, 4),
  (10, 5),
  (10, 6),
  (10, 7),
  (10, 8),
  (10, 9),
  (11, 0),
  (11, 1),
  (11, 2),
  (11, 3),
  (11, 4),
  (11, 5),
  (11, 6),
  (11, 7),
  (11, 8),
  (11, 9),
  (11, 10),
  (12, 0),
  (12, 1),
  (12, 2),
  (12, 3),
  (12, 4),
  (12, 5),
  (12, 6),
  (12, 7),
  (12, 8),
  (12, 9),
  (12, 10),
  (12, 11),
  (13, 0),
  (13, 1),
  (13, 2),
  (13, 3),
  (13, 4),
  (13, 5),
  (13, 6),
  (13, 7),
  (13, 8),
  (13, 9),
  (13, 10),
  (13, 11),
  (13, 12),
  (14, 0),
  (14, 1),
  (14, 2),
  (14, 3),
  (14, 4),
  (14, 5),
  (14, 6),
  (14, 7),
  (14, 8),
  (14, 9),
  (14, 10),
  (14, 11),
  (14, 12),
  (14, 13),
  (15, 0),
  (15, 1),
  (15, 2),
  (15, 3),
  (15, 4),
  (15, 5),
  (15, 6),
  (15, 7),
  (15, 8),
  (15, 9),
  (15, 10),
  (15, 11),
  (15, 12),
  (15, 13),
  (15, 14),
  (16, 0),
  (16, 1),
  (16, 2),
  (16, 3),
  (16, 4),
  (16, 5),
  (16, 6),
  (16, 7),
  (16, 8),
  (16, 9),
  (16, 10),
  (16, 11),
  (16, 12),
  (16, 13),
  (16, 14),
  (16, 15),
  (17, 0),
  (17, 1),
  (17, 2),
  (17, 3),
  (17, 4),
  (17, 5),
  (17, 6),
  (17, 7),
  (17, 8),
  (17, 9),
  (17, 10),
  (17, 11),
  (17, 12),
  (17, 13),
  (17, 14),
  (17, 15),
  (17, 16),
  (18, 0),
  (18, 1),
  (18, 2),
  (18, 3),
  (18, 4),
  (18, 5),
  (18, 6),
  (18, 7),
  (18, 8),
  (18, 9),
  (18, 10),
  (18, 11),
  (18, 12),
  (18, 13),
  (18, 14),
  (18, 15),
  (18, 16),
  (18, 17),
  (19, 0),
  (19, 1),
  (19, 2),
  (19, 3),
  (19, 4),
  (19, 5),
  (19, 6),
  (19, 7),
  (19, 8),
  (19, 9),
  (19, 10),
  (19, 11),
  (19, 12),
  (19, 13),
  (19, 14),
  (19, 15),
  (19, 16),
  (19, 17),
  (19, 18)]

def exteriorPair (i : Fin 190) : Fin 20 × Fin 20 := exteriorPairs[i.val]!

/-- The second coordinate is strictly smaller in the source convention. -/
theorem exteriorPair_lt (i : Fin 190) : (exteriorPair i).2 < (exteriorPair i).1 := by
  have h : ∀ i : Fin 190, (exteriorPair i).2 < (exteriorPair i).1 := by decide +kernel
  exact h i

/-- Coordinate formula for the exterior square, over the binary field. -/
def exteriorMatrix (M : Matrix (Fin 20) (Fin 20) (ZMod 2)) :
    Matrix (Fin 190) (Fin 190) (ZMod 2) := fun i j =>
  M (exteriorPair i).1 (exteriorPair j).1 * M (exteriorPair i).2 (exteriorPair j).2 +
  M (exteriorPair i).1 (exteriorPair j).2 * M (exteriorPair i).2 (exteriorPair j).1

/-- The two ambient matrices to which every section identity refers. -/
def ambientGenerator (s : Fin 2) : Matrix (Fin 190) (Fin 190) (ZMod 2) :=
  exteriorMatrix (if s = 0 then Sporadic.LeechRelated.HS.Twenty.aMatrix
    else Sporadic.LeechRelated.HS.Twenty.bMatrix)

def targetGenerator (i : Fin 4) (s : Fin 2) : Mat i :=
  if s = 0 then aMatrix i else bMatrix i

/-- Concatenation in kernel-then-lift order, indexed by the corresponding sum. -/
def sectionRows {r n : ℕ} (N : Matrix (Fin r) (Fin 190) (ZMod 2))
    (U : Matrix (Fin n) (Fin 190) (ZMod 2)) :
    Matrix (Fin r ⊕ Fin n) (Fin 190) (ZMod 2) := Sum.elim N U

/-- Independent marked rows of a literal subquotient of exterior-square(20).
The right inverse proves independence of the entire concatenated row family.
The quotient action and its dual are subsequent mathematical constructions. -/
structure SectionCertificate (i : Fin 4) (r : ℕ) where
  kernelRows : Matrix (Fin r) (Fin 190) (ZMod 2)
  liftRows : Matrix (Fin (binaryDegree i)) (Fin 190) (ZMod 2)
  retract : Matrix (Fin 190) (Fin r ⊕ Fin (binaryDegree i)) (ZMod 2)
  independent : sectionRows kernelRows liftRows * retract = 1
  kernelAction : Fin 2 → Matrix (Fin r) (Fin r) (ZMod 2)
  corrections : Fin 2 → Matrix (Fin (binaryDegree i)) (Fin r) (ZMod 2)
  kernel_invariant : ∀ s, kernelRows * ambientGenerator s = kernelAction s * kernelRows
  lift_action : ∀ s, liftRows * ambientGenerator s =
    corrections s * kernelRows + targetGenerator i s * liftRows

end Representation.HigmanSims.LargeModels.Binary.Small
