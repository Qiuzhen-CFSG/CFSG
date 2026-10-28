module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SourceMatrices

/-!
# Coordinates for the marked Sylow normalizer

These are the target coordinates for the involution x and the cubic element u
in Gorenstein, *Finite Groups*, §16.6, pp.482–483. Together with the literal
`sourceY`, they satisfy `UX = XU` and `UY = Y²U`. Indices and multiplication
use column vectors, so the nonzero entry in row i of U has column 4i+2 modulo 7.

This module only specifies matrices. Constructing a simultaneous basis for
the supplied representation is a separate mathematical obligation; the
matrix calculation uses such a basis as an explicit premise.
-/

namespace CFSG.Quasithin.Janko1RelatorPair.SevenNormalization.MatrixCalculation

/-- The marked involution fixes three of the seven nontrivial character lines. -/
@[expose] public def normalX : Matrix (Fin 7) (Fin 7) (ZMod 11) :=
  Matrix.diagonal ![-1, 1, -1, -1, -1, 1, 1]

/-- The cubic complement, with direct conjugation taking y to y². -/
@[expose] public def normalU : Matrix (Fin 7) (Fin 7) (ZMod 11) :=
  !![0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 1;
     0, 0, 0, 1, 0, 0, 0;
     1, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0;
     0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0]

end CFSG.Quasithin.Janko1RelatorPair.SevenNormalization.MatrixCalculation
