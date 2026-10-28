module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Basic

/-!
# Relator words in Janko's original matrices

The two matrices displayed by Janko (1965), p.657, and Gorenstein,
*Finite Groups*, §16.6, equation (6.1), pp.482–483, differ from the
ATLAS standard generators used to define `Janko1.Model`. We give two
explicit words in those original matrices satisfying all five ATLAS
relators. The first word is nonidentity.

The calculation is split into 45 kernel-checked binary matrix products.
These are identities in a matrix ring, and do not assert that an arbitrary
group with the source centralizers has such a representation. The owning
`RelatorPair` module transfers them only through an explicitly supplied
injective representation.

Sources: Z. Janko, *A new finite simple group with abelian 2-Sylow
subgroups*, PNAS 53 (1965), 657–658, DOI 10.1073/pnas.53.3.657;
Gorenstein, *Finite Groups*, §16.6; ATLAS presentation `J1G1-P1`.
-/

namespace CFSG.Quasithin.Janko1RelatorPair

private abbrev Mat := Matrix (Fin 7) (Fin 7) (ZMod 11)

/-- Janko's cyclic permutation matrix, transcribed without transposition. -/
@[expose] public def sourceY : Matrix (Fin 7) (Fin 7) (ZMod 11) :=
  !![0, 1, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 1;
     1, 0, 0, 0, 0, 0, 0]

/-- Janko's second matrix, with entries written as residues modulo eleven. -/
@[expose] public def sourceV : Matrix (Fin 7) (Fin 7) (ZMod 11) :=
  !![8, 2, 10, 10, 8, 10, 8;
     9, 1, 1, 3, 1, 3, 3;
     10, 10, 8, 10, 8, 8, 2;
     10, 8, 10, 8, 8, 2, 10;
     8, 10, 8, 8, 2, 10, 10;
     1, 3, 3, 9, 1, 1, 3;
     3, 3, 9, 1, 1, 3, 1]

private def m01 : Mat :=
  !![0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 1;
     1, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0]

private def m02 : Mat :=
  !![0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 1;
     1, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0]

private def m03 : Mat :=
  !![0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 1;
     1, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0]

private def m04 : Mat :=
  !![6, 2, 10, 10, 7, 3, 0;
     9, 4, 8, 0, 3, 8, 8;
     10, 3, 6, 10, 7, 0, 2;
     10, 0, 10, 6, 7, 2, 3;
     7, 8, 7, 7, 6, 8, 8;
     8, 8, 0, 9, 3, 4, 8;
     0, 8, 9, 8, 3, 8, 4]

private def m05 : Mat :=
  !![6, 9, 10, 10, 7, 8, 0;
     2, 4, 3, 0, 8, 8, 8;
     10, 8, 6, 10, 7, 0, 9;
     10, 0, 10, 6, 7, 9, 8;
     7, 3, 7, 7, 6, 3, 3;
     3, 8, 0, 2, 8, 4, 8;
     0, 8, 2, 3, 8, 8, 4]

private def m06 : Mat :=
  !![8, 9, 10, 10, 8, 1, 3;
     2, 1, 10, 8, 10, 3, 3;
     10, 1, 8, 10, 8, 3, 9;
     10, 3, 10, 8, 8, 9, 1;
     8, 1, 8, 8, 2, 1, 1;
     10, 3, 8, 2, 10, 1, 3;
     8, 3, 2, 10, 10, 3, 1]

private def m07 : Mat :=
  !![0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 1;
     1, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0]

private def m08 : Mat :=
  !![8, 1, 8, 8, 2, 1, 1;
     10, 3, 8, 2, 10, 1, 3;
     8, 3, 2, 10, 10, 3, 1;
     8, 9, 10, 10, 8, 1, 3;
     2, 1, 10, 8, 10, 3, 3;
     10, 1, 8, 10, 8, 3, 9;
     10, 3, 10, 8, 8, 9, 1]

private def m09 : Mat :=
  !![8, 8, 2, 1, 1, 8, 1;
     8, 2, 10, 1, 3, 10, 3;
     2, 10, 10, 3, 1, 8, 3;
     10, 10, 8, 1, 3, 8, 9;
     10, 8, 10, 3, 3, 2, 1;
     8, 10, 8, 3, 9, 10, 1;
     10, 8, 8, 9, 1, 10, 3]

private def m10 : Mat :=
  !![1, 2, 6, 6, 2, 6, 4;
     2, 6, 5, 2, 9, 9, 1;
     6, 5, 4, 10, 9, 2, 6;
     6, 2, 10, 10, 1, 9, 3;
     2, 9, 9, 1, 3, 8, 5;
     6, 9, 2, 9, 8, 10, 8;
     4, 1, 6, 3, 5, 8, 9]

private def m11 : Mat :=
  !![10, 0, 10, 6, 7, 2, 3;
     7, 8, 7, 7, 6, 8, 8;
     8, 8, 0, 9, 3, 4, 8;
     0, 8, 9, 8, 3, 8, 4;
     6, 2, 10, 10, 7, 3, 0;
     9, 4, 8, 0, 3, 8, 8;
     10, 3, 6, 10, 7, 0, 2]

private def m12 : Mat :=
  !![2, 3, 10, 0, 10, 6, 7;
     8, 8, 7, 8, 7, 7, 6;
     4, 8, 8, 8, 0, 9, 3;
     8, 4, 0, 8, 9, 8, 3;
     3, 0, 6, 2, 10, 10, 7;
     8, 8, 9, 4, 8, 0, 3;
     0, 2, 10, 3, 6, 10, 7]

private def m13 : Mat :=
  !![4, 10, 6, 3, 5, 3, 2;
     1, 9, 6, 6, 2, 5, 7;
     9, 6, 6, 9, 2, 9, 1;
     5, 5, 7, 1, 2, 2, 6;
     6, 9, 10, 10, 1, 2, 8;
     9, 9, 2, 10, 8, 8, 5;
     6, 2, 2, 9, 8, 1, 3]

private def m14 : Mat :=
  !![10, 4, 3, 7, 4, 4, 9;
     9, 3, 6, 8, 2, 0, 4;
     9, 7, 9, 3, 4, 8, 8;
     5, 3, 2, 5, 7, 10, 3;
     3, 8, 8, 10, 4, 1, 0;
     10, 2, 10, 6, 1, 8, 9;
     10, 2, 2, 9, 8, 3, 6]

private def m15 : Mat :=
  !![10, 9, 9, 5, 3, 10, 10;
     4, 3, 7, 3, 8, 2, 2;
     3, 6, 9, 2, 8, 10, 2;
     7, 8, 3, 5, 10, 6, 9;
     4, 2, 4, 7, 4, 1, 8;
     4, 0, 8, 10, 1, 8, 3;
     9, 4, 8, 3, 0, 9, 6]

private def m16 : Mat :=
  !![9, 7, 0, 9, 10, 9, 7;
     3, 5, 2, 9, 8, 9, 10;
     1, 9, 10, 3, 8, 1, 3;
     0, 8, 2, 9, 10, 0, 7;
     7, 8, 4, 10, 8, 7, 0;
     1, 5, 2, 3, 10, 0, 7;
     6, 1, 7, 6, 9, 3, 3]

private def m17 : Mat :=
  !![3, 5, 7, 9, 7, 4, 5;
     4, 2, 3, 7, 2, 6, 2;
     0, 7, 3, 6, 7, 0, 10;
     6, 8, 0, 4, 5, 0, 5;
     0, 7, 1, 8, 4, 8, 7;
     6, 7, 4, 9, 8, 4, 6;
     5, 6, 4, 2, 5, 10, 2]

private def m18 : Mat :=
  !![0, 9, 4, 0, 5, 0, 0;
     0, 4, 5, 0, 2, 0, 0;
     1, 0, 0, 3, 0, 2, 8;
     0, 5, 2, 0, 7, 0, 0;
     1, 0, 0, 2, 0, 3, 8;
     10, 0, 0, 8, 0, 8, 2;
     3, 0, 0, 1, 0, 1, 10]

private def m19 : Mat :=
  !![0, 0, 1, 0, 1, 10, 3;
     9, 4, 0, 5, 0, 0, 0;
     4, 5, 0, 2, 0, 0, 0;
     0, 0, 3, 0, 2, 8, 1;
     5, 2, 0, 7, 0, 0, 0;
     0, 0, 2, 0, 3, 8, 1;
     0, 0, 8, 0, 8, 2, 10]

private def m20 : Mat :=
  !![3, 4, 0, 6, 0, 6, 5;
     5, 2, 7, 8, 7, 7, 6;
     7, 3, 3, 0, 1, 4, 4;
     9, 7, 6, 4, 8, 9, 2;
     7, 2, 7, 5, 4, 8, 5;
     4, 6, 0, 0, 8, 4, 10;
     5, 2, 10, 5, 7, 6, 2]

private def m21 : Mat :=
  !![9, 3, 1, 0, 7, 1, 6;
     7, 5, 9, 8, 8, 5, 1;
     0, 2, 10, 2, 4, 2, 7;
     9, 9, 3, 9, 10, 3, 6;
     10, 8, 8, 10, 8, 10, 9;
     9, 9, 1, 0, 7, 0, 3;
     7, 10, 3, 7, 0, 7, 3]

private def m22 : Mat :=
  !![3, 3, 10, 6, 7, 6, 2;
     2, 7, 5, 4, 4, 8, 5;
     10, 9, 4, 4, 3, 1, 3;
     9, 8, 6, 3, 10, 7, 6;
     0, 6, 9, 5, 3, 5, 10;
     1, 2, 3, 9, 1, 9, 0;
     2, 0, 3, 4, 2, 8, 5]

private def m23 : Mat :=
  !![8, 1, 6, 2, 9, 3, 9;
     8, 8, 2, 8, 1, 1, 1;
     10, 4, 3, 2, 0, 0, 9;
     8, 0, 3, 1, 7, 7, 7;
     10, 4, 6, 8, 0, 1, 9;
     9, 8, 10, 5, 3, 6, 4;
     10, 4, 4, 2, 9, 9, 0]

private def m24 : Mat :=
  !![3, 4, 7, 0, 1, 4, 3;
     10, 8, 4, 8, 5, 5, 2;
     6, 2, 9, 1, 2, 8, 3;
     8, 0, 2, 7, 9, 0, 10;
     5, 0, 2, 7, 3, 1, 10;
     4, 2, 0, 4, 2, 2, 1;
     9, 1, 10, 3, 3, 1, 8]

private def m25 : Mat :=
  !![4, 1, 6, 9, 4, 10, 9;
     0, 4, 2, 4, 0, 4, 2;
     9, 10, 9, 10, 4, 5, 7;
     0, 4, 4, 9, 2, 7, 0;
     2, 7, 4, 4, 0, 9, 0;
     7, 4, 10, 1, 4, 10, 4;
     4, 10, 1, 6, 2, 9, 4]

private def m26 : Mat :=
  !![4, 7, 10, 6, 5, 6, 5;
     6, 7, 5, 7, 6, 1, 6;
     8, 8, 6, 3, 5, 6, 3;
     0, 8, 7, 6, 7, 5, 3;
     8, 5, 5, 0, 4, 4, 3;
     4, 6, 5, 4, 10, 5, 6;
     6, 0, 7, 8, 5, 4, 8]

private def m27 : Mat :=
  !![1, 2, 3, 5, 6, 4, 3;
     7, 3, 9, 7, 1, 7, 4;
     1, 3, 0, 1, 3, 4, 3;
     0, 5, 7, 3, 9, 2, 8;
     3, 10, 9, 6, 1, 10, 2;
     8, 2, 3, 8, 9, 4, 4;
     8, 2, 6, 9, 1, 3, 2]

private def m28 : Mat :=
  !![1, 7, 1, 0, 3, 8, 8;
     2, 3, 3, 5, 10, 2, 2;
     3, 9, 0, 7, 9, 3, 6;
     5, 7, 1, 3, 6, 8, 9;
     6, 1, 3, 9, 1, 9, 1;
     4, 7, 4, 2, 10, 4, 3;
     3, 4, 3, 8, 2, 4, 2]

private def m29 : Mat :=
  !![4, 6, 8, 0, 8, 4, 6;
     7, 7, 8, 8, 5, 6, 0;
     10, 5, 6, 7, 5, 5, 7;
     6, 7, 3, 6, 0, 4, 8;
     5, 6, 5, 7, 4, 10, 5;
     6, 1, 6, 5, 4, 5, 4;
     5, 6, 3, 3, 3, 6, 8]

private def m30 : Mat :=
  !![7, 3, 0, 5, 2, 1, 10;
     8, 3, 8, 9, 7, 8, 0;
     4, 0, 2, 10, 8, 6, 1;
     7, 2, 8, 1, 0, 1, 6;
     5, 3, 8, 7, 3, 7, 4;
     3, 4, 3, 3, 8, 0, 9;
     3, 8, 7, 0, 8, 2, 8]

private def m31 : Mat :=
  !![7, 10, 4, 7, 7, 3, 2;
     8, 2, 7, 7, 8, 2, 8;
     1, 8, 7, 8, 1, 3, 0;
     9, 10, 8, 9, 8, 2, 5;
     3, 2, 9, 3, 0, 5, 4;
     5, 5, 7, 8, 1, 2, 8;
     6, 10, 1, 9, 3, 10, 2]

private def m32 : Mat :=
  !![8, 9, 10, 8, 6, 2, 2;
     10, 0, 7, 0, 3, 2, 2;
     1, 0, 4, 1, 5, 9, 3;
     1, 2, 4, 9, 7, 0, 9;
     8, 1, 3, 10, 2, 10, 8;
     3, 4, 0, 7, 8, 7, 10;
     9, 3, 3, 5, 10, 7, 5]

private def m33 : Mat :=
  !![3, 9, 7, 7, 9, 9, 6;
     0, 5, 7, 6, 5, 8, 0;
     7, 6, 2, 6, 8, 7, 7;
     4, 5, 2, 3, 7, 5, 7;
     3, 1, 6, 0, 4, 4, 0;
     1, 4, 8, 0, 7, 4, 8;
     7, 2, 9, 5, 5, 6, 1]

private def m34 : Mat :=
  !![10, 8, 6, 3, 9, 5, 7;
     8, 2, 1, 2, 1, 6, 1;
     7, 9, 10, 7, 3, 4, 7;
     3, 8, 9, 4, 9, 8, 7;
     1, 0, 8, 8, 3, 10, 4;
     8, 6, 10, 9, 2, 2, 3;
     0, 7, 2, 3, 5, 8, 2]

private def m35 : Mat :=
  !![2, 1, 6, 10, 3, 2, 10;
     2, 9, 9, 3, 8, 5, 10;
     7, 3, 4, 4, 4, 9, 1;
     3, 5, 8, 9, 0, 7, 9;
     4, 9, 8, 4, 8, 8, 2;
     8, 2, 6, 7, 10, 3, 6;
     3, 8, 1, 4, 1, 0, 8]

private def m36 : Mat :=
  !![4, 5, 1, 5, 9, 5, 9;
     2, 5, 1, 2, 8, 2, 8;
     6, 2, 8, 7, 5, 1, 3;
     6, 1, 2, 2, 2, 5, 9;
     1, 3, 10, 6, 10, 9, 9;
     9, 8, 9, 6, 3, 2, 10;
     6, 7, 5, 10, 2, 2, 5]

private def m37 : Mat :=
  !![0, 10, 3, 0, 2, 7, 2;
     10, 10, 6, 0, 2, 7, 8;
     9, 1, 7, 2, 0, 4, 9;
     1, 3, 9, 10, 1, 8, 3;
     4, 8, 3, 7, 4, 0, 1;
     6, 2, 1, 8, 4, 8, 6;
     8, 8, 6, 9, 2, 10, 2]

private def m38 : Mat :=
  !![4, 4, 7, 0, 2, 0, 2;
     1, 1, 5, 9, 2, 4, 4;
     4, 9, 4, 0, 4, 9, 0;
     7, 4, 2, 9, 4, 0, 0;
     4, 1, 1, 4, 10, 7, 4;
     1, 5, 9, 4, 10, 2, 7;
     10, 2, 10, 4, 5, 4, 2]

private def m39 : Mat :=
  !![0, 9, 9, 9, 10, 3, 10;
     8, 2, 4, 1, 1, 4, 8;
     6, 0, 4, 8, 9, 3, 9;
     5, 3, 3, 7, 2, 6, 1;
     9, 8, 6, 6, 8, 10, 4;
     1, 5, 5, 5, 0, 9, 8;
     6, 4, 4, 8, 9, 5, 7]

private def m40 : Mat :=
  !![9, 6, 2, 1, 5, 7, 6;
     6, 5, 9, 7, 3, 4, 4;
     2, 9, 4, 6, 7, 3, 2;
     1, 7, 6, 0, 0, 8, 4;
     5, 3, 7, 0, 5, 0, 5;
     7, 4, 3, 8, 0, 1, 4;
     6, 4, 2, 4, 5, 4, 8]

private theorem products :
    sourceY * sourceY = m01 ∧
    m01 * sourceY = m02 ∧
    m02 * sourceY = m03 ∧
    sourceV * sourceV = m04 ∧
    m04 * sourceV = m05 ∧
    m05 * sourceV = m06 ∧
    m03 * sourceY = m07 ∧
    m03 * m06 = m08 ∧
    m08 * m07 = m09 ∧
    m09 * m04 = m10 ∧
    m02 * m04 = m11 ∧
    m11 * m01 = m12 ∧
    m12 * m04 = m13 ∧
    m13 * m13 = m14 ∧
    m10 * m10 = 1 ∧
    m14 * m14 = m15 ∧
    m15 * m14 = 1 ∧
    m10 * m14 = m16 ∧
    m16 * m16 = m17 ∧
    m17 * m16 = m18 ∧
    m18 * m16 = m19 ∧
    m19 * m16 = m20 ∧
    m20 * m16 = m21 ∧
    m21 * m16 = 1 ∧
    m16 * m10 = m22 ∧
    m22 * m15 = m23 ∧
    m23 * m23 = m24 ∧
    m24 * m23 = m25 ∧
    m16 * m25 = m26 ∧
    m26 * m26 = m27 ∧
    m27 * m26 = m28 ∧
    m28 * m26 = m29 ∧
    m29 * m26 = 1 ∧
    m25 * m23 = m30 ∧
    m30 * m23 = m31 ∧
    m31 * m23 = m32 ∧
    m10 * m15 = m33 ∧
    m33 * m33 = m34 ∧
    m16 * m32 = m35 ∧
    m35 * m10 = m36 ∧
    m36 * m14 = m37 ∧
    m37 * m10 = m38 ∧
    m38 * m14 = m39 ∧
    m39 * m34 = m40 ∧
    m40 * m40 = 1 := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ ⟩ <;> decide +kernel

private theorem evalA : sourceY ^ 4 * sourceV ^ 4 * sourceY ^ 5 * sourceV ^ 2 = m10 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := products
  simp only [pow_succ, pow_zero, one_mul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]

private theorem evalB : (sourceY ^ 3 * sourceV ^ 2 * sourceY ^ 2 * sourceV ^ 2) ^ 2 = m14 := by
  obtain ⟨h0, h1, _, h3, _, _, _, _, _, _, h10, h11, h12, h13, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := products
  simp only [pow_succ, pow_zero, one_mul, h0, h1, h3, h10, h11, h12, h13]

private theorem rel2 : m10 ^ 2 = 1 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, h14, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := products
  simp only [pow_succ, pow_zero, one_mul, h14]

private theorem rel3 : m14 ^ 3 = 1 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h15, h16, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := products
  simp only [pow_succ, pow_zero, one_mul, h15, h16]

private theorem rel7 : (m10 * m14) ^ 7 = 1 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h17, h18, h19, h20, h21, h22, h23, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := products
  simp only [pow_succ, pow_zero, one_mul, h17, h18, h19, h20, h21, h22, h23]

private theorem rel4 : (m10 * m14 * (m10 * m14 * m10 * m14 ^ 2) ^ 3) ^ 5 = 1 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h15, _, h17, _, _, _, _, _, _, h24, h25, h26, h27, h28, h29, h30, h31, h32, _, _, _, _, _, _, _, _, _, _, _, _⟩ := products
  simp only [pow_succ, pow_zero, one_mul, h15, h17, h24, h25, h26, h27, h28, h29, h30, h31, h32]

private theorem rel5 : (m10 * m14 * (m10 * m14 * m10 * m14 ^ 2) ^ 6 * m10 * m14 * m10 * m14 * (m10 * m14 ^ 2) ^ 2) ^ 2 = 1 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h15, _, h17, _, _, _, _, _, _, h24, h25, h26, h27, _, _, _, _, _, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44⟩ := products
  simp only [pow_succ, pow_zero, one_mul, h15, h17, h24, h25, h26, h27, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44]

private theorem ne_one : m10 ≠ 1 := by decide +kernel

/-- The first explicit word in the original source generators. -/
@[expose] public def firstWord {M : Type*} [Monoid M] (y v : M) : M :=
  y ^ 4 * v ^ 4 * y ^ 5 * v ^ 2

/-- The second explicit word in the original source generators. -/
@[expose] public def secondWord {M : Type*} [Monoid M] (y v : M) : M :=
  (y ^ 3 * v ^ 2 * y ^ 2 * v ^ 2) ^ 2

/-- The first word in the original matrices is nonidentity. -/
public theorem source_firstWord_ne_one : firstWord sourceY sourceV ≠ 1 := by
  rw [firstWord, evalA]
  exact ne_one

/-- All five matrix relators, with the second generator's inverse replaced
by its square. This replacement is justified by the second relation. -/
public theorem source_matrix_relations :
    let a := firstWord sourceY sourceV
    let b := secondWord sourceY sourceV
    a ^ 2 = 1 ∧ b ^ 3 = 1 ∧ (a * b) ^ 7 = 1 ∧
      (a * b * (a * b * a * b ^ 2) ^ 3) ^ 5 = 1 ∧
      (a * b * (a * b * a * b ^ 2) ^ 6 * a * b * a * b * (a * b ^ 2) ^ 2) ^ 2 = 1 := by
  dsimp only
  rw [firstWord, secondWord, evalA, evalB]
  exact ⟨rel2, rel3, rel7, rel4, rel5⟩

end CFSG.Quasithin.Janko1RelatorPair
