module

public import Theory.SpecificGroups.PSL3Three.Generators
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Generator data for the degree-sixteen modules of PSL₃(3)

These are the two numerical generator matrices L33G1-f16r16aB0 from the
ATLAS of Finite Group Representations, together with the corresponding
L33G1-f3r3aB0 generators in the native special linear group. Entries are
binary polynomials in a parameter `t`; the intended specialization satisfies
`t ^ 4 = t + 1`. The matrices act on columns with the usual matrix product.

This file defines certificate data, not a group action or a simplicity proof.
The native quotient map is retained in `generatorA` and `generatorB`.

Source: R. A. Wilson, S. J. Nickerson and J. N. Bray, ATLAS of Finite Group
Representations, L₃(3), representation L33G1-f16r16aB0 (individual contributor
not recorded), downloaded 9 October 2026. Numerical data:
http://atlas.math.rwth-aachen.de/Atlas/lin/L33/mtx/L33G1-f16r16aB0.m1
http://atlas.math.rwth-aachen.de/Atlas/lin/L33/mtx/L33G1-f16r16aB0.m2
and the same directory's L33G1-f3r3aB0.m1 and .m2. The GAP-format copy
L33G1-f16r16aB0.g1 confirms the binary coefficient convention (e.g. code
3 is `t + 1 = t ^ 4`). See GM02, Proposition 4.2, manuscript pp.9–10,
and the characteristic-two decomposition matrix of L₃(3) for the consumer.
-/

public section
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels

/-- ATLAS standard involution, in the actual native matrix group. -/
@[expose] def nativeA : Matrix.PSL3Three.SL :=
  ⟨!![1, 0, 0; 2, 2, 0; 1, 0, 2], by decide⟩

/-- ATLAS standard element of order three. -/
@[expose] def nativeB : Matrix.PSL3Three.SL :=
  ⟨!![0, 1, 0; 0, 0, 1; 1, 0, 0], by decide⟩

@[expose] def generatorA : Matrix.PSL3Three.PSL := Matrix.PSL3Three.project nativeA
@[expose] def generatorB : Matrix.PSL3Three.PSL := Matrix.PSL3Three.project nativeB

/-- Decode the four binary digits as coefficients of `1,t,t²,t³`. -/
@[expose] def coefficient {F : Type*} [CommRing F] (t : F) : Fin 16 → F :=
  ![0, 1, t, t + 1, t ^ 2, t ^ 2 + 1, t ^ 2 + t, t ^ 2 + t + 1,
    t ^ 3, t ^ 3 + 1, t ^ 3 + t, t ^ 3 + t + 1,
    t ^ 3 + t ^ 2, t ^ 3 + t ^ 2 + 1, t ^ 3 + t ^ 2 + t,
    t ^ 3 + t ^ 2 + t + 1]

/-- The first ATLAS generator, with entries encoded by binary polynomials. -/
@[expose] def codesA : Matrix (Fin 16) (Fin 16) (Fin 16) :=
  !![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    9, 15, 10, 12, 6, 6, 10, 8, 12, 8, 6, 11, 1, 11, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
    2, 0, 11, 13, 6, 3, 12, 1, 8, 5, 0, 11, 10, 14, 13, 5;
    13, 8, 14, 10, 5, 9, 14, 4, 3, 5, 12, 2, 11, 14, 3, 13]

/-- The second ATLAS generator, in the same basis and coefficient convention. -/
@[expose] def codesB : Matrix (Fin 16) (Fin 16) (Fin 16) :=
  !![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
    11, 0, 11, 1, 10, 15, 11, 0, 11, 10, 15, 4, 10, 1, 15, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]

@[expose] def matrixA {F : Type*} [CommRing F] (t : F) :
    Matrix (Fin 16) (Fin 16) F := codesA.map (coefficient t)

@[expose] def matrixB {F : Type*} [CommRing F] (t : F) :
    Matrix (Fin 16) (Fin 16) F := codesB.map (coefficient t)

/-- The trace of the product of the two marked generators. -/
@[expose] def traceParameter {F : Type*} [CommRing F] (t : F) : F := t ^ 3 + t + 1

end Representation.PSL3Three.AbsoluteDegrees.SixteenModels
