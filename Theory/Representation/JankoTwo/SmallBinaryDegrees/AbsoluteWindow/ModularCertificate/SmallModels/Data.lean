module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels.Arithmetic

/-!
# Literal matrices and proposed witnesses for the two small Hall--Janko degrees

The generator matrices are transcribed from the ATLAS originals retained in
`source/`, with their source URLs and SHA-256 sums. Coefficients 0,1,2,3 mean
0,1,t,t+1 where t²=t+1. These are data declarations, not certificates.

The proposed rank-one polynomial has coefficients in increasing degree.
Left-orbit words are reversed from the discovery JSON to act on columns;
right-orbit words and algebra words retain their displayed order. The shorter
trace words use only positive generators. Every claimed product, orbit, inverse,
and trace identity must be proved by the separate certificate modules.

Source: ATLAS J2G1-f4r6aB0 and J2G1-f4r14aB0. See source/README.md.
-/

@[expose] public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels
open Arithmetic


namespace SixData

def A : CodeMatrix 6 :=
  !![3, 3, 0, 0, 0, 0;
    1, 3, 0, 0, 0, 0;
    1, 1, 3, 3, 0, 0;
    2, 1, 1, 3, 0, 0;
    0, 3, 3, 3, 0, 2;
    3, 1, 3, 0, 3, 0]

def B : CodeMatrix 6 :=
  !![2, 1, 3, 1, 3, 3;
    2, 1, 2, 1, 1, 2;
    2, 2, 3, 3, 1, 0;
    0, 0, 0, 0, 1, 1;
    3, 1, 3, 3, 2, 3;
    3, 1, 3, 2, 3, 2]

def P : CodeMatrix 6 :=
  !![2, 3, 2, 1, 2, 1;
    3, 0, 0, 2, 0, 2;
    0, 2, 0, 1, 3, 0;
    1, 3, 1, 0, 0, 0;
    1, 1, 3, 2, 1, 2;
    0, 1, 3, 3, 0, 0]

def Pi : CodeMatrix 6 :=
  !![1, 3, 3, 1, 0, 1;
    2, 2, 0, 1, 3, 0;
    0, 2, 3, 3, 2, 1;
    3, 1, 3, 1, 3, 3;
    0, 3, 3, 1, 3, 1;
    1, 3, 2, 3, 3, 1]

def Q : CodeMatrix 6 :=
  !![1, 1, 1, 1, 1, 3;
    3, 0, 3, 3, 2, 2;
    3, 0, 3, 1, 2, 2;
    0, 2, 0, 3, 0, 3;
    2, 3, 3, 0, 1, 3;
    2, 2, 3, 1, 1, 2]

def Qi : CodeMatrix 6 :=
  !![2, 3, 1, 0, 0, 1;
    0, 0, 0, 1, 3, 3;
    0, 3, 0, 1, 0, 1;
    0, 3, 3, 0, 0, 0;
    3, 1, 0, 3, 2, 2;
    0, 3, 3, 1, 2, 2]

def v : CodeVector 6 := ![2, 3, 0, 1, 1, 0]

def lam : CodeVector 6 := ![1, 1, 1, 1, 1, 3]

def leftWords : Fin 6 → List Bool := ![[], [false], [true], [false, true], [true, true], [false, true, true]]

def rightWords : Fin 6 → List Bool := ![[], [false], [true], [false, true], [true, false], [true, false, true]]

def algebraWords : List (List Bool) := [[true, false, true, true, false, true, true, true], [false, false, false, false, false, false, true, true], [true, false, false, false, false, true, false], [false, true, false, false, true, false, true], [true, true, false, true, false, false, true], [false], [false, true, true, false, false, false], [true, true, false, false, true, true]]

def algebraCoefficients : List (Fin 4) := [2, 0, 3, 0, 2, 1, 3, 0]

def polynomial : List (Fin 4) := [1, 0, 0, 1, 1, 1]

def traceWord : List Bool := [true, false, true, true, false, true, false, true, false, true, true, false, true, true, false]

def traceCode : Fin 4 := 2

theorem traceCode_nonbinary : traceCode = 2 ∨ traceCode = 3 := by decide

end SixData


namespace FourteenData

def A : CodeMatrix 14 :=
  !![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
    1, 1, 1, 1, 0, 0, 1, 3, 1, 3, 2, 1, 2, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    1, 1, 3, 3, 3, 3, 1, 1, 1, 1, 0, 0, 0, 1]

def B : CodeMatrix 14 :=
  !![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
    2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 3, 1, 1]

def P : CodeMatrix 14 :=
  !![1, 2, 3, 3, 1, 2, 2, 1, 3, 3, 0, 3, 0, 2;
    2, 1, 1, 2, 3, 3, 3, 3, 0, 2, 3, 1, 3, 0;
    3, 3, 2, 1, 3, 1, 0, 2, 2, 2, 2, 0, 1, 1;
    3, 3, 3, 0, 2, 2, 1, 0, 1, 1, 2, 2, 2, 0;
    3, 0, 2, 0, 1, 3, 2, 3, 2, 0, 1, 0, 1, 3;
    0, 3, 1, 2, 2, 0, 0, 0, 1, 3, 0, 3, 2, 0;
    2, 0, 3, 3, 2, 3, 1, 0, 2, 3, 1, 2, 1, 1;
    1, 2, 0, 0, 1, 0, 0, 3, 2, 0, 2, 3, 2, 1;
    0, 2, 2, 1, 3, 3, 3, 2, 1, 3, 2, 0, 2, 2;
    2, 1, 1, 0, 0, 0, 0, 3, 2, 0, 1, 3, 2, 0;
    0, 0, 0, 3, 2, 1, 2, 2, 2, 1, 0, 0, 2, 3;
    2, 1, 3, 2, 1, 0, 2, 2, 0, 2, 0, 3, 3, 2;
    0, 0, 2, 2, 0, 1, 3, 0, 2, 1, 1, 2, 2, 1;
    2, 2, 1, 0, 2, 0, 1, 0, 1, 1, 1, 3, 1, 0]

def Pi : CodeMatrix 14 :=
  !![1, 0, 3, 2, 2, 1, 3, 1, 2, 0, 1, 2, 1, 3;
    1, 0, 2, 3, 3, 0, 3, 2, 2, 3, 2, 2, 2, 3;
    1, 1, 3, 0, 0, 3, 1, 3, 1, 0, 2, 0, 0, 0;
    1, 0, 0, 3, 0, 0, 0, 2, 0, 1, 0, 2, 3, 0;
    0, 3, 0, 0, 1, 2, 0, 2, 3, 3, 1, 3, 2, 0;
    1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 0, 2;
    1, 2, 1, 0, 1, 1, 1, 1, 3, 3, 3, 0, 3, 0;
    2, 1, 1, 2, 1, 1, 0, 3, 0, 0, 2, 0, 3, 1;
    1, 0, 1, 1, 3, 2, 1, 0, 3, 1, 2, 0, 0, 2;
    3, 0, 1, 3, 2, 2, 0, 0, 0, 2, 2, 1, 2, 1;
    2, 2, 1, 3, 0, 3, 3, 3, 3, 1, 2, 1, 0, 1;
    2, 0, 1, 3, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1;
    1, 0, 2, 1, 3, 3, 0, 2, 2, 0, 3, 2, 2, 0;
    0, 3, 3, 1, 2, 0, 3, 0, 0, 3, 0, 0, 0, 3]

def Q : CodeMatrix 14 :=
  !![0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0;
    1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0;
    1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0;
    0, 0, 1, 1, 0, 0, 1, 3, 0, 3, 2, 1, 3, 0;
    0, 2, 1, 2, 1, 2, 1, 0, 3, 1, 3, 0, 0, 3;
    1, 3, 0, 3, 0, 3, 0, 2, 2, 3, 0, 0, 3, 3;
    1, 1, 1, 0, 0, 1, 1, 2, 1, 2, 3, 0, 3, 0;
    1, 1, 0, 1, 1, 0, 1, 2, 1, 2, 3, 0, 3, 0;
    1, 3, 1, 3, 0, 3, 0, 1, 2, 0, 2, 1, 0, 3;
    0, 3, 0, 3, 1, 3, 1, 0, 2, 0, 2, 1, 0, 3;
    0, 3, 0, 2, 0, 3, 1, 2, 2, 3, 1, 0, 3, 3;
    0, 3, 0, 2, 1, 2, 1, 0, 2, 1, 3, 0, 1, 3;
    1, 3, 0, 3, 1, 2, 0, 3, 3, 2, 1, 0, 3, 2;
    3, 2, 0, 0, 1, 2, 2, 1, 3, 1, 0, 2, 2, 1]

def Qi : CodeMatrix 14 :=
  !![0, 3, 3, 3, 1, 2, 3, 0, 1, 1, 1, 1, 1, 0;
    2, 1, 2, 2, 3, 0, 2, 1, 1, 1, 0, 0, 1, 0;
    3, 3, 0, 1, 2, 1, 2, 1, 3, 0, 1, 0, 1, 1;
    0, 0, 0, 1, 1, 2, 3, 0, 3, 0, 0, 1, 1, 1;
    0, 0, 0, 1, 0, 3, 2, 0, 3, 0, 0, 1, 1, 1;
    3, 3, 0, 1, 3, 0, 2, 0, 3, 0, 1, 0, 1, 1;
    0, 0, 0, 0, 1, 3, 3, 0, 2, 0, 0, 1, 1, 1;
    3, 0, 3, 3, 2, 3, 0, 1, 2, 0, 0, 1, 0, 1;
    3, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 0, 1, 1;
    3, 1, 3, 3, 2, 3, 1, 0, 3, 1, 0, 1, 0, 1;
    0, 3, 3, 2, 1, 2, 3, 0, 0, 1, 0, 1, 1, 0;
    2, 1, 3, 3, 2, 3, 1, 1, 2, 1, 1, 1, 0, 1;
    2, 0, 3, 2, 3, 0, 2, 1, 1, 0, 0, 1, 1, 0;
    0, 3, 2, 3, 1, 1, 0, 0, 2, 1, 0, 0, 1, 1]

def v : CodeVector 14 := ![1, 2, 3, 3, 3, 0, 2, 1, 0, 2, 0, 2, 0, 2]

def lam : CodeVector 14 := ![0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0]

def leftWords : Fin 14 → List Bool := ![[], [false], [true], [true, false], [false, true], [true, true], [false, true, false], [true, true, false], [true, false, true], [false, true, true], [true, false, true, false], [false, true, true, false], [false, true, false, true], [true, false, true, true]]

def rightWords : Fin 14 → List Bool := ![[], [false], [true], [true, false], [true, false, true], [true, false, true, false], [true, false, true, false, true], [true, false, true, false, true, false], [true, false, true, false, true, true], [true, false, true, false, true, false, true], [true, false, true, false, true, false, true, true], [true, false, true, false, true, false, true, true, false], [true, false, true, false, true, false, true, true, false, true], [true, false, true, false, true, false, true, true, false, true, true]]

def algebraWords : List (List Bool) := [[false, true, true, false, true, false, false, true], [true, false, true, true, true], [false, true, true, false, true, true], [true, false, false, false, true, true], [true, true, true, false, true], [true, false, false, false, true, false, false], [false, true, false, true, true, false, true], [true]]

def algebraCoefficients : List (Fin 4) := [0, 3, 3, 0, 0, 2, 1, 0]

def polynomial : List (Fin 4) := [3, 1, 3, 2, 0, 2, 3, 1, 2, 2, 0, 3, 1, 1]

def traceWord : List Bool := [false, true, false, true, true, false, true, false, true, true, false, true, true, false, true]

def traceCode : Fin 4 := 3

theorem traceCode_nonbinary : traceCode = 2 ∨ traceCode = 3 := by decide

end FourteenData


end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels
