module

public import Theory.AtlasPort.Janko2.Algebra.GoldenFourFinite
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Tactic
/-!
# A checked order-seventeen matrix word

The four determinant-one matrices below use the encoding 0, 1, ω, 1+ω
in GF(4), with ω²=1+ω. The six-dimensional blocks use the literal octonion
coordinate order: the natural coordinates are (0,3,4), and the dual
coordinates are (5,2,1). Multiplication certificates identify the word
(bad · graph · block(A₀)) ⋯ (bad · graph · block(A₃)). Its square Q is
nonidentity and Q¹⁷=1, as checked by four squarings and one multiplication.

Each displayed multiplication is checked in the Lean kernel. The matrices
were discovered by the parent's `Scratch/LeechLocalA5/search_seventeen.py`;
no external computation is trusted. `Transport` connects this certificate
to the actual quotient action in the diagonal selection for Aschbacher,
*Sporadic Groups* (1994), Lemma 49.5, p.284.
-/

@[expose] public section

open Matrix Atlas.Algebra
open scoped MatrixGroups
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.DiagonalSelection.Certificate
abbrev K := GoldenFour
abbrev w : K := goldenFourTau
local instance : CharP K 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2
def blockMatrix {R : Type*} [CommRing R] (A : Matrix (Fin 3) (Fin 3) R) :
    Matrix (Fin 6) (Fin 6) R :=
  let c := A.adjugate.transpose
  !![A 0 0,0,0,A 0 1,A 0 2,0;
     0,c 2 2,c 2 1,0,0,c 2 0;
     0,c 1 2,c 1 1,0,0,c 1 0;
     A 1 0,0,0,A 1 1,A 1 2,0;
     A 2 0,0,0,A 2 1,A 2 2,0;
     0,c 0 2,c 0 1,0,0,c 0 0]

def bad : Matrix (Fin 6) (Fin 6) K :=
  !![1,0,0,0,0,1;
    0,1,0,0,0,0;
    0,0,1,0,0,0;
    0,1,0,1,0,0;
    0,0,1,0,1,0;
    0,0,0,0,0,1]

def graphMatrix : Matrix (Fin 6) (Fin 6) K :=
  !![0,0,0,0,0,1;
    0,0,0,1,0,0;
    0,0,0,0,1,0;
    0,1,0,0,0,0;
    0,0,1,0,0,0;
    1,0,0,0,0,0]

def A0 : SL(3,K) := ⟨!![0,1+w,w;
    w,1+w,1;
    1+w,w,1], by decide +kernel⟩

def B0 : Matrix (Fin 6) (Fin 6) K :=
  !![0,0,0,1+w,w,0;
    0,1,1+w,0,0,w;
    0,w,1,0,0,0;
    w,0,0,1+w,1,0;
    1+w,0,0,w,1,0;
    0,1,1,0,0,1]

def A1 : SL(3,K) := ⟨!![0,1,1;
    1,1,1;
    1,0,1], by decide +kernel⟩

def B1 : Matrix (Fin 6) (Fin 6) K :=
  !![0,0,0,1,1,0;
    0,1,1,0,0,0;
    0,1,1,0,0,1;
    1,0,0,1,1,0;
    1,0,0,0,1,0;
    0,1,0,0,0,1]

def A2 : SL(3,K) := ⟨!![1,0,1+w;
    w,1,w;
    1+w,0,1+w], by decide +kernel⟩

def B2 : Matrix (Fin 6) (Fin 6) K :=
  !![1,0,0,0,1+w,0;
    0,1,1+w,0,0,1+w;
    0,0,1,0,0,0;
    w,0,0,1,w,0;
    1+w,0,0,0,1+w,0;
    0,1+w,0,0,0,1+w]

def A3 : SL(3,K) := ⟨!![1,1,0;
    0,1,0;
    0,1,1], by decide +kernel⟩

def B3 : Matrix (Fin 6) (Fin 6) K :=
  !![1,0,0,1,0,0;
    0,1,0,0,0,0;
    0,1,1,0,0,1;
    0,0,0,1,0,0;
    0,0,0,1,1,0;
    0,0,0,0,0,1]

def bg : Matrix (Fin 6) (Fin 6) K :=
  !![1,0,0,0,0,1;
    0,0,0,1,0,0;
    0,0,0,0,1,0;
    0,1,0,1,0,0;
    0,0,1,0,1,0;
    1,0,0,0,0,0]

theorem bad_graph : bad * graphMatrix = bg := by decide +kernel

def S0 : Matrix (Fin 6) (Fin 6) K :=
  !![0,1,1,1+w,w,1;
    w,0,0,1+w,1,0;
    1+w,0,0,w,1,0;
    w,1,1+w,1+w,1,w;
    1+w,w,1,w,1,0;
    0,0,0,1+w,w,0]

theorem step0 : bg * B0 = S0 := by decide +kernel

def S1 : Matrix (Fin 6) (Fin 6) K :=
  !![0,1,0,1,1,1;
    1,0,0,1,1,0;
    1,0,0,0,1,0;
    1,1,1,1,1,0;
    1,1,1,0,1,1;
    0,0,0,1,1,0]

theorem step1 : bg * B1 = S1 := by decide +kernel

def S2 : Matrix (Fin 6) (Fin 6) K :=
  !![1,1+w,0,0,1+w,1+w;
    w,0,0,1,w,0;
    1+w,0,0,0,1+w,0;
    w,1,1+w,1,w,1+w;
    1+w,0,1,0,1+w,0;
    1,0,0,0,1+w,0]

theorem step2 : bg * B2 = S2 := by decide +kernel

def S3 : Matrix (Fin 6) (Fin 6) K :=
  !![1,0,0,1,0,1;
    0,0,0,1,0,0;
    0,0,0,1,1,0;
    0,1,0,1,0,0;
    0,1,1,1,1,1;
    1,0,0,1,0,0]

theorem step3 : bg * B3 = S3 := by decide +kernel

def P1 : Matrix (Fin 6) (Fin 6) K :=
  !![1,1,1,1+w,0,w;
    w,0,w,1,0,1+w;
    1+w,0,1+w,1,0,w;
    0,0,w,w,0,1+w;
    0,0,1+w,1+w,1+w,w;
    1,1,1,1+w,1,w]

theorem product1 : S0 * S1 = P1 := by decide +kernel

def P2 : Matrix (Fin 6) (Fin 6) K :=
  !![1+w,0,w,w,w,1;
    w,0,1+w,1,0,w;
    1,1+w,1+w,1,1+w,1;
    1,w,1,w,0,1;
    1+w,1+w,1,1+w,0,w;
    0,0,1+w,w,1,1]

theorem product2 : P1 * S2 = P2 := by decide +kernel

def P3 : Matrix (Fin 6) (Fin 6) K :=
  !![w,0,w,0,0,1;
    0,1,0,w,1+w,w;
    0,w,1+w,w,0,w;
    0,w,0,1,1,1;
    1,1+w,0,0,1,1+w;
    1,1+w,1,1,w,1]

theorem product3 : P2 * S3 = P3 := by decide +kernel

def Q : Matrix (Fin 6) (Fin 6) K :=
  !![w,0,1+w,w,w,0;
    1,1,w,w,1,0;
    w,1,0,w,0,w;
    0,0,1,1+w,1+w,0;
    0,w,1,w,w,0;
    1,1,0,1+w,1+w,1+w]

theorem square : P3 * P3 = Q := by decide +kernel

def Q2 : Matrix (Fin 6) (Fin 6) K :=
  !![w,0,1,0,1,1;
    0,1,w,0,0,1+w;
    0,1+w,1,1,w,1;
    w,0,0,1,1+w,w;
    0,0,1+w,1+w,0,w;
    0,1+w,1,1,w,w]

theorem square2 : Q * Q = Q2 := by decide +kernel

def Q4 : Matrix (Fin 6) (Fin 6) K :=
  !![1+w,0,1,1+w,w,1+w;
    0,w,1+w,1,w,0;
    w,1+w,0,0,1+w,0;
    1,1,w,1,w,w;
    1,1+w,1,w,0,1;
    w,1,1+w,1+w,w,1]

theorem square4 : Q2 * Q2 = Q4 := by decide +kernel

def Q8 : Matrix (Fin 6) (Fin 6) K :=
  !![0,w,w,0,w,w;
    w,1,1,0,1+w,0;
    w,1+w,1+w,1+w,w,w;
    0,1,1+w,1,0,1;
    1,1,1+w,1,1,1;
    1+w,1+w,1,1+w,0,1+w]

theorem square8 : Q4 * Q4 = Q8 := by decide +kernel

def Q16 : Matrix (Fin 6) (Fin 6) K :=
  !![1+w,0,0,w,0,0;
    1+w,w,1+w,0,1,w;
    1+w,w,1+w,w,w,w;
    0,1,1,0,w,1+w;
    1,w,0,1,1,0;
    1,0,0,w,1,w]

theorem square16 : Q8 * Q8 = Q16 := by decide +kernel

theorem final_product : Q16 * Q = 1 := by decide +kernel

theorem nonidentity : Q ≠ 1 := by decide +kernel
theorem block0 : blockMatrix A0.val = B0 := by decide +kernel
theorem block1 : blockMatrix A1.val = B1 := by decide +kernel
theorem block2 : blockMatrix A2.val = B2 := by decide +kernel
theorem block3 : blockMatrix A3.val = B3 := by decide +kernel

def word : Matrix (Fin 6) (Fin 6) K :=
  (bad * graphMatrix * B0) * (bad * graphMatrix * B1) *
    (bad * graphMatrix * B2) * (bad * graphMatrix * B3)

theorem word_eq : word = P3 := by
  rw [word, bad_graph, step0, step1, step2, step3, product1, product2, product3]

theorem word_square : word ^ 2 = Q := by rw [word_eq, pow_two, square]

theorem Q_pow : Q ^ 17 = 1 := by
  have h2 : Q ^ 2 = Q2 := by simpa only [pow_two] using square2
  have h4 : Q ^ 4 = Q4 := by
    rw [show 4 = 2 * 2 by rfl, pow_mul, h2, pow_two, square4]
  have h8 : Q ^ 8 = Q8 := by
    rw [show 8 = 4 * 2 by rfl, pow_mul, h4, pow_two, square8]
  have h16 : Q ^ 16 = Q16 := by
    rw [show 16 = 8 * 2 by rfl, pow_mul, h8, pow_two, square16]
  rw [show 17 = 16 + 1 by rfl, pow_succ, h16, final_product]

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.DiagonalSelection.Certificate
