module

public import Theory.Representation.Mathieu.M22James.Model
public import Theory.Representation.SL2FourNaturalOrbits.Model

/-!
# Coordinates for the genuine triple Mathieu module

The six field coordinates are the paired binary rows of the inverse of the
orthonormal frame [1, 5, 52, 231, 998, 1758]. The decoder certificate proves
that these coordinates retain every binary vector. The two six by six
matrices are candidates for the actual native generators; their action and
unitary identities are checked in `Certificates`.

Source: Aschbacher–Smith H.12.1(2), printed pp.393–394. The binary generators
are the native ATLAS matrices attributed in the `M22James.Model` imports;
column zero is the least significant bit in each packed row. The coordinate
data were obtained by binary Gaussian elimination, and are checked in Lean.
-/

@[expose] public section
namespace Sporadic.Mathieu.M22TripleCover.Unitary
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Matrix
open Representation.SL2FourNatural
open scoped Matrix

abbrev Vector := Fin 6 → F

def coordMatrix : Matrix (Fin 6) (Fin 12) F := fun i j =>
  ⟨fromRows ![295,2890,92,2240,2026,2160,706,3192,3512,3322,3248,3210]
      ⟨2*i.val, by omega⟩ j,
    fromRows ![295,2890,92,2240,2026,2160,706,3192,3512,3322,3248,3210]
      ⟨2*i.val+1, by omega⟩ j⟩

def decodeMatrix : Matrix (Fin 12) (Fin 6) F := fun j i =>
  ⟨fromRows ![743,3554,4084,3752,1042,2904,1354,3938,2984,1930,3592,2592]
      j ⟨2*i.val, by omega⟩,
    fromRows ![743,3554,4084,3752,1042,2904,1354,3938,2984,1930,3592,2592]
      j ⟨2*i.val+1, by omega⟩⟩

theorem decode_coord : (decodeMatrix * coordMatrix).map QuadraticAlgebra.re =
    (1 : Matrix12) := by decide +kernel

def fieldEntry (n : ℕ) : F := ⟨if n.testBit 0 then 1 else 0,
  if n.testBit 1 then 1 else 0⟩

def generatorA : Matrix (Fin 6) (Fin 6) F :=
  (!![1,0,1,2,2,3; 3,3,0,3,3,2; 2,3,2,0,3,1;
      3,3,2,3,0,2; 3,1,2,1,3,0; 0,1,2,1,3,2] : Matrix _ _ ℕ).map fieldEntry

def generatorB : Matrix (Fin 6) (Fin 6) F :=
  (!![1,0,2,0,0,3; 0,1,2,0,0,3; 3,3,1,2,1,0;
      0,0,3,1,0,1; 0,0,1,0,1,2; 2,2,0,1,3,1] : Matrix _ _ ℕ).map fieldEntry

end Sporadic.Mathieu.M22TripleCover.Unitary
