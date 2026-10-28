module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuCocodeSylow
public import Theory.Representation.FirstCohomology
public import Theory.Mathieu.WordSubgroup

/-!
# Finite cocycle constraints for the M24 sextet residual

Two explicit odd-order words in the sextet stabilizer, together with the
standard generator orders, give 21 independent equations on the 22 binary
coordinates of a cocycle's generator values. One normalization coordinate
completes an invertible matrix. Both matrix identities are checked by the
kernel; the cocycle interpretation and original-core application are supplied
in the adjoining MathieuSextetCocycle modules.

Source: Aschbacher–Smith 8.2.12, printed p.722, refs/quasithin.pdf.
The permutation and Golay coordinates come from the imported native models,
with ATLAS Research and Attribution License 1.0 attribution in those modules.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.OneCohomology
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open MathieuCode MathieuCode.CocodeOctad.Involutions MathieuCode.QuadraticActors
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuSextet.Cocycle
set_option maxRecDepth 4096

def letter : Fin 2 → M24 := ![m24GeneratorAInM24,m24GeneratorBInM24]
def letterPoint : Fin 2 → Fin 24 → Fin 24 :=
  ![![20,4,7,17,1,13,9,2,15,6,19,18,21,5,16,8,14,3,11,10,0,12,23,22],![23,4,21,9,6,18,1,7,8,15,5,11,12,17,2,3,13,16,10,0,20,14,22,19]]
theorem letter_apply : ∀ i x, (letter i).val x = letterPoint i x := by decide +kernel

def word : Fin 4 → List (Fin 2)
  | 0 => [0, 0]
  | 1 => [1, 1, 1]
  | 2 => [0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1]
  | 3 => [0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1]

abbrev Slots := Fin 2 × Fin 11
def wordRows (p : Fin 24 → Fin 24) : List (Fin 2) → Matrix (Fin 11) Slots (ZMod 2)
  | [] => 0
  | a :: w => fun i j =>
      (if j.1 = a then pointMatrix p i j.2 + (1 : Matrix (Fin 11) (Fin 11) (ZMod 2)) i j.2 else 0) +
        wordRows (fun x => p (letterPoint a x)) w i j

def selected : Fin 21 → Fin 4 × Fin 11 := ![(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,8),(2,0),(2,1),(2,2),(2,4),(2,5),(2,6),(2,7),(2,9),(3,0),(3,2),(3,5)]
def flat (i : Slots) : Fin 22 := ⟨11*i.1.val+i.2.val,by omega⟩
def testMatrix : Matrix Slots Slots (ZMod 2) := fun i j =>
  if h : (flat i).val < 21 then
    let s := selected ⟨(flat i).val,h⟩
    wordRows id (word s.1) s.2 j
  else if j = (0,0) then 1 else 0

def row : Fin 22 → ℕ := ![169,834,284,320,116,1189888,2852864,3682304,3815424,3307520,1373839,3035537,4114741,1644816,3841631,3856824,2035149,3810397,2822307,1194556,2118529,1]
def inverseRow : Fin 22 → ℕ := ![2097152,2010375,3912325,1698606,2946719,1698610,962360,2097181,962352,2010381,215910,2138945,125227,67170,2216654,2231298,2352585,2138817,2302109,2216398,67522,2111941]
def encoded : Matrix Slots Slots (ZMod 2) := fun i j => bit (row (flat i)) (flat j).val
def inverseMatrix : Matrix Slots Slots (ZMod 2) := fun i j => bit (inverseRow (flat i)) (flat j).val

theorem matrix_check : testMatrix = encoded := by decide +kernel
theorem inverse_check : inverseMatrix * encoded = 1 := by decide +kernel

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuSextet.Cocycle
