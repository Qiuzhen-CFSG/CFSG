module
public import Theory.Representation.BinaryEndpointInduction.CosetCoordinates
public import Theory.SpecificGroups.Thompson.Model.GeneratorCertificates.BinaryMatrix
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Tactic

/-!
# The literal fifteen-point permutation coordinates

These six matrices act on right rows by the exact frozen right-coset
transitions. The first two are the shear and cycle. Their product has five
primary blocks of dimensions 1,2,4,4,4 in the displayed invertible basis.
All arithmetic identities below are checked by the Lean kernel.
-/
@[expose] public section
namespace BinaryFifteenPoint
open Matrix Thompson.BinaryMatrix

/-- Packed rows in the original ordered fifteen right cosets. -/
def actorRows : Array (Array ℕ) := #[#[128, 2, 4, 8, 16, 32, 8192, 1, 4096, 512, 1024, 16384, 256, 64, 2048], #[32, 1, 128, 2, 4, 8, 16, 64, 8192, 256, 4096, 512, 1024, 2048, 16384], #[1, 4, 2, 8, 16, 32, 64, 256, 128, 1024, 512, 2048, 4096, 16384, 8192], #[1, 2, 512, 16, 8, 32, 64, 128, 16384, 4, 1024, 4096, 2048, 8192, 256], #[1, 2, 4, 8, 2048, 64, 32, 128, 256, 16384, 8192, 16, 4096, 1024, 512], #[1, 2, 4, 8, 16384, 8192, 1024, 128, 256, 2048, 64, 512, 4096, 32, 16]]

/-- The six literal right-row permutation matrices. -/
def permutationActor (a : Fin 6) : Matrix (Fin 15) (Fin 15) (ZMod 2) :=
  decode 15 actorRows[a.val]!

private theorem entry_check : ∀ (a : Fin 6) (i j : Fin 15),
    (actorRows[a.val]!)[i.val]!.testBit j.val =
      decide (BinaryEndpointInduction.transitionIndex a i=j) := by decide +kernel

/-- Exact agreement with the original endpoint coset transition table. -/
theorem permutationActor_entry (a : Fin 6) (i j : Fin 15) :
    permutationActor a i j =
      if BinaryEndpointInduction.transitionIndex a i=j then 1 else 0 := by
  change (if (actorRows[a.val]!)[i.val]!.testBit j.val then (1 : ZMod 2) else 0)=_
  rw [entry_check]
  simp

/-- Packed rows of the change from primary coordinates to original cosets. -/
def changeRows : Array ℕ := #[32767, 15310, 28083, 2550, 19629, 21226, 11051, 3191, 22733, 27362, 19257, 791, 1477, 7392, 30760]
/-- Packed rows of its inverse. -/
def inverseRows : Array ℕ := #[23003, 22247, 23461, 11573, 22419, 27291, 19245, 20295, 23167, 20853, 19563, 28247, 27853, 11663, 10427]
/-- Primary coordinates to original coset coordinates. -/
def changeMatrix : Matrix (Fin 15) (Fin 15) (ZMod 2) := decode 15 changeRows
/-- Original coset coordinates to primary coordinates. -/
def inverseChangeMatrix : Matrix (Fin 15) (Fin 15) (ZMod 2) := decode 15 inverseRows

/-- The six actors in the same primary coordinates. -/
def adaptedRows : Array (Array ℕ) := #[#[1, 20594, 20500, 104, 16, 64, 32, 13906, 20752, 5276, 9262, 10286, 16400, 8288, 4112], #[1, 22652, 22566, 72, 32, 24, 64, 24764, 23072, 9654, 17618, 20562, 30752, 16472, 8224], #[1, 6184, 4184, 8, 64, 112, 16, 7582, 7246, 1892, 2322, 38, 92, 10278, 16384], #[1, 2144, 30776, 32, 56, 8, 104, 29292, 946, 30862, 3146, 98, 26644, 8192, 18530], #[1, 90, 22652, 8, 72, 32, 24, 24932, 24764, 23072, 9654, 18442, 20562, 30752, 16472], #[1, 16464, 14432, 80, 72, 120, 64, 1950, 17996, 31342, 17172, 18442, 4096, 22582, 10]]
/-- A literal actor in the displayed primary basis. -/
def adaptedActor (a : Fin 6) : Matrix (Fin 15) (Fin 15) (ZMod 2) :=
  decode 15 adaptedRows[a.val]!

/-- Packed rows of the companion-block operator. -/
def companionRows : Array ℕ := #[1, 4, 6, 16, 32, 64, 24, 256, 512, 1024, 1152, 4096, 8192, 16384, 30720]
/-- The product of the two generating actors in primary coordinates. -/
def companion : Matrix (Fin 15) (Fin 15) (ZMod 2) := decode 15 companionRows

private theorem inverse_check : ∀ i : Fin 15,
    rowProduct changeRows[i.val]! inverseRows 15=2^i.val := by decide +kernel
private theorem reverse_inverse_check : ∀ i : Fin 15,
    rowProduct inverseRows[i.val]! changeRows 15=2^i.val := by decide +kernel

/-- The displayed changes of coordinates are two-sided inverses. -/
theorem change_inverse : changeMatrix*inverseChangeMatrix=1 ∧
    inverseChangeMatrix*changeMatrix=1 :=
  ⟨decode_mul_one 15 _ _ inverse_check,decode_mul_one 15 _ _ reverse_inverse_check⟩

private theorem intertwine_check : ∀ (a : Fin 6) (i : Fin 15),
    rowProduct changeRows[i.val]! actorRows[a.val]! 15=
      rowProduct (adaptedRows[a.val]!)[i.val]! changeRows 15 := by decide +kernel

/-- All six original actors preserve their exact matrix marking under the basis change. -/
theorem actor_intertwine (a : Fin 6) :
    changeMatrix*permutationActor a=adaptedActor a*changeMatrix := by
  ext i j
  change (∑ x : Fin 15, bit changeRows[i.val]! x.val *
      bit (actorRows[a.val]!)[x.val]! j.val)=
    ∑ x : Fin 15, bit (adaptedRows[a.val]!)[i.val]! x.val * bit changeRows[x.val]! j.val
  rw [Fin.sum_univ_eq_sum_range (fun x => bit changeRows[i.val]! x *
    bit (actorRows[a.val]!)[x]! j.val),
    Fin.sum_univ_eq_sum_range (fun x => bit (adaptedRows[a.val]!)[i.val]! x *
      bit changeRows[x]! j.val),←bit_rowProduct,←bit_rowProduct,intertwine_check]

private theorem product_check : ∀ i : Fin 15,
    rowProduct (adaptedRows[0]!)[i.val]! adaptedRows[1]! 15=companionRows[i.val]! := by
  decide +kernel

/-- The actual shear-cycle product supplies the primary-block operator. -/
theorem spectral_intertwine :
    changeMatrix*(permutationActor 0*permutationActor 1)=companion*changeMatrix := by
  have hp : adaptedActor 0*adaptedActor 1=companion := decode_mul 15 _ _ _ product_check
  rw [←Matrix.mul_assoc,actor_intertwine,Matrix.mul_assoc,actor_intertwine,
    ←Matrix.mul_assoc,hp]

end BinaryFifteenPoint
