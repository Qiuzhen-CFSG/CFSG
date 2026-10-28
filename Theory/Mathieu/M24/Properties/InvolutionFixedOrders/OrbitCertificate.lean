module
public import Theory.Mathieu.M24.Basic
public import Theory.Mathieu.M24.Properties.Sylow3
public import Mathlib.Data.Fin.VecNotation
import all Theory.Mathieu.M24.Properties.Sylow3
import all Theory.Mathieu.M24.Block
/-!
# Finite orbit certificates for the four M₂₄ Sylow-three planes

The original certified Sylow generators give four elementary subgroups of
order nine. Their degree-24 orbits leave 54 possible fixed-point-free
commuting involutions. The recorded permutations are checked by orbit
coordinates, and each fails a Golay parity check on one of three actual
octads. These are finite certificates used by the following source proof.

The internal imports reuse the original Sylow generators and Golay
self-orthogonality proof. No alternative carrier is introduced.
Source: Aschbacher–Smith 16.1.5(7), E.6.18 and E.6.23.
-/
open Sporadic.Mathieu Subgroup
namespace Sporadic.Mathieu.M24InvolutionFixedOrders
private def plane : Fin 4 → Equiv.Perm (Fin 24) :=
  ![rankXPerm, rankYPerm, rankXPerm * rankYPerm, rankXPerm * rankYPerm ^ 2]
private def orbitWord (i : Fin 4) (a b : Fin 3) : Equiv.Perm (Fin 24) :=
  plane i ^ a.val * rankZPerm ^ b.val
private def otherNine : Fin 9 → Fin 24 := ![2,3,5,9,10,14,15,18,21]
private def otherThree : Fin 3 → Fin 24 := ![11,12,22]
private def smallPlane (k : Fin 2) : Fin 4 := ⟨k.val + 2, by omega⟩
private def candidateTable : Array (Array (Fin 24)) := #[
  #[2,11,0,7,22,8,12,3,5,13,23,1,6,9,16,19,14,18,17,15,21,20,4,10],
  #[2,12,0,7,11,8,22,3,5,13,23,4,1,9,16,19,14,18,17,15,21,20,6,10],
  #[2,22,0,7,12,8,11,3,5,13,23,6,4,9,16,19,14,18,17,15,21,20,1,10],
  #[3,11,13,0,22,19,12,9,18,7,16,1,6,2,20,17,10,15,8,5,14,23,4,21],
  #[3,12,13,0,11,19,22,9,18,7,16,4,1,2,20,17,10,15,8,5,14,23,6,21],
  #[3,22,13,0,12,19,11,9,18,7,16,6,4,2,20,17,10,15,8,5,14,23,1,21],
  #[5,11,16,23,22,0,12,18,14,20,17,1,6,15,8,13,2,10,7,21,9,19,4,3],
  #[5,12,16,23,11,0,22,18,14,20,17,4,1,15,8,13,2,10,7,21,9,19,6,3],
  #[5,22,16,23,12,0,11,18,14,20,17,6,4,15,8,13,2,10,7,21,9,19,1,3],
  #[9,11,7,13,22,17,12,2,15,0,20,1,6,3,23,8,21,5,19,18,10,16,4,14],
  #[9,12,7,13,11,17,22,2,15,0,20,4,1,3,23,8,21,5,19,18,10,16,6,14],
  #[9,22,7,13,12,17,11,2,15,0,20,6,4,3,23,8,21,5,19,18,10,16,1,14],
  #[10,11,19,8,22,20,12,21,3,17,0,1,6,14,13,23,18,9,16,2,5,7,4,15],
  #[10,12,19,8,11,20,22,21,3,17,0,4,1,14,13,23,18,9,16,2,5,7,6,15],
  #[10,22,19,8,12,20,11,21,3,17,0,6,4,14,13,23,18,9,16,2,5,7,1,15],
  #[14,11,8,17,22,16,12,10,2,19,7,1,6,21,0,20,5,3,23,9,15,13,4,18],
  #[14,12,8,17,11,16,22,10,2,19,7,4,1,21,0,20,5,3,23,9,15,13,6,18],
  #[14,22,8,17,12,16,11,10,2,19,7,6,4,21,0,20,5,3,23,9,15,13,1,18],
  #[15,11,23,20,22,7,12,5,21,16,19,1,6,18,17,0,9,14,13,10,3,8,4,2],
  #[15,12,23,20,11,7,22,5,21,16,19,4,1,18,17,0,9,14,13,10,3,8,6,2],
  #[15,22,23,20,12,7,11,5,21,16,19,6,4,18,17,0,9,14,13,10,3,8,1,2],
  #[18,11,20,16,22,13,12,15,10,23,8,1,6,5,19,7,3,21,0,14,2,17,4,9],
  #[18,12,20,16,11,13,22,15,10,23,8,4,1,5,19,7,3,21,0,14,2,17,6,9],
  #[18,22,20,16,12,13,11,15,10,23,8,6,4,5,19,7,3,21,0,14,2,17,1,9],
  #[21,11,17,19,22,23,12,14,9,8,13,1,6,10,7,16,15,2,20,3,18,0,4,5],
  #[21,12,17,19,11,23,22,14,9,8,13,4,1,10,7,16,15,2,20,3,18,0,6,5],
  #[21,22,17,19,12,23,11,14,9,8,13,6,4,10,7,16,15,2,20,3,18,0,1,5],
  #[2,11,0,16,12,13,22,9,18,7,23,1,4,5,20,19,3,21,8,15,14,17,6,10],
  #[2,12,0,16,22,13,11,9,18,7,23,6,1,5,20,19,3,21,8,15,14,17,4,10],
  #[2,22,0,16,11,13,12,9,18,7,23,4,6,5,20,19,3,21,8,15,14,17,1,10],
  #[3,11,20,0,12,19,22,15,10,13,8,1,4,9,16,7,14,18,17,5,2,23,6,21],
  #[3,12,20,0,22,19,11,15,10,13,8,6,1,9,16,7,14,18,17,5,2,23,4,21],
  #[3,22,20,0,11,19,12,15,10,13,8,4,6,9,16,7,14,18,17,5,2,23,1,21],
  #[5,11,8,23,12,0,22,10,2,16,7,1,4,18,17,20,9,14,13,21,15,19,6,3],
  #[5,12,8,23,22,0,11,10,2,16,7,6,1,18,17,20,9,14,13,21,15,19,4,3],
  #[5,22,8,23,11,0,12,10,2,16,7,4,6,18,17,20,9,14,13,21,15,19,1,3],
  #[9,11,17,8,12,20,22,21,3,0,13,1,4,10,23,16,15,2,19,18,5,7,6,14],
  #[9,12,17,8,22,20,11,21,3,0,13,6,1,10,23,16,15,2,19,18,5,7,4,14],
  #[9,22,17,8,11,20,12,21,3,0,13,4,6,10,23,16,15,2,19,18,5,7,1,14],
  #[10,11,19,13,12,17,22,14,9,8,0,1,4,3,7,23,21,5,20,2,18,16,6,15],
  #[10,12,19,13,22,17,11,14,9,8,0,6,1,3,7,23,21,5,20,2,18,16,4,15],
  #[10,22,19,13,11,17,12,14,9,8,0,4,6,3,7,23,21,5,20,2,18,16,1,15],
  #[14,11,16,20,12,7,22,5,21,19,17,1,4,15,0,13,2,10,23,9,3,8,6,18],
  #[14,12,16,20,22,7,11,5,21,19,17,6,1,15,0,13,2,10,23,9,3,8,4,18],
  #[14,22,16,20,11,7,12,5,21,19,17,4,6,15,0,13,2,10,23,9,3,8,1,18],
  #[15,11,23,17,12,16,22,18,14,20,19,1,4,21,8,0,5,3,7,10,9,13,6,2],
  #[15,12,23,17,22,16,11,18,14,20,19,6,1,21,8,0,5,3,7,10,9,13,4,2],
  #[15,22,23,17,11,16,12,18,14,20,19,4,6,21,8,0,5,3,7,10,9,13,1,2],
  #[18,11,13,7,12,8,22,3,5,23,16,1,4,2,19,17,10,15,0,14,21,20,6,9],
  #[18,12,13,7,22,8,11,3,5,23,16,6,1,2,19,17,10,15,0,14,21,20,4,9],
  #[18,22,13,7,11,8,12,3,5,23,16,4,6,2,19,17,10,15,0,14,21,20,1,9],
  #[21,11,7,19,12,23,22,2,15,17,20,1,4,14,13,8,18,9,16,3,10,0,6,5],
  #[21,12,7,19,22,23,11,2,15,17,20,6,1,14,13,8,18,9,16,3,10,0,4,5],
  #[21,22,7,19,11,23,12,2,15,17,20,4,6,14,13,8,18,9,16,3,10,0,1,5]]
private def candidate (k : Fin 2) (a : Fin 9) (b : Fin 3) : Fin 24 → Fin 24 :=
  fun i => (candidateTable[k.val*27+a.val*3+b.val]!)[i.val]!
private def witnessTable : Array (Fin 4096) := #[1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,4,1,1,1,1,2,1,1,1,1,1,1,1,1,1,1,1,1,1,2,1,1,1,1,1]
private def rowTable : Array (Fin 12) := #[1,2,1,2,1,2,2,1,2,2,1,2,1,3,1,1,3,1,2,1,2,1,2,1,1,4,1,4,1,4,2,1,2,1,3,1,1,2,1,1,2,1,1,2,1,1,2,1,3,1,4,2,1,2]
private def witness (k : Fin 2) (a : Fin 9) (b : Fin 3) : Fin 4096 :=
  witnessTable[k.val*27+a.val*3+b.val]!
private def checkRow (k : Fin 2) (a : Fin 9) (b : Fin 3) : Fin 12 :=
  rowTable[k.val*27+a.val*3+b.val]!
private theorem block_parity (B : Finset (Fin 24)) (hB : B ∈ m24Blocks) (i : Fin 12) :
    2 ∣ (B ∩ m24BitVecSupport (m24GolayRow i)).card := by
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hB
  rw [m24BlockAt_eq_m24GolayWord]
  exact (m24GolayCode_invariant _).2 i
private theorem witness_card : ∀ k a b, (m24GolayWord (witness k a b)).card = 8 := by
  decide +kernel
private theorem candidate_bad_parity : ∀ k a b,
    ¬ 2 ∣ ((m24GolayWord (witness k a b)).image (candidate k a b) ∩
      m24BitVecSupport (m24GolayRow (checkRow k a b))).card := by
  decide +kernel
private theorem orbitWord_cube : ∀ i a b, orbitWord i a b ^ 3 = 1 := by
  decide +kernel
private theorem candidate_coordinates : ∀ k a b (x : Fin 24), ∃ c d : Fin 3,
    (orbitWord (smallPlane k) c d 0 = x ∧
      orbitWord (smallPlane k) c d (otherNine a) = candidate k a b x) ∨
    (orbitWord (smallPlane k) c d (otherNine a) = x ∧
      orbitWord (smallPlane k) c d 0 = candidate k a b x) ∨
    (orbitWord (smallPlane k) c d 1 = x ∧
      orbitWord (smallPlane k) c d (otherThree b) = candidate k a b x) ∨
    (orbitWord (smallPlane k) c d (otherThree b) = x ∧
      orbitWord (smallPlane k) c d 1 = candidate k a b x) := by
  decide +kernel
private def sameStabilizer (i : Fin 4) (x y : Fin 24) : Prop :=
  ∀ a b : Fin 3, orbitWord i a b x = x ↔ orbitWord i a b y = y
private theorem first_orbit_unique : ∀ (i : Fin 2) (y : Fin 24),
    sameStabilizer ⟨i.val,by omega⟩ (if i=0 then 2 else 0) y →
      ∃ a b, orbitWord ⟨i.val,by omega⟩ a b (if i=0 then 2 else 0) = y := by
  unfold sameStabilizer
  decide +kernel
private theorem second_orbit_options : ∀ k (y : Fin 24),
    (sameStabilizer (smallPlane k) 0 y →
      (∃ a b, orbitWord (smallPlane k) a b 0 = y) ∨ ∃ a, otherNine a = y) ∧
    (sameStabilizer (smallPlane k) 1 y →
      (∃ a b, orbitWord (smallPlane k) a b 1 = y) ∨ ∃ b, otherThree b = y) := by
  unfold sameStabilizer
  decide +kernel
end Sporadic.Mathieu.M24InvolutionFixedOrders
