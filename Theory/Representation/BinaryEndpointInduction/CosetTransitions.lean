module
public import Theory.Representation.BinaryEndpointInduction.CosetCoordinates
public import Theory.Representation.BinaryEndpointInduction.CoordinateCertificates
public import Theory.Representation.BinaryEndpointInduction.MaskCoordinates

/-!
# Checked transitions for the original endpoint induction coordinates

The exact right-coset equations retain the original actors and corrections.
Every correction and each of the four parabolic actors fixes row e0. The
literal forty-five coordinate matrices have the indicated three-by-three
blocks, including the inverse-transpose orientation. Both generator tables
and all four spectral parabolic matrices agree with these actual transitions.

These finite identities support a map into the original conjugate span;
they do not assume or assert a classification of its quotient module.
Source context: Aschbacher--Smith 15.3.23, binary-four carrier.
-/
public section
open Matrix
open scoped MatrixGroups
namespace BinaryEndpointInduction
open Thompson.BinaryMatrix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The seed block is the identity right coset. -/
theorem cosetRepresentative_zero : cosetRepresentative 0 = 1 := by decide +kernel

/-- Actor indices zero and one retain the proved generating pair. -/
theorem cosetActor_generators :
    cosetActor 0 = transvectionGenerator ∧ cosetActor 1 = cycleGenerator := by
  constructor <;> rfl

/-- The last four actor indices retain their original parabolic marking. -/
theorem cosetActor_parabolic : ∀ k : Fin 4,
    cosetActor ⟨k.val + 2, by omega⟩ = parabolicGenerator k := by decide +kernel

/-- Each actual parabolic actor fixes the row vector e0. -/
theorem parabolicGenerator_row_zero : ∀ k : Fin 4, ∀ j : Fin 4,
    (parabolicGenerator k).val 0 j = if j = 0 then 1 else 0 := by decide +kernel

/-- The actual equation is r_i*g = p*r_j, for all six original actors. -/
theorem coset_transition : ∀ a : Fin 6, ∀ i : Fin 15,
    cosetRepresentative i * cosetActor a =
      transitionCorrection a i * cosetRepresentative (transitionIndex a i) := by
  decide +kernel

/-- Each transition correction belongs to the same row-e0 stabilizer. -/
theorem transitionCorrection_row_zero : ∀ a : Fin 6, ∀ i : Fin 15, ∀ j : Fin 4,
    (transitionCorrection a i).val 0 j = if j = 0 then 1 else 0 := by decide +kernel

/-- Flag false is the actual lower-right Levi block in right-row convention. -/
theorem transitionBlock_false : ∀ a : Fin 6, ∀ i : Fin 15,
    transitionBlock false a i =
      (transitionCorrection a i).val.submatrix Fin.succ Fin.succ := by decide +kernel

/-- Flag true is inverse transpose of that same Levi block. Both inverse
identities are retained without relying on an unchecked matrix inversion. -/
theorem transitionBlock_inverseTranspose : ∀ a : Fin 6, ∀ i : Fin 15,
    transitionBlock true a i * (transitionBlock false a i).transpose = 1 ∧
      (transitionBlock false a i).transpose * transitionBlock true a i = 1 := by
  decide +kernel

/-- The stored right-row matrices implement precisely the original coset
transition and its local coefficient, with the exact block order retained. -/
theorem inducedCosetMatrix_entry : ∀ dual : Bool, ∀ a : Fin 6,
    ∀ i j : Fin 15, ∀ u v : Fin 3,
    inducedCosetMatrix dual a ⟨3 * i.val + u.val, by omega⟩
      ⟨3 * j.val + v.val, by omega⟩ =
      if transitionIndex a i = j then transitionBlock dual a i u v else 0 := by
  decide +kernel

/-- The two original generator matrices are exactly the transition matrices. -/
theorem inducedCosetMatrix_generators : ∀ dual : Bool, ∀ k : Fin 2,
    inducedCosetMatrix dual ⟨k.val, by omega⟩ = generator dual k := by decide +kernel

private theorem parabolic_intertwine_check : ∀ dual : Bool, ∀ k : Fin 4, ∀ i : Fin 45,
    rowProduct (changeRows dual)[i.val]! (inducedCosetRows dual)[k.val + 2]! 45 =
      rowProduct ((adaptedParabolicRows dual)[k.val]!)[i.val]! (changeRows dual) 45 := by
  decide +kernel

/-- All four spectral parabolic matrices come from their actual actors,
through the same checked change of basis used for the group generators. -/
theorem parabolic_intertwine (dual : Bool) (k : Fin 4) :
    changeMatrix dual * inducedCosetMatrix dual ⟨k.val + 2, by omega⟩ =
      adaptedParabolic dual k * changeMatrix dual := by
  ext i j
  change (∑ x : Fin 45, bit (changeRows dual)[i.val]! x.val *
      bit ((inducedCosetRows dual)[k.val + 2]!)[x.val]! j.val) =
    ∑ x : Fin 45, bit ((adaptedParabolicRows dual)[k.val]!)[i.val]! x.val *
      bit (changeRows dual)[x.val]! j.val
  rw [Fin.sum_univ_eq_sum_range (fun x => bit (changeRows dual)[i.val]! x *
    bit ((inducedCosetRows dual)[k.val + 2]!)[x]! j.val),
    Fin.sum_univ_eq_sum_range (fun x => bit ((adaptedParabolicRows dual)[k.val]!)[i.val]! x *
      bit (changeRows dual)[x]! j.val),
    ← bit_rowProduct, ← bit_rowProduct, parabolic_intertwine_check]

end BinaryEndpointInduction
