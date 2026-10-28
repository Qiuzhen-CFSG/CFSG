module

public import Theory.Representation.G2DerivedPermutationFiltration.CycleFiltration.CosetAction.Geometry

/-!
# Actual ambient actions on the saved G₂ cycle coordinates

Kernel-checked XOR identities give the products of the saved 189-by-64 cycle
embedding with each of the eight ambient and two derived action matrices.
Their decoded identities and the certified coset enumeration give
`cycleLift_ambient` and `cycleLift_derived` in the actual flag module.
`pushForward_coordinates` identifies the literal incidence boundary in the
same ordering. These are the action and endpoint certificates consumed by
the construction of coordinates on the actual incidence kernel; completeness
of the cycle basis and its two factor blocks are separate matrix obligations.

Witness provenance and ATLAS attribution are in Data and source/README.md.
Source application: Aschbacher–Smith G.7.2(3), printed p.348 / PDF p.359.
-/

@[expose] public section

namespace G2DerivedPermutationFiltration.CycleFlagCoordinates
open VertexCoordinates
open CycleData

private def xorList : List ℕ → ℕ
  | [] => 0
  | a :: l => a ^^^ xorList l

private theorem bit_xor (a b x : ℕ) : bit (a ^^^ b) x = bit a x + bit b x := by
  unfold bit
  rw [Nat.testBit_xor]
  cases a.testBit x <;> cases b.testBit x <;> decide

private theorem bit_xorList (l : List ℕ) (x : ℕ) :
    bit (xorList l) x = (l.map (fun a => bit a x)).sum := by
  induction l with
  | nil => simp [xorList, bit]
  | cons a l ih => simp [xorList, bit_xor, ih]

private def combine {n : ℕ} (c : Fin n → ℕ) (b : Fin n → Bool) : ℕ :=
  xorList (List.ofFn fun y => if b y then c y else 0)

private theorem bit_combine {n : ℕ} (c : Fin n → ℕ) (b : Fin n → Bool) (x : ℕ) :
    bit (combine c b) x = ∑ y, bit (c y) x * (if b y then 1 else 0) := by
  rw [combine, bit_xorList, List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro y _
  cases h : b y <;> simp [h, bit]

private def pack {n : ℕ} (b : Fin n → Bool) := combine (fun x => 2 ^ x.val) b

private theorem bit_pack {n : ℕ} (b : Fin n → Bool) (x : Fin n) :
    bit (pack b) x.val = if b x then 1 else 0 := by
  rw [pack, bit_combine]
  simp only [bit, Nat.testBit_two_pow, Fin.val_inj, ite_mul, one_mul, zero_mul]
  simp

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
private theorem packed_ambient_action : ∀ (j : Fin 8) (y : Fin 64),
    combine cycleEmbeddingRows (fun z => (ambientCycleColumns j y).testBit z.val) =
      pack (fun x : Fin 189 => (cycleEmbeddingRows y).testBit (ambientTable j x).val) := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
private theorem packed_derived_action : ∀ (j : Fin 2) (y : Fin 64),
    combine cycleEmbeddingRows (fun z => (derivedCycleColumns j y).testBit z.val) =
      pack (fun x : Fin 189 => (cycleEmbeddingRows y).testBit (derivedInverseTable j x).val) := by
  decide +kernel

/-- The saved cycle embedding intertwines every ambient root/Weyl matrix
with the actual permutation of the 189 coordinates. -/
theorem cycleEmbedding_mul_ambient (j : Fin 8) :
    cycleEmbedding * ambientCycleMatrix j =
      fun x y => cycleEmbedding (ambientTable j x) y := by
  ext x y
  have h := congrArg (fun a => bit a x.val) (packed_ambient_action j y)
  rw [bit_combine, bit_pack] at h
  exact h

/-- The same identification for the two saved derived-generator matrices. -/
theorem cycleEmbedding_mul_derived (j : Fin 2) :
    cycleEmbedding * derivedCycleMatrix j =
      fun x y => cycleEmbedding (derivedInverseTable j x) y := by
  ext x y
  have h := congrArg (fun a => bit a x.val) (packed_derived_action j y)
  rw [bit_combine, bit_pack] at h
  exact h

/-- Reindex the actual flag module by the certified literal enumeration. -/
noncomputable def flagCoordinates :
    BinaryPermutation.Full Flag ≃ₗ[ZMod 2] (Fin 189 → ZMod 2) :=
  LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) flagEquiv

@[simp] theorem flagCoordinates_apply (v : BinaryPermutation.Full Flag) (x : Fin 189) :
    flagCoordinates v x = v (flag x) := rfl

@[simp] theorem flagCoordinates_symm_flag (v : Fin 189 → ZMod 2) (x : Fin 189) :
    flagCoordinates.symm v (flag x) = v x := by
  change (flagCoordinates (flagCoordinates.symm v)) x = v x
  rw [LinearEquiv.apply_symm_apply]

/-- The full ambient flag action, restricting to `flagRepresentation`. -/
def ambientFlagRepresentation :
    Representation (ZMod 2) FullGroup (BinaryPermutation.Full Flag) :=
  (BinaryPermutation.representation Flag).comp (MulAction.toPermHom FullGroup Flag)

@[simp] theorem ambientFlagRepresentation_subtype (g : Group) :
    ambientFlagRepresentation g.val = flagRepresentation g := rfl

/-- Reindexing gives the inverse-permutation action, as required on functions. -/
theorem flagCoordinates_ambient (j : Fin 8) (v : BinaryPermutation.Full Flag) :
    flagCoordinates (ambientFlagRepresentation (rootGenerator j) v) =
      fun x => flagCoordinates v (ambientTable j x) := by
  funext x
  change v ((MulAction.toPermHom FullGroup Flag (rootGenerator j)).symm (flag x)) = _
  congr 1
  apply (MulAction.toPermHom FullGroup Flag (rootGenerator j)).injective
  rw [Equiv.apply_symm_apply]
  change flag x = rootGenerator j • flag (ambientTable j x)
  rw [ambient_flag_action, ambientTable_involutive]

theorem flagCoordinates_derived (j : Fin 2) (v : BinaryPermutation.Full Flag) :
    flagCoordinates (flagRepresentation (groupGenerator j) v) =
      fun x => flagCoordinates v (derivedInverseTable j x) := by
  funext x
  change v ((flagPerm (groupGenerator j)).symm (flag x)) = _
  congr 1
  apply (flagPerm (groupGenerator j)).injective
  rw [Equiv.apply_symm_apply, flagEquiv_apply, derived_flag_action, derivedTable_right]

/-- The literal saved cycle vectors, now in the actual flag module. -/
noncomputable def cycleLift : (Fin 64 → ZMod 2) →ₗ[ZMod 2] BinaryPermutation.Full Flag :=
  flagCoordinates.symm.toLinearMap.comp cycleEmbedding.mulVecLin

/-- Coordinate action of all eight ambient generators on the actual lifted
cycle vectors. No representation has been substituted for the flag module. -/
theorem cycleLift_ambient (j : Fin 8) (v : Fin 64 → ZMod 2) :
    cycleLift ((ambientCycleMatrix j).mulVec v) =
      ambientFlagRepresentation (rootGenerator j) (cycleLift v) := by
  apply flagCoordinates.injective
  rw [flagCoordinates_ambient]
  change flagCoordinates (flagCoordinates.symm (cycleEmbedding.mulVec
      ((ambientCycleMatrix j).mulVec v))) =
    fun x => flagCoordinates (flagCoordinates.symm (cycleEmbedding.mulVec v)) (ambientTable j x)
  simp only [LinearEquiv.apply_symm_apply]
  rw [Matrix.mulVec_mulVec, cycleEmbedding_mul_ambient]
  rfl

/-- Coordinate action of the two actual commutator-subgroup actors. -/
theorem cycleLift_derived (j : Fin 2) (v : Fin 64 → ZMod 2) :
    cycleLift ((derivedCycleMatrix j).mulVec v) =
      flagRepresentation (groupGenerator j) (cycleLift v) := by
  apply flagCoordinates.injective
  rw [flagCoordinates_derived]
  change flagCoordinates (flagCoordinates.symm (cycleEmbedding.mulVec
      ((derivedCycleMatrix j).mulVec v))) =
    fun x => flagCoordinates (flagCoordinates.symm (cycleEmbedding.mulVec v)) (derivedInverseTable j x)
  simp only [LinearEquiv.apply_symm_apply]
  rw [Matrix.mulVec_mulVec, cycleEmbedding_mul_derived]
  rfl

/-- Boundary formula in the exact flag and vertex ordering used by the data. -/
theorem pushForward_coordinates (i : Fin 2) (v : Fin 189 → ZMod 2) :
    pushForward i (flagCoordinates.symm v) =
      ∑ x : Fin 189, v x • vertexBasis i (vertex i (endpoint i x)) := by
  rw [pushForward_apply, ← Equiv.sum_comp flagEquiv]
  simp only [flagEquiv_apply, flagCoordinates_symm_flag, projection_flag]

end G2DerivedPermutationFiltration.CycleFlagCoordinates
