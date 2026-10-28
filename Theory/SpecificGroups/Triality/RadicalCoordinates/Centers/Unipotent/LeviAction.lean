module

public import Theory.SpecificGroups.Triality.RadicalCoordinates.Centers.Unipotent.MatrixEntries

/-!
# The highest root commutes with the negative arm curves

On the full Geck lattice the linear and quadratic coefficients of the highest
root commute with those of each negative arm-simple root. Compact binary row
certificates check these four coefficient identities, and scalar extension
proves commutation for every pair of field parameters. The existing canonical
positive-root comparison and the signed simple-root comparison identify the
matrices with the actual curves, retaining the negative-root convention.

The binary row encoding and its operation proofs are adapted from this
repository's `PositiveRootCoordinates/Collection/SumExchange/PolynomialExchange`.
Source: GLS3 §§2.4 and 2.6 (`refs/KGroup/GLS3/chapter2.tex`), as used for
Aschbacher–Smith F.1.12(4), including q = 2.
-/
open Theory.AlgebraicGroup.StandardRootSystem
open Triality.Standard.PositiveCoordinates
open Triality.Standard.PositiveCoordinates.SumExchangeData
open RootPairing.IntegralGeckConstruction
open Triality.Standard.Parabolics.RankOneMatrices
namespace Triality.Standard.RadicalCoordinates.Centers.UnipotentLevi
noncomputable section
local instance : DecidableEq LatticeIndex := fun a b => instDecidableEqSum a b

/-- Bits 0–3 are Cartan coordinates; bits 4–27 are root coordinates. -/
def indexNumber : Index → ℕ
  | .inl i => i.val
  | .inr i => 4 + i.val

def bitEntry (a : ℕ) (s : Index) : ZMod 2 := if a.testBit (indexNumber s) then 1 else 0

lemma bitEntry_zero (s : Index) : bitEntry 0 s = 0 := by simp [bitEntry]

lemma bitEntry_xor (a b : ℕ) (s : Index) :
    bitEntry (Nat.xor a b) s = bitEntry a s + bitEntry b s := by
  simp only [bitEntry, Nat.xor_eq, Nat.testBit_xor]
  cases a.testBit (indexNumber s) <;> cases b.testBit (indexNumber s) <;> decide

lemma bitEntry_fold (l : List ℕ) (s : Index) :
    bitEntry (l.foldr Nat.xor 0) s = (l.map (fun a => bitEntry a s)).sum := by
  induction l with
  | nil => simp [bitEntry_zero]
  | cons a l ih => simp only [List.foldr_cons, List.map_cons, List.sum_cons, bitEntry_xor, ih]

/-- The operations only need to model their decoded matrices. -/
structure BinaryRows where
  row : Index → ℕ

instance : DecidableEq BinaryRows := fun a b =>
  decidable_of_iff (a.row = b.row)
    ⟨fun h => by cases a; cases b; exact congrArg BinaryRows.mk h,
      fun h => congrArg BinaryRows.row h⟩

instance : Zero BinaryRows := ⟨⟨fun _ => 0⟩⟩
instance : Add BinaryRows := ⟨fun a b => ⟨fun r => Nat.xor (a.row r) (b.row r)⟩⟩

def allIndices : List Index :=
  (List.ofFn (fun i : Fin 4 => Sum.inl i)) ++ (List.ofFn (fun i : Fin 24 => Sum.inr i))

instance : Mul BinaryRows := ⟨fun a b => ⟨fun r =>
  (allIndices.map (fun u => if (a.row r).testBit (indexNumber u) then b.row u else 0)).foldr Nat.xor 0⟩⟩

def decode (a : BinaryRows) : Matrix Index Index (ZMod 2) := fun r s => bitEntry (a.row r) s

lemma decode_zero : decode 0 = 0 := by ext r s; exact bitEntry_zero s
lemma decode_add (a b : BinaryRows) : decode (a + b) = decode a + decode b := by
  ext r s
  exact bitEntry_xor _ _ _
-- Use homogeneous multiplication here, matching the abstract transport lemma.
-- Otherwise elaboration expands finite matrix products during instance comparison.
lemma decode_mul (a b : BinaryRows) : decode (a * b) = Mul.mul (decode a) (decode b) := by
  ext r s
  change bitEntry ((allIndices.map (fun u => if (a.row r).testBit (indexNumber u) then b.row u else 0)).foldr Nat.xor 0) s =
    ∑ u : Index, bitEntry (a.row r) u * bitEntry (b.row u) s
  rw [bitEntry_fold]
  simp only [List.map_map]
  have h (u : Index) : bitEntry (if (a.row r).testBit (indexNumber u) then b.row u else 0) s =
      bitEntry (a.row r) u * bitEntry (b.row u) s := by
    unfold bitEntry
    split <;> simp_all
  simp only [allIndices, List.map_append, List.sum_append, List.map_ofFn,
    List.sum_ofFn, Fintype.sum_sum_type, Function.comp_apply, h]

def highestLinearBits : BinaryRows :=
  ⟨Sum.elim ![128, 0, 128, 128]
    ![2, 0, 0, 0, 262144, 524288, 0, 0, 4194304, 8388608, 0, 0, 1024, 2048, 0, 0, 16384, 32768, 0, 0, 0, 0, 0, 0]⟩

def negativeLinearBits : Fin 4 → BinaryRows :=
  ![⟨Sum.elim ![32, 0, 0, 0]
      ![0, 0, 2, 0, 0, 0, 262144, 524288, 0, 0, 4194304, 8388608, 256, 512, 0, 0, 4096, 8192, 0, 0, 0, 0, 0, 0]⟩,
    ⟨Sum.elim ![0, 131072, 0, 0]
      ![0, 512, 0, 2048, 16, 0, 64, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 67108864, 134217728, 1048576, 2097152, 0, 0]⟩,
    ⟨Sum.elim ![0, 0, 33554432, 0]
      ![0, 0, 0, 0, 0, 8192, 0, 32768, 256, 0, 1024, 0, 0, 2097152, 0, 8388608, 65536, 0, 262144, 0, 0, 0, 2, 0]⟩,
    ⟨Sum.elim ![0, 0, 0, 16777216]
      ![0, 0, 0, 0, 0, 4096, 0, 16384, 0, 256, 0, 1024, 0, 1048576, 0, 4194304, 0, 65536, 0, 262144, 0, 0, 0, 2]⟩]

def quadraticBits (r : Fin 24) : BinaryRows :=
  ⟨fun q => if q = .inr r then 2 ^ (4 + (negativeIndex r).val) else 0⟩

lemma highest_linear_eq : decode highestLinearBits = linearCoefficient 0 := by
  decide +kernel

lemma negative_linear_eq (i : Fin 4) :
    decode (negativeLinearBits i) = linearCoefficient (negativeIndex (simpleIndex i)) := by
  revert i
  decide +kernel

lemma highest_quadratic_eq : decode (quadraticBits 0) = quadraticCoefficient 0 := by
  decide +kernel

lemma negative_quadratic_eq (i : Fin 4) :
    decode (quadraticBits (negativeIndex (simpleIndex i))) =
      quadraticCoefficient (negativeIndex (simpleIndex i)) := by
  revert i
  decide +kernel

lemma bits_commute (i : Fin 4) (hi : i ≠ 1) :
    highestLinearBits * negativeLinearBits i = negativeLinearBits i * highestLinearBits ∧
    highestLinearBits * quadraticBits (negativeIndex (simpleIndex i)) =
      quadraticBits (negativeIndex (simpleIndex i)) * highestLinearBits ∧
    quadraticBits 0 * negativeLinearBits i = negativeLinearBits i * quadraticBits 0 ∧
    quadraticBits 0 * quadraticBits (negativeIndex (simpleIndex i)) =
      quadraticBits (negativeIndex (simpleIndex i)) * quadraticBits 0 := by
  revert i
  decide +kernel

lemma coefficients_commute (i : Fin 4) (hi : i ≠ 1) :
    Commute (linearCoefficient 0) (linearCoefficient (negativeIndex (simpleIndex i))) ∧
    Commute (linearCoefficient 0) (quadraticCoefficient (negativeIndex (simpleIndex i))) ∧
    Commute (quadraticCoefficient 0) (linearCoefficient (negativeIndex (simpleIndex i))) ∧
    Commute (quadraticCoefficient 0) (quadraticCoefficient (negativeIndex (simpleIndex i))) := by
  obtain ⟨hll, hlq, hql, hqq⟩ := bits_commute i hi
  have hd {A B : BinaryRows} (h : A * B = B * A) : Commute (decode A) (decode B) := by
    change Mul.mul (decode A) (decode B) = Mul.mul (decode B) (decode A)
    exact (decode_mul A B).symm.trans ((congrArg decode h).trans (decode_mul B A))
  rw [← highest_linear_eq, ← negative_linear_eq, ← highest_quadratic_eq,
    ← negative_quadratic_eq]
  exact ⟨hd hll, hd hlq, hd hql, hd hqq⟩

variable {F : Type*} [CommRing F] [CharP F 2]

lemma matrixCurve_highest_commute_negative (i : Fin 4) (hi : i ≠ 1) (t u : F) :
    Commute (matrixCurve 0 t) (matrixCurve (negativeIndex (simpleIndex i)) u) := by
  obtain ⟨hll, hlq, hql, hqq⟩ := coefficients_commute i hi
  have hc {A B : Matrix Index Index (ZMod 2)} (h : Commute A B) (s v : F) :
      Commute (s • (scalarMap F).mapMatrix A) (v • (scalarMap F).mapMatrix B) :=
    ((h.map (scalarMap F).mapMatrix).smul_left s).smul_right v
  unfold matrixCurve
  apply Commute.add_left
  · apply Commute.add_left
    · exact Commute.one_left _
    · exact ((Commute.one_right _).add_right (hc hll t u)).add_right (hc hlq t (u ^ 2))
  · exact ((Commute.one_right _).add_right (hc hql (t ^ 2) u)).add_right
      (hc hqq (t ^ 2) (u ^ 2))

lemma negativeMatrix_reindex (i : Fin 4) (t : F) :
    Matrix.reindexRingEquiv F latticeEnumeration.symm
      (RootPairing.SimpleGeckGroup.negativeMatrix (typeDRootPairing_baseEquiv 2 i) t) =
        matrixCurve (negativeIndex (simpleIndex i)) t := by
  have hc (d : Fin 4) :
      Matrix.reindexRingEquiv F latticeEnumeration.symm
        (specializeMatrix (fDividedPower (typeDRootPairing_baseEquiv 2 i) d)) =
      (scalarMap F).mapMatrix (dividedCoefficient (negativeIndex (simpleIndex i)) d) := by
    rw [← fDividedPower_binary i d]
    ext r s
    exact (map_intCast (scalarMap F) _).symm
  rw [RootPairing.SimpleGeckGroup.negativeMatrix_formula]
  have hr (s : F) (M : Matrix LatticeIndex LatticeIndex F) :
      Matrix.reindexRingEquiv F latticeEnumeration.symm (s • M) =
        s • Matrix.reindexRingEquiv F latticeEnumeration.symm M := rfl
  simp only [map_add, map_one, hr]
  have hc' (d : Fin 4) :
      Matrix.reindexRingEquiv F latticeEnumeration.symm
        ((fDividedPower (typeDRootPairing_baseEquiv 2 i) d).map (Int.castRingHom F)) =
      (scalarMap F).mapMatrix (dividedCoefficient (negativeIndex (simpleIndex i)) d) := hc d
  rw [hc' ⟨1, by decide⟩, hc' ⟨2, by decide⟩, hc' ⟨3, by decide⟩]
  simp [dividedCoefficient, matrixCurve]

public theorem highestCurve_commute_negativeRoot (P : Parameters) (hp : P.prime = 2)
    (i : Fin 4) (hi : i ≠ 1) (s t : ExtensionField P) :
    Commute (curve P 11 s) (Parabolics.negativeRoot P i t) := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstance
  apply UnipotentMatrices.matrixHom_injective P
  rw [map_mul, map_mul, UnipotentMatrices.matrixHom_curve P hp]
  have hn : UnipotentMatrices.matrixHom P (Parabolics.negativeRoot P i t) =
      matrixCurve (negativeIndex (simpleIndex i)) t := negativeMatrix_reindex i t
  rw [hn]
  exact (matrixCurve_highest_commute_negative i hi s t).eq

end
end Triality.Standard.RadicalCoordinates.Centers.UnipotentLevi
