module

public import Theory.SpecificGroups.Triality.PositiveRootCoordinates.Collection.SumExchange.Data

/-!
# Polynomial sum exchanges on the full binary D₄ lattice

For each of the 32 ordered positive root-sum triples, the linear and quadratic
coefficient matrices satisfy thirteen identities. These identities give the
exchange formula by expansion over any characteristic-two commutative ring;
in particular they give an identity in two independent polynomial variables.

The finite verification retains all four Cartan and all 24 root coordinates.
We encode each binary matrix row by a natural number. Decoding preserves zero,
addition (exclusive-or) and matrix multiplication, and kernel-checked finite
computations identify these rows with the coefficients published in `Data`.
The symbolic expansion then accounts for every quadratic cross term.

This is the coefficient-matrix ingredient of the positive-root collection in
GLS3 2.3.6–7 and the Chevalley construction in §§2.4–2.6
(`refs/KGroup/GLS3/chapter2.tex`). Comparison with canonical root operators is
separate from this polynomial identity.
-/

noncomputable section
open scoped BigOperators

namespace Triality.Standard.PositiveCoordinates.SumExchangeData
namespace PolynomialExchangeProof

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

/-- Row encodings, certified against the published matrices by `linear_eq`. -/
def linearBits : Fin 12 → BinaryRows :=
  ![⟨Sum.elim ![64, 0, 0, 0]
      ![0, 2, 0, 0, 65536, 131072, 0, 0, 1048576, 2097152, 0, 0, 0, 0, 1024, 2048, 0, 0, 16384, 32768, 0, 0, 0, 0]⟩,
    ⟨Sum.elim ![0, 0, 67108864, 0]
      ![0, 0, 0, 0, 4096, 0, 16384, 0, 0, 512, 0, 2048, 1048576, 0, 4194304, 0, 0, 131072, 0, 524288, 0, 2, 0, 0]⟩,
    ⟨Sum.elim ![0, 0, 0, 134217728]
      ![0, 0, 0, 0, 8192, 0, 32768, 0, 512, 0, 2048, 0, 2097152, 0, 8388608, 0, 131072, 0, 524288, 0, 2, 0, 0, 0]⟩,
    ⟨Sum.elim ![0, 262144, 0, 0]
      ![256, 0, 1024, 0, 0, 32, 0, 128, 0, 0, 0, 0, 0, 13, 0, 0, 16777216, 33554432, 0, 0, 0, 0, 4194304, 8388608]⟩,
    ⟨Sum.elim ![1024, 1024, 0, 0]
      ![65536, 262144, 0, 0, 0, 15, 0, 0, 16777216, 33554432, 0, 0, 0, 64, 0, 128, 0, 0, 0, 0, 0, 0, 16384, 32768]⟩,
    ⟨Sum.elim ![0, 4194304, 4194304, 0]
      ![4096, 0, 16384, 0, 0, 0, 0, 0, 0, 32, 0, 128, 16777216, 67108864, 0, 0, 0, 15, 0, 0, 0, 262144, 0, 524288]⟩,
    ⟨Sum.elim ![0, 8388608, 0, 8388608]
      ![8192, 0, 32768, 0, 0, 0, 0, 0, 32, 0, 128, 0, 33554432, 134217728, 0, 0, 15, 0, 0, 0, 262144, 0, 524288, 0]⟩,
    ⟨Sum.elim ![16384, 16384, 16384, 0]
      ![1048576, 4194304, 0, 0, 16777216, 67108864, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0, 64, 0, 128, 0, 1024, 0, 2048]⟩,
    ⟨Sum.elim ![0, 524288, 524288, 524288]
      ![512, 0, 2048, 0, 32, 0, 128, 0, 0, 0, 0, 0, 13, 0, 0, 0, 67108864, 134217728, 0, 0, 4194304, 8388608, 0, 0]⟩,
    ⟨Sum.elim ![32768, 32768, 0, 32768]
      ![2097152, 8388608, 0, 0, 33554432, 134217728, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0, 64, 0, 128, 0, 1024, 0, 2048, 0]⟩,
    ⟨Sum.elim ![2048, 2048, 2048, 2048]
      ![131072, 524288, 0, 0, 15, 0, 0, 0, 67108864, 134217728, 0, 0, 64, 0, 128, 0, 0, 0, 0, 0, 16384, 32768, 0, 0]⟩,
    ⟨Sum.elim ![128, 0, 128, 128]
      ![2, 0, 0, 0, 262144, 524288, 0, 0, 4194304, 8388608, 0, 0, 1024, 2048, 0, 0, 16384, 32768, 0, 0, 0, 0, 0, 0]⟩]

def quadraticBits (i : Fin 12) : BinaryRows :=
  ⟨fun r => if r = .inr (positiveIndex i) then 2 ^ (4 + (negativeIndex (positiveIndex i)).val) else 0⟩

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1000000 in
lemma linear_eq (i : Fin 12) : decode (linearBits i) = linearCoefficient (positiveIndex i) := by
  revert i
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1000000 in
lemma quadratic_eq (i : Fin 12) : decode (quadraticBits i) = quadraticCoefficient (positiveIndex i) := by
  revert i
  decide +kernel

/-- Coefficient identities sufficient for the full two-variable exchange. -/
def CoefficientRelations {M : Type*} [Zero M] [Add M] [Mul M] (A P B Q C R : M) : Prop :=
  A * B = B * A + C ∧
  A * Q = Q * A + B * C ∧
  P * B = B * P + A * C ∧
  P * Q = 0 ∧ Q * P = 0 ∧
  P * C = 0 ∧ Q * C = 0 ∧
  A * R = 0 ∧ B * R = 0 ∧ P * R = 0 ∧ Q * R = 0 ∧
  B * (A * C) = R ∧ Q * (A * C) = 0

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1000000 in
lemma bit_relations : ∀ t ∈ sumTriples,
    CoefficientRelations (linearBits t.1) (quadraticBits t.1)
      (linearBits t.2.1) (quadraticBits t.2.1)
      (linearBits t.2.2) (quadraticBits t.2.2) := by
  unfold CoefficientRelations
  decide +kernel

lemma algebra_exchange {F : Type*} [CommRing F] [CharP F 2]
    (A P B Q C R : Matrix Index Index F) (h : CoefficientRelations A P B Q C R)
    (x y : F) :
    (1 + x • A + x ^ 2 • P) * (1 + y • B + y ^ 2 • Q) =
      (1 + y • B + y ^ 2 • Q) * (1 + x • A + x ^ 2 • P) *
        (1 + (x * y) • C + (x * y) ^ 2 • R) := by
  obtain ⟨hab, haq, hpb, hpq, hqp, hpc, hqc, har, hbr, hpr, hqr, hbac, hqac⟩ := h
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    one_mul, mul_one]
  simp only [mul_assoc, hab, haq, hpb, hpq, hqp, hpc, hqc, har, hbr, hpr,
    hqr, hbac, hqac, mul_zero, smul_zero, add_zero, zero_add, smul_add]
  ext r s
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring_nf
  simp [CharTwo.two_eq_zero]

lemma map_relations {M N : Type*} [Zero M] [Add M] [Mul M] [Zero N] [Add N] [Mul N]
    (f : M → N) (hzero : f 0 = 0)
    (hadd : ∀ a b, f (a + b) = f a + f b)
    (hmul : ∀ a b, f (a * b) = f a * f b)
    (A P B Q C R : M) (h : CoefficientRelations A P B Q C R) :
    CoefficientRelations (f A) (f P) (f B) (f Q) (f C) (f R) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨by simpa only [hmul, hadd] using congrArg f h1,
    by simpa only [hmul, hadd] using congrArg f h2,
    by simpa only [hmul, hadd] using congrArg f h3,
    by simpa only [hmul, hzero] using congrArg f h4,
    by simpa only [hmul, hzero] using congrArg f h5,
    by simpa only [hmul, hzero] using congrArg f h6,
    by simpa only [hmul, hzero] using congrArg f h7,
    by simpa only [hmul, hzero] using congrArg f h8,
    by simpa only [hmul, hzero] using congrArg f h9,
    by simpa only [hmul, hzero] using congrArg f h10,
    by simpa only [hmul, hzero] using congrArg f h11,
    by simpa only [hmul] using congrArg f h12,
    by simpa only [hmul, hzero] using congrArg f h13⟩

lemma binary_relations (i j k : Fin 12) (h : (i, j, k) ∈ sumTriples) :
    CoefficientRelations (linearCoefficient (positiveIndex i)) (quadraticCoefficient (positiveIndex i))
      (linearCoefficient (positiveIndex j)) (quadraticCoefficient (positiveIndex j))
      (linearCoefficient (positiveIndex k)) (quadraticCoefficient (positiveIndex k)) := by
  rw [← linear_eq i, ← quadratic_eq i, ← linear_eq j, ← quadratic_eq j,
    ← linear_eq k, ← quadratic_eq k]
  exact map_relations (M := BinaryRows) (N := Matrix Index Index (ZMod 2))
    decode decode_zero decode_add decode_mul
    (linearBits i) (quadraticBits i) (linearBits j) (quadraticBits j)
    (linearBits k) (quadraticBits k) (bit_relations (i, j, k) h)

end PolynomialExchangeProof

open PolynomialExchangeProof in
open Triality.Standard.Parabolics.RankOneMatrices in
/-- The full D₄ coefficient matrices obey the sum exchange as a polynomial
identity, including the Cartan entries and all quadratic terms. -/
public theorem polynomial_exchange (i j k : Fin 12)
    (h : rootCoords (positiveIndex k) = rootCoords (positiveIndex i) + rootCoords (positiveIndex j)) :
    polynomialCurve (positiveIndex i) 0 * polynomialCurve (positiveIndex j) 1 =
      polynomialCurve (positiveIndex j) 1 * polynomialCurve (positiveIndex i) 0 *
        matrixCurve (positiveIndex k) ((MvPolynomial.X 0 : PolynomialRing) * MvPolynomial.X 1) := by
  exact algebra_exchange _ _ _ _ _ _
    (map_relations (scalarMap PolynomialRing).mapMatrix (map_zero _) (map_add _) (map_mul _)
      _ _ _ _ _ _ (binary_relations i j k ((mem_sumTriples_iff i j k).mpr h))) _ _

end Triality.Standard.PositiveCoordinates.SumExchangeData
