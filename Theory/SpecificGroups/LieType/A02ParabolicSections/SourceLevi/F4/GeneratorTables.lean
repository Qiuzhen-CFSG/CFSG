module

public import Theory.SpecificGroups.LieType.A02ParabolicSections.SourceLevi.F4.Matrices
public import Theory.SpecificGroups.LieType.A02ParabolicSections.SourceLevi.F4.WordCertificates.Rows

/-!
# The actual integral F4 tables agree with the packed binary generators

Encode each sparse integral row modulo two by XOR of its odd entries.
Induction on the sparse list proves that decoding the packed row is exactly
the matrix reduced modulo two. Eight small row computations then compare
all actual signed simple-root matrices with the finite word certificates.
This avoids expanding every entry of every sparse sum during kernel checking.

Source: the root-operator tables in `F4.Matrices`; GLS3 §1.12 and §2.6,
used for Aschbacher–Smith A.2.18, printed p.40.
-/

public section
open ReeF4.Cartan.FieldSeparation.TraceValues
open Thompson.BinaryMatrix
namespace Theory.SpecificGroups.LieType.SourceLevi.F4.GeneratorTables

private def rowCode (r : Fin 52) : Sparse → ℕ
  | [] => 0
  | e :: a => (if r = e.1 ∧ e.2.2 % 2 = 1 then 2 ^ e.2.1.val else 0) ^^^ rowCode r a

private theorem entry_bit (e : Entry) (r c : Fin 52) :
    bit (if r = e.1 ∧ e.2.2 % 2 = 1 then 2 ^ e.2.1.val else 0) c.val =
      ((Matrix.single e.1 e.2.1 e.2.2 r c : ℤ) : ZMod 2) := by
  rcases e with ⟨i,j,v⟩
  have hv : (v : ZMod 2) = ((v % 2 : ℤ) : ZMod 2) := (ZMod.intCast_mod v 2).symm
  rcases Int.emod_two_eq_zero_or_one v with h | h <;>
    by_cases hr : r = i <;> by_cases hc : c = j <;>
      simp [bit, h, hr, hc, Nat.testBit_two_pow,
        eq_comm, hv]
  exact fun h => hc (Fin.ext h)

private theorem bit_rowCode (a : Sparse) (r c : Fin 52) :
    bit (rowCode r a) c.val = ((matrix a r c : ℤ) : ZMod 2) := by
  induction a with
  | nil => simp [rowCode, bit, matrix]
  | cons e a ih =>
    rw [rowCode, bit_xor, entry_bit, ih, matrix_cons]
    simp

private theorem cast_matrix_eq_decode (a : Sparse) (rows : Array ℕ)
    (h : ∀ r : Fin 52, rowCode r a = rows[r.val]!) :
    (matrix a).map (Int.castRingHom (ZMod 2)) = decode 52 rows := by
  ext r c
  change ((matrix a r c : ℤ) : ZMod 2) = bit rows[r.val]! c.val
  rw [← bit_rowCode, h]

theorem integer_cast_decode (j : Fin 8) :
    (Matrices.integerGenerator j).map (Int.castRingHom (ZMod 2)) =
      decode 52 (WordCertificates.generatorRows j) := by
  fin_cases j <;> apply cast_matrix_eq_decode <;> decide +kernel +revert

end Theory.SpecificGroups.LieType.SourceLevi.F4.GeneratorTables
