module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.TrivialCalculation.MiddleFactors.Density104.MatrixChecks

/-!
# Spanning translates of the two degree-104 seeds

The saved short words form two rooted orbit trees. Checking each edge needs
one packed vector product. For columns we use the transposed actors, so no
full word matrices or repeated matrix-vector kernel reductions are needed.
Two inverse checks show that the resulting columns and rows are bases.
The rank-one density criterion converts these bases into the full algebra.
Source motivation: Guralnick–Malle Proposition 4.3; Aschbacher–Smith K.2, p.453.
-/

set_option Elab.async false

@[expose] public section
namespace Representation.SU3.FiveSmallModules.Degrees.TrivialCalculation.MiddleFactors.Density104Certificate
open Thompson.BinaryMatrix CycleCertificate
open scoped Matrix

private abbrev Mat := Matrix (Fin 104) (Fin 104) (ZMod 2)
private abbrev Vec := Fin 104 → ZMod 2

/-- Realize every vertex of a rooted column orbit tree inside an actor algebra. -/
private theorem column_realizations (Q : Subalgebra (ZMod 2) Mat)
    (A : Fin 2 → Mat) (hA : ∀ a, A a ∈ Q) (xs : Fin 104 → Vec)
    (p : Fin 103 → Fin 104) (a : Fin 103 → Fin 2)
    (hp : ∀ i, p i < i.succ)
    (hs : ∀ i, A (a i) *ᵥ xs (p i) = xs i.succ) :
    ∀ i, ∃ L : Mat, L ∈ Q ∧ L *ᵥ xs 0 = xs i := by
  intro i
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    cases i using Fin.cases with
    | zero => exact ⟨1, Q.one_mem, Matrix.one_mulVec _⟩
    | succ i =>
      obtain ⟨L, hL, he⟩ := ih (p i) (hp i)
      refine ⟨A (a i) * L, Q.mul_mem (hA _) hL, ?_⟩
      rw [← Matrix.mulVec_mulVec, he, hs i]

/-- The analogous realization for a rooted row orbit tree. -/
private theorem row_realizations (Q : Subalgebra (ZMod 2) Mat)
    (A : Fin 2 → Mat) (hA : ∀ a, A a ∈ Q) (xs : Fin 104 → Vec)
    (p : Fin 103 → Fin 104) (a : Fin 103 → Fin 2)
    (hp : ∀ i, p i < i.succ)
    (hs : ∀ i, xs (p i) ᵥ* A (a i) = xs i.succ) :
    ∀ i, ∃ R : Mat, R ∈ Q ∧ xs 0 ᵥ* R = xs i := by
  intro i
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    cases i using Fin.cases with
    | zero => exact ⟨1, Q.one_mem, Matrix.vecMul_one _⟩
    | succ i =>
      obtain ⟨R, hR, he⟩ := ih (p i) (hp i)
      refine ⟨R * A (a i), Q.mul_mem hR (hA _), ?_⟩
      rw [← Matrix.vecMul_vecMul, he, hs i]

private theorem row_entries (i j : Fin 104) :
    bit rows[i.val]! j.val = decode 104 rows i j := rfl

attribute [local irreducible] factorRows104 transposedActors columnVectors
  columns columnInverse rows rowInverse columnParent rowParent columnActor rowActor
  column row

/-- The checked orbit bases discharge all spanning premises of rank-one density. -/
theorem density_of_seed_mem
    (Q : Subalgebra (ZMod 2) (Matrix (Fin 104) (Fin 104) (ZMod 2)))
    (hA : ∀ a, factor104 a ∈ Q)
    (hcr : Matrix.vecMulVec (fun i : Fin 104 => bit column i.val)
      (fun j : Fin 104 => bit row j.val) ∈ Q) : Q = ⊤ := by
  classical
  have hcs (i : Fin 103) :
      factor104 (columnActor i) *ᵥ (fun j : Fin 104 => bit columnVectors[(columnParent i).val]! j.val) =
        fun j : Fin 104 => bit columnVectors[i.succ.val]! j.val := by
    have h := decode_vecMul 104 (transposedActors (columnActor i))
      columnVectors[(columnParent i).val]! columnVectors[i.succ.val]! (column_step i)
    rw [transposed_actors, Matrix.vecMul_transpose] at h
    exact h
  have hrs (i : Fin 103) :
      (fun j : Fin 104 => bit rows[(rowParent i).val]! j.val) ᵥ* factor104 (rowActor i) =
        fun j : Fin 104 => bit rows[i.succ.val]! j.val :=
    decode_vecMul 104 (factorRows104 (rowActor i)) rows[(rowParent i).val]!
      rows[i.succ.val]! (row_step i)
  choose L hL heL using
    (column_realizations Q factor104 hA (fun i j => bit columnVectors[i.val]! j.val)
      columnParent columnActor column_parent_lt hcs)
  choose R hR heR using
    (row_realizations Q factor104 hA (fun i j => bit rows[i.val]! j.val)
      rowParent rowActor row_parent_lt hrs)
  apply density_of_rank_one Q (fun i : Fin 104 => bit column i.val)
    (fun i : Fin 104 => bit row i.val) hcr L R hL hR
    (decode 104 columns) (decode 104 columnInverse) (decode 104 rows) (decode 104 rowInverse)
    columns_inverse rows_inverse
  · intro i
    have h := heL i
    simp only [Fin.val_zero, column_initial] at h
    exact h.trans (funext (column_entries i))
  · intro i
    have h := heR i
    simp only [Fin.val_zero, row_initial] at h
    exact h.trans (funext (row_entries i))

end Representation.SU3.FiveSmallModules.Degrees.TrivialCalculation.MiddleFactors.Density104Certificate
