module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density518.Data
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density518.Projection
public import Theory.Representation.HigmanSims.LargeModels.Binary.Assembly

/-!
# Literal word and orbit interfaces for degree-518 density

Words multiply in the printed left-to-right order, with false denoting A and
true denoting B. Prepending a letter acts on columns; appending one acts on
rows. Thus the two independently checkable orbit families use the conventions
of `Binary/source/density518.json` without a hidden transpose or reversal.
The inverse lemmas below turn their literal basis certificates into the span
hypotheses of the rank-one density criterion.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density518
open Matrix

/-- The algebra whose fullness is required by `MatrixAlgebraFull 2`. -/
def Q : Subalgebra (ZMod 2) Matrix518 := Algebra.adjoin (ZMod 2) {A, B}

/-- Generator words in the order used by the source matrices. -/
def word : List Bool → Matrix518
  | [] => 1
  | b :: w => (if b then B else A) * word w

theorem word_append (s t : List Bool) : word (s ++ t) = word s * word t := by
  induction s with
  | nil => simp [word]
  | cons b s ih => simp only [List.cons_append, word, ih, mul_assoc]

theorem word_mem (w : List Bool) : word w ∈ Q := by
  induction w with
  | nil => exact Q.one_mem
  | cons b w ih =>
    apply Q.mul_mem _ ih
    cases b <;> exact Algebra.subset_adjoin (by simp)

/-- The exact four words in the saved density search; no generator relations
have been used to simplify them. -/
def algebraElement : Matrix518 :=
  word [true, true, false, false, false, false] +
  word [true, true, true, false, false] +
  word [false, true, true, false, true, true] + word [false, false]

theorem algebraElement_mem : algebraElement ∈ Q :=
  Q.add_mem (Q.add_mem (Q.add_mem (word_mem _) (word_mem _)) (word_mem _)) (word_mem _)

def columnActor (i : Fin 518) : Matrix518 := word columnWords[i.val]!
def rowActor (i : Fin 518) : Matrix518 := word rowWords[i.val]!

theorem columnActor_mem (i : Fin 518) : columnActor i ∈ Q := word_mem _
theorem rowActor_mem (i : Fin 518) : rowActor i ∈ Q := word_mem _

/-- A checked right inverse spans the literal columns. -/
theorem span_columns_of_inverse
    {k n : Type*} [Field k] [Fintype n] [DecidableEq n]
    (M N : Matrix n n k) (h : M * N = 1) :
    Submodule.span k (Set.range M.col) = ⊤ := by
  rw [← Matrix.range_mulVecLin, LinearMap.range_eq_top]
  intro x
  refine ⟨N.mulVec x, ?_⟩
  change M.mulVec (N.mulVec x) = x
  rw [mulVec_mulVec, h, one_mulVec]

/-- A checked left inverse spans the literal rows. -/
theorem span_rows_of_inverse
    {k n : Type*} [Field k] [Fintype n] [DecidableEq n]
    (M N : Matrix n n k) (h : N * M = 1) :
    Submodule.span k (Set.range M.row) = ⊤ := by
  rw [← range_vecMulLinear, LinearMap.range_eq_top]
  intro x
  refine ⟨vecMul x N, ?_⟩
  change vecMul (vecMul x N) M = x
  rw [vecMul_vecMul, h, vecMul_one]

/-- A right inverse is enough for a square row-basis certificate. -/
theorem span_rows_of_right_inverse
    {k n : Type*} [Field k] [Fintype n] [DecidableEq n]
    (M N : Matrix n n k) (h : M * N = 1) :
    Submodule.span k (Set.range M.row) = ⊤ :=
  span_rows_of_inverse M N (mul_eq_one_comm.mp h)

/-- Consumer of the shared-prefix column transitions and column inverse. -/
theorem column_span_of_certificates
    (horbit : ∀ i, (columnActor i).mulVec u = C.col i) (hinv : C * Ci = 1) :
    Submodule.span (ZMod 2) (Set.range (fun i => (columnActor i).mulVec u)) = ⊤ := by
  simp_rw [horbit]
  exact span_columns_of_inverse C Ci hinv

/-- Consumer of the shared-prefix row transitions and saved right inverse.
Square-matrix one-sided inverse symmetry supplies the left inverse. -/
theorem row_span_of_certificates
    (horbit : ∀ i, vecMul v (rowActor i) = R.row i) (hinv : R * Ri = 1) :
    Submodule.span (ZMod 2) (Set.range (fun i => vecMul v (rowActor i))) = ⊤ := by
  simp_rw [horbit]
  exact span_rows_of_right_inverse R Ri hinv

end Representation.HigmanSims.LargeModels.Binary.Large.Density518
