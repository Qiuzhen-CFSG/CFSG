module
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density518.Columns.Transpose
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density518.Columns.Products
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density518.Columns.Metadata
/-!
# The spanning degree-518 column orbit

The exact saved column tree starts at u and prepends A or B at every edge.
Certified packed transposes convert the row calculations into these literal
left-generator steps. The checked right inverse C*Ci=1 proves that the resulting
columns span the full vector space. Shared-prefix induction identifies them
with the original `columnActor` words.

This supplies the column premise of the rank-one density criterion; the
rank-one operator and row-span premises retain their separate owners.
Source: R. A. Wilson et al., ATLAS HSG1-f2r518B0 and the unchanged
`Binary/source/density518.json`. See `Columns/source/README.md` for attribution
and reproducible kernel certificates.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density518
open Matrix RowArithmetic
namespace Columns

theorem parent_value (i : Fin 517) : (parent i).val = columnParents[i.val + 1]! := by
  have h := (prefix_checks i).1
  change columnParents[i.val + 1]! % 518 = _
  exact Nat.mod_eq_of_lt (by omega)

theorem parent_lt (i : Fin 517) : parent i < i.succ := by
  change (parent i).val < i.val + 1
  rw [parent_value]
  exact (prefix_checks i).1

theorem prefix_words (i : Fin 517) :
    columnWords[i.succ.val]! = letter i :: columnWords[(parent i).val]! := by
  rw [parent_value]
  exact (prefix_checks i).2

theorem column_vector (i : Fin 518) : C.col i = vector 518 ctRows[i.val]! :=
  (congrArg (fun M : Matrix518 => M i) transpose_c).symm

theorem column_start : C.col 0 = u := by
  rw [column_vector]
  exact congrArg (vector 518) root_packed

theorem inverse : C * Ci = 1 := by
  funext i
  exact decode_product_one_row 518 columnRows columnInverseRows i Blocks.ci_size
    (inverse_checks i)

theorem transition (i : Fin 517) :
    (if letter i then B else A).mulVec (C.col (parent i)) = C.col i.succ := by
  have hp := transition_checks i
  change combine (if columnLetters[1 + i.val]! then btRows else atRows).toList
    ctRows[columnParents[1 + i.val]!]! = ctRows[1 + i.val]! at hp
  rw [Nat.add_comm 1 i.val] at hp
  have hs : (if letter i then btRows else atRows).size = 518 := by
    cases letter i
    · exact at_size
    · exact bt_size
  have h := vector_mul_checked (if letter i then btRows else atRows)
    ctRows[columnParents[i.val+1]!]! ctRows[i.val+1]! hs hp
  rw [column_vector, column_vector, parent_value]
  have ht : Thompson.BinaryMatrix.decode 518 (if letter i then btRows else atRows) =
      (if letter i then B else A).transpose := by
    cases letter i
    · exact transpose_a
    · exact transpose_b
  rw [ht, Matrix.vecMul_transpose] at h
  exact h

end Columns

/-- The literal column words applied to the saved image vector span degree 518. -/
theorem column_span :
    Submodule.span (ZMod 2) (Set.range (fun i => (columnActor i).mulVec u)) = ⊤ :=
  column_span_of_prefix_certificates Columns.parent Columns.letter Columns.parent_lt
    Columns.column_start Columns.prefix_words Columns.transition Columns.inverse


end Representation.HigmanSims.LargeModels.Binary.Large.Density518
