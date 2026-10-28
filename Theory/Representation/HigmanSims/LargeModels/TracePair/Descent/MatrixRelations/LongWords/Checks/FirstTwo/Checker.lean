module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Products
/-!
# Direct numerical checks for the first two long HS words

Select coefficient k by division by 2^k, then use the existing proved packed
row operations. `productFrom_eq` connects this evaluator to `Packed.rowProduct`;
consecutive bounded ranges supply every actual row of a product gate.

The direct-division evaluator and bounded-range method follow the completed
`Certificates.OrbitSpans.RowChecks.Checker` development. Source matrices and
field conventions are unchanged: see `TracePair/source/README.md` and
`LongWords/source/README.md`.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.FirstTwo
open Certificates


def productFrom (a : Packed.Row) : Packed.Mat → Nat → Packed.Row
  | [], _ => (0, 0)
  | b :: bs, k => Packed.Base.addRow
      (Packed.Base.addRow (if a.1 / 2^k % 2 = 1 then b else (0, 0))
        (if a.2 / 2^k % 2 = 1 then Packed.Base.timesT b else (0, 0)))
      (productFrom a bs (k + 1))

theorem productFrom_eq (a : Packed.Row) (bs : Packed.Mat) (k : Nat) :
    productFrom a bs k = Packed.rowProductFrom a bs k := by
  induction bs generalizing k with
  | nil => rfl
  | cons b bs ih =>
    simp only [productFrom, Packed.rowProductFrom, ih,
      Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq]

def checkAt (i : Fin 46) (r : Nat) : Bool :=
  productFrom ((rowsAt (inputs i).1).getD r (0,0)) (rowsAt (inputs i).2) 0 ==
    (rowsAt (i.val + 2)).getD r (0,0)

def checkRange (i : Fin 46) (start count : Nat) : Bool :=
  (List.range count).all (fun r => checkAt i (start+r))

/-- Every row in a half-open interval passes the numerical product check. -/
def CheckedRange (i : Fin 46) (start count : Nat) : Prop :=
  ∀ r, start ≤ r → r < start + count → checkAt i r = true

theorem checkedRange_of_check (i : Fin 46) (start count : Nat)
    (h : checkRange i start count = true) : CheckedRange i start count := by
  intro r hlo hhi
  have hr : r - start < count := by omega
  have he : start + (r - start) = r := by omega
  have := List.all_eq_true.mp h (r - start) (List.mem_range.mpr hr)
  simpa only [he] using this

theorem checkedRange_append (i : Fin 46) (start left right : Nat)
    (hl : CheckedRange i start left) (hr : CheckedRange i (start + left) right) :
    CheckedRange i start (left + right) := by
  intro r hlo hhi
  by_cases h : r < start + left
  · exact hl r hlo h
  · exact hr r (by omega) (by omega)

/-- Numerical certificates for all 896 rows prove the original matrix gate. -/
theorem productCheck_of_checkedRange (i : Fin 46) (h : CheckedRange i 0 896) :
    ProductCheck i := by
  apply productCheck_of_rows
  intro r
  have he := eq_of_beq (h r.val (Nat.zero_le _) r.isLt)
  simpa only [checkAt, productFrom_eq, Packed.rowProduct] using he

/-- A checked numerical row gives equality on that row of the literal matrices. -/
theorem row_eq_of_check (i : Fin 46) (r : Fin 896) (h : checkAt i r.val = true) :
    (candidate (inputs i).1 * candidate (inputs i).2) r = candidate (i.val + 2) r := by
  have hp : Packed.rowProduct ((rowsAt (inputs i).1).getD r.val (0, 0))
      (rowsAt (inputs i).2) = (rowsAt (i.val + 2)).getD r.val (0, 0) := by
    simpa only [checkAt, productFrom_eq, Packed.rowProduct] using (eq_of_beq h)
  funext j
  simp only [candidate, Matrix.mul_apply, Packed.eval]
  rw [← Packed.decode_rowProduct _ _ 896 (rowsAt_length _) j.val, hp]

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.FirstTwo
