module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.SquareSix.Data
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans.RowChecks.Checker

/-!
# Four fixed products for the sixth-power HS commutator relation

Write U = AB³ and V = AB². The proposed rows C, D, E encode UV, C², DC.
The four independent checks below identify these products and prove E² = I.
All matrices, including the two inputs, are fixed data, so numerical checks
for later products need not wait for the interpretation of earlier products.
The separate assembly discharges every interpretation premise.

The direct coefficient checker is reused from the certified row-orbit
arithmetic. Its equality with `Packed.rowProduct` retains all 896 entries.
Source: the unchanged `Descent/source/HSG1-P1.M`, relation (a,b²)⁶.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.SquareSix
open Certificates
open Certificates.OrbitSpans.RowChecks

def leftRows (i : Fin 4) : Packed.Mat :=
  match i.val with
  | 0 => LongWords.rows07
  | 1 => rowsC
  | 2 => rowsD
  | _ => rowsE

def rightRows (i : Fin 4) : Packed.Mat :=
  match i.val with
  | 0 => LongWords.rows03
  | 1 => rowsC
  | 2 => rowsC
  | _ => rowsE

def resultRows (i : Fin 4) : Packed.Mat :=
  match i.val with
  | 0 => rowsC
  | 1 => rowsD
  | 2 => rowsE
  | _ => LongWords.identityRows

theorem rightRows_length (i : Fin 4) : (rightRows i).length = 896 := by
  unfold rightRows
  split
  · exact LongWords.rows03_length
  · exact rowsC_length
  · exact rowsC_length
  · exact rowsE_length

/-- A full fixed-matrix equality, without invertibility or representation premises. -/
def ProductCheck (i : Fin 4) : Prop :=
  Packed.eval 896 (leftRows i) * Packed.eval 896 (rightRows i) =
    Packed.eval 896 (resultRows i)

def rowCheck (i : Fin 4) (r : ℕ) : Bool :=
  directProductFrom ((leftRows i).getD r (0, 0)) (rightRows i) 0 ==
    (resultRows i).getD r (0, 0)

private theorem eval_product_row {n : ℕ} (a b c : Packed.Mat) (hb : b.length = n)
    (r : Fin n) (hp : Packed.rowProduct (a.getD r.val (0, 0)) b = c.getD r.val (0, 0)) :
    (Packed.eval n a * Packed.eval n b) r = Packed.eval n c r := by
  funext j
  exact (Packed.decode_rowProduct (a.getD r.val (0, 0)) b n hb j.val).symm.trans
    (congrArg (fun v => Packed.decode v j.val) hp)

/-- A bounded check certifies all columns of this row of the actual product. -/
theorem product_row_of_check (i : Fin 4) (r : Fin 896) (h : rowCheck i r.val = true) :
    (Packed.eval 896 (leftRows i) * Packed.eval 896 (rightRows i)) r =
      Packed.eval 896 (resultRows i) r := by
  have hp : Packed.rowProduct ((leftRows i).getD r.val (0, 0)) (rightRows i) =
      (resultRows i).getD r.val (0, 0) := by
    simpa only [rowCheck, directProductFrom_eq, Packed.rowProduct] using eq_of_beq h
  exact eval_product_row _ _ _ (rightRows_length i) r hp

theorem productCheck_of_range (i : Fin 4)
    (h : CheckedRange (rowCheck i) 0 896) : ProductCheck i := by
  apply Packed.eval_product 896 _ _ _ (rightRows_length i)
  intro r
  have he := eq_of_beq (h r.val (Nat.zero_le _) r.isLt)
  simpa only [rowCheck, directProductFrom_eq, Packed.rowProduct] using he

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.SquareSix
