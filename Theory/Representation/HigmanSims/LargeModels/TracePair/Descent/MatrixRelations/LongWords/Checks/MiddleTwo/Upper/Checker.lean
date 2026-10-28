module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.MiddleTwo.Arithmetic

/-!
# Bounded certificates for the upper middle HS products

The accumulator applies each GF(4) scalar in one step, using
`omega * omega = omega + 1`. Its equality with the established two-plane
accumulator is proved for arbitrary packed inputs, then `rowProduct_eq`
connects every Boolean check to the literal matrix product. Small consecutive
ranges bound the numerical reductions; they are proved in the gate modules.

Source: the unchanged HSG1-f4r896aB0 matrices and
`LongWords/source/circuit.json`. See `Upper/source/README.md` for measurements.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.MiddleTwo.Upper
open Certificates Packed

def accumulate : Nat → Nat → Mat → Nat → Nat → Row
  | _, _, [], p, q => (p, q)
  | x, y, (u,v)::bs, p, q =>
    forceNat (x / 2) fun xx => forceNat (y / 2) fun yy =>
    let next := fun s t => forceNat s fun ss => forceNat t fun tt => accumulate xx yy bs ss tt
    if x % 2 = 1 then
      if y % 2 = 1 then next (p ^^^ (u ^^^ v)) (q ^^^ u)
      else next (p ^^^ u) (q ^^^ v)
    else
      if y % 2 = 1 then next (p ^^^ v) (q ^^^ (u ^^^ v))
      else next p q

private theorem force_eq {α : Sort*} (n : Nat) (f : Nat → α) : forceNat n f = f n := by
  cases n <;> rfl

private theorem accumulate_eq (x y : Nat) (bs : Mat) (p q : Nat) :
    accumulate x y bs p q = product x y bs p q := by
  induction bs generalizing x y p q with
  | nil => rfl
  | cons b bs ih =>
    rcases b with ⟨u,v⟩
    simp only [accumulate, product, force_eq]
    by_cases hx : x % 2 = 1 <;> by_cases hy : y % 2 = 1 <;>
      simp only [hx, hy, if_true, if_false, ih]
    congr 1
    · exact (Nat.xor_assoc p u v).symm
    · calc
        q ^^^ u = q ^^^ (u ^^^ (v ^^^ v)) := by rw [Nat.xor_self, Nat.xor_zero]
        _ = (q ^^^ v) ^^^ (u ^^^ v) := by ac_rfl

def checkAt (i : Fin 46) (r : Nat) : Bool :=
  match accumulate ((rowsAt (inputs i).1).getD r (0,0)).1
      ((rowsAt (inputs i).1).getD r (0,0)).2 (rowsAt (inputs i).2) 0 0,
      (rowsAt (i.val+2)).getD r (0,0) with
  | (p,q), (u,v) => p == u && q == v

def checkRange (i : Fin 46) (start count : Nat) : Bool :=
  (List.range count).all (fun r => checkAt i (start+r))


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

private theorem eq_of_test (a b : Row)
    (h : (match a, b with | (p,q), (u,v) => p == u && q == v) = true) : a = b := by
  rcases a with ⟨p,q⟩
  rcases b with ⟨u,v⟩
  simpa only [Bool.and_eq_true, beq_iff_eq, Prod.mk.injEq] using h

theorem row_eq_of_check (i : Fin 46) (r : Nat) (h : checkAt i r = true) :
    rowProduct ((rowsAt (inputs i).1).getD r (0,0)) (rowsAt (inputs i).2) =
      (rowsAt (i.val+2)).getD r (0,0) := by
  have he := eq_of_test _ _ h
  rw [accumulate_eq, rowProduct_eq] at he
  exact he

theorem productCheck_of_checked (i : Fin 46) (h : CheckedRange i 0 896) :
    ProductCheck i := by
  apply productCheck_of_rows
  intro r
  exact row_eq_of_check i r.val (h r.val (Nat.zero_le _) r.isLt)

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.MiddleTwo.Upper
