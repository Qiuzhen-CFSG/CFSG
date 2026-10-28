module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.MiddleTwo.Arithmetic

/-!
# Bounded checks for four literal middle products

A Boolean checker compares corresponding packed rows using the proved
`MiddleTwo.product` accumulator. Its soundness theorem keeps the original
row ordering and both coefficient planes. Slicing the two literal matrices
into sixteen-row blocks bounds each kernel computation; `block_sound`
transports a successful block back to its original matrix row.

The consumers are gates 26--29 of `LongWords/source/circuit.json` for the
unchanged HSG1-f4r896aB0 data. See `Lower/source/README.md` for provenance.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.MiddleTwo.Lower
open Certificates Packed

def check (b : Mat) : Mat → Mat → Bool
  | [], [] => true
  | a::as, c::cs => (product a.1 a.2 b 0 0 == c) && check b as cs
  | _, _ => false

private theorem check_sound (a b c : Mat) (h : check b a c = true) :
    ∀ r, r < a.length → rowProduct (a.getD r (0,0)) b = c.getD r (0,0) := by
  induction a generalizing c with
  | nil => simp
  | cons a as ih =>
    cases c with
    | nil => simp [check] at h
    | cons c cs =>
      simp only [check, Bool.and_eq_true, beq_iff_eq] at h
      intro r hr
      cases r with
      | zero => simpa only [List.getD_cons_zero, rowProduct_eq] using h.1
      | succ r =>
        simpa only [List.getD_cons_succ] using ih cs h.2 r (by simpa using hr)

theorem block_sound (a b c : Mat) (k n : Nat)
    (h : check b ((a.drop n).take k) ((c.drop n).take k) = true)
    (ha : a.length = 896) (r : Nat) (hr : n ≤ r) (hk : r < n+k) (hb : r < 896) :
    rowProduct (a.getD r (0,0)) b = c.getD r (0,0) := by
  have hlt : r-n < k := by omega
  have hh : r-n < ((a.drop n).take k).length := by simp [ha]; omega
  have he := check_sound _ _ _ h (r-n) hh
  simpa only [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hlt,
    List.getElem?_drop, Nat.add_sub_of_le hr] using he

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.MiddleTwo.Lower
