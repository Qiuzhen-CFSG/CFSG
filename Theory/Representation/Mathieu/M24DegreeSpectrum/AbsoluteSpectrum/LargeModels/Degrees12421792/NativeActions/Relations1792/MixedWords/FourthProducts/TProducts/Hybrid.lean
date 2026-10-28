module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.Arithmetic

/-!
# Basis-vector selection in the two-product row checker

A binary basis-vector row selects exactly one row of the right matrix.
Every other row is evaluated by the existing certified base-2048 arithmetic.
This specialization avoids repeated widening arithmetic for the sparse X
rows without changing any matrix data. `TProducts.t_product` is the concrete
consumer. Source: ATLAS M24G1-P1; see `TProducts/source/README.md`.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TProducts.Hybrid
open scoped BigOperators
open Thompson.BinaryMatrix
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.Arithmetic

/-- A basis-vector row selects one binary row; other rows use the widened checker. -/
def row (a : Nat) (ys : List Nat) (ws : List (List Nat)) : Nat :=
  if a = 2^a.log2 ∧ a.log2 < 1792 then ys[a.log2]! else Arithmetic.row a ws

theorem selected_row (a : Nat) (ys : List Nat) (k j : Fin 1792) (ha : a = 2^k.val) :
    (∑ i : Fin 1792, bit a i.val * bit ys[i.val]! j.val) = bit ys[k.val]! j.val := by
  subst a
  have hb (i : Fin 1792) : bit (2^k.val) i.val = if i = k then 1 else 0 := by
    simp [bit, Nat.testBit_two_pow, Fin.ext_iff, eq_comm]
  simp [hb]

/-- Apply every hybrid row check to the literal matrix product. -/
theorem product (xs ys zs : List Nat) (ws : List (List Nat))
    (hx : xs.length = 1792) (hy : ys.length = 1792)
    (hw : ws.flatten = ys.map (Arithmetic.expandFast 448))
    (hg : ∀ b ∈ ws, b.length = 32)
    (hc : xs.map (fun a => row a ys ws) = zs) :
    decodeRows 1792 xs * decodeRows 1792 ys = decodeRows 1792 zs := by
  ext i j
  have hi := congrArg (fun l : List Nat => l[i.val]?) hc
  have hxi : i.val < xs.length := by simpa only [hx] using i.isLt
  have hzi : i.val < zs.length := by rw [← hc, List.length_map]; exact hxi
  have hr : row xs[i.val]! ys ws = zs[i.val]! := by
    simpa [List.getElem?_map, hxi, hzi] using hi
  change (decodeRows 1792 xs * decodeRows 1792 ys) i j = bit zs[i.val]! j.val
  rw [← hr]
  unfold row
  split
  · rename_i h
    rw [Matrix.mul_apply]
    change (∑ k : Fin 1792, bit xs[i.val]! k.val * bit ys[k.val]! j.val) = _
    exact selected_row _ ys ⟨xs[i.val]!.log2, h.2⟩ j h.1
  · exact Arithmetic.matrix_row xs ys ws hx hy hw hg i j

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TProducts.Hybrid
