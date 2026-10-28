module

public import Theory.SpecificGroups.Lyons.Atlas111LocalIndexPlaneOrbitArithmetic
public import Theory.SpecificGroups.Lyons.Atlas111LocalIndexPlaneOrbitArithmetic.SparseData

/-!
# Sparse involution transitions for the Lyons plane orbit

Ambient A has only 201 nonzero entries and at most two per row. Its column
product therefore needs at most two scalar terms per coordinate. Ambient B
uses the packed full-column arithmetic from the parent module. Both routes
prove exactly the same matrix identity, and `checkFastBatch_sound` assembles
independently checked batches.

Sources: `../Atlas111PlaneOrbitSource/README.md`, `SparseData`, and
`../Atlas111Source/README.md`. No external arithmetic result is trusted.
-/

@[expose] public section
namespace Lyons.OrderCertificate.PlaneOrbitArithmetic
open Atlas111WordCertificate Atlas111Certificate Matrix

def sparseAProduct (u : ℕ) (i : Fin 111) : ℕ :=
  (aSupport1 i).2 * digit8 u (aSupport1 i).1 +
  (aSupport2 i).2 * digit8 u (aSupport2 i).1

theorem sparseAProduct_entry (u : Fin 7 → ℕ) (i : Fin 111) (j : Fin 7) :
    (sparseAProduct (u j) i : ZMod 5) =
      (matrixRepresentation (indexGenerator false) * decodeColumns u) i j := by
  simp only [Matrix.mul_apply, ← generatorEntry_cast, generatorEntry_eq_sparseA,
    sparseAEntry, sparseAProduct, decodeColumns, Nat.cast_add]
  simp [Nat.cast_mul, add_mul, Finset.sum_add_distrib]

def checkSparseAColumn (u : ℕ) (v : Fin 7 → ℕ) (k : ℕ) : Bool :=
  let rhs := combine (fun r => widen 111 (v (Fin.ofNat 7 r))) k 7
  allBelow 111 fun i => sparseAProduct u (Fin.ofNat 111 i) % 5 == digit rhs i % 5

def checkSparseAEdge (u v k : Fin 7 → ℕ) : Bool :=
  allBelow 7 fun j => checkSparseAColumn (u (Fin.ofNat 7 j)) v (k (Fin.ofNat 7 j))

theorem checkSparseAEdge_sound (u v k : Fin 7 → ℕ) (h : checkSparseAEdge u v k = true) :
    matrixRepresentation (indexGenerator false) * decodeColumns u =
      decodeColumns v * decodeCoefficient k := by
  ext i j
  have hj := allBelow_sound h j.val j.isLt
  have hi := allBelow_sound hj i.val i.isLt
  have hi' : Fin.ofNat 111 i.val = i := by ext; exact Nat.mod_eq_of_lt i.isLt
  have hj' : Fin.ofNat 7 j.val = j := by ext; exact Nat.mod_eq_of_lt j.isLt
  simp only [hi', hj', beq_iff_eq] at hi
  have he := congrArg (fun x : ℕ => (x : ZMod 5)) hi
  simp only [ZMod.natCast_mod] at he
  exact (sparseAProduct_entry u i j).symm.trans
    (he.trans (coordinateProduct_entry v k i j))

def checkFastEdge (b : Bool) (u v k : Fin 7 → ℕ) : Bool :=
  if b then checkEdge true u v k else checkSparseAEdge u v k

theorem checkFastEdge_sound (b : Bool) (u v k : Fin 7 → ℕ)
    (h : checkFastEdge b u v k = true) :
    matrixRepresentation (indexGenerator b) * decodeColumns u =
      decodeColumns v * decodeCoefficient k := by
  cases b
  · exact checkSparseAEdge_sound u v k h
  · exact checkEdge_sound true u v k h

def checkFastBatch (n : ℕ) (edges : ℕ → EdgeInput) : Bool :=
  allBelow n fun i => checkFastEdge (edges i).letter (edges i).parent
    (edges i).child (edges i).coefficient

theorem checkFastBatch_sound (n : ℕ) (edges : ℕ → EdgeInput) (h : checkFastBatch n edges = true)
    (i : ℕ) (hi : i < n) :
    matrixRepresentation (indexGenerator (edges i).letter) * decodeColumns (edges i).parent =
      decodeColumns (edges i).child * decodeCoefficient (edges i).coefficient :=
  checkFastEdge_sound _ _ _ _ (allBelow_sound h i hi)
end Lyons.OrderCertificate.PlaneOrbitArithmetic
