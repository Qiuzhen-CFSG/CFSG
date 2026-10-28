module

public import Theory.SpecificGroups.Lyons.Atlas111LocalIndexPlaneOrbitArithmetic.Data
public import Theory.SpecificGroups.Lyons.Atlas111LocalIndexPlaneOrbit

/-!
# Kernel-checked transitions in the concrete Lyons plane orbit

The producer stores seven base-eight columns and seven rows of a coefficient
matrix K. The decoder uses those columns for U and V, and K.transpose for C.
`checkEdge_sound` proves the actual equation G * U = V * C. Each product column
is computed with one carry-free packed linear combination, using the checked
word arithmetic rather than 111 separate dot products. `checkBatch_sound`
allows independent batches of closed checks without any orbit-size assumption.

Source format and orientation: `Atlas111PlaneOrbitSource/README.md` and
`GenerateOrbit.py`. Numeric generator conversion: the descendant `Data` module.
-/

@[expose] public section
namespace Lyons.OrderCertificate.PlaneOrbitArithmetic
open Atlas111WordCertificate Atlas111Certificate Matrix

/-- The seven producer rows are columns of the Lean matrix. -/
def decodeColumns (u : Fin 7 → ℕ) : Matrix (Fin 111) (Fin 7) (ZMod 5) :=
  fun i j => (digit8 (u j) i : ZMod 5)

/-- The producer's coefficient rows encode K; the edge uses its transpose. -/
def decodeCoefficient (k : Fin 7 → ℕ) : Matrix (Fin 7) (Fin 7) (ZMod 5) :=
  fun i j => (digit8 (k j) i : ZMod 5)

theorem decodeCoefficient_transpose (k : Fin 7 → ℕ) :
    decodeCoefficient k = (fun i j : Fin 7 => (digit8 (k i) j : ZMod 5))ᵀ := rfl

private theorem ofNat_val {n : ℕ} [NeZero n] (i : Fin n) : Fin.ofNat n i.val = i := by
  ext
  exact Nat.mod_eq_of_lt i.isLt

theorem generatorEntry_cast (b : Bool) (i k : Fin 111) :
    (generatorEntry b k i : ZMod 5) = matrixRepresentation (indexGenerator b) i k := by
  cases b <;> simp only [generatorEntry, Bool.false_eq_true, ↓reduceIte, ofNat_val,
    ZMod.natCast_mod, indexGenerator, matrixRepresentation_generatorA,
    matrixRepresentation_generatorB, atlasAMatrix, atlasBMatrix]

/-- A packed generator product computes a full output column. -/
theorem generatorProduct_entry (b : Bool) (u : Fin 7 → ℕ) (i : Fin 111) (j : Fin 7) :
    (digit (combine (generatorColumns b) (u j) 111) i : ZMod 5) =
      (matrixRepresentation (indexGenerator b) * decodeColumns u) i j := by
  rw [combine_digit 111 111 4 _ (generatorEntry b) _
    (generatorColumns_eq_encode b) (fun k _ r _ => generatorEntry_le b k r) (by decide) i i.isLt]
  simp only [Nat.cast_sum, Nat.cast_mul, generatorEntry_cast, Matrix.mul_apply, decodeColumns]
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

/-- Coordinate multiplication is a combination of the seven widened columns. -/
theorem coordinateProduct_entry (v k : Fin 7 → ℕ) (i : Fin 111) (j : Fin 7) :
    (digit (combine (fun r => widen 111 (v (Fin.ofNat 7 r))) (k j) 7) i : ZMod 5) =
      (decodeColumns v * decodeCoefficient k) i j := by
  rw [combine_digit 111 7 7 _ (fun r => digit8 (v (Fin.ofNat 7 r))) _
    (fun r _ => widen_eq_encode 111 _) (fun r _ s _ => digit8_le _ s) (by decide) i i.isLt]
  simp only [Nat.cast_sum, Nat.cast_mul, ofNat_val, Matrix.mul_apply,
    decodeColumns, decodeCoefficient]
  apply Finset.sum_congr rfl
  intro r _
  exact mul_comm _ _

/-- Check one of the seven output columns. -/
def checkColumn (b : Bool) (u : ℕ) (v : Fin 7 → ℕ) (k : ℕ) : Bool :=
  residuesEq 111 (combine (generatorColumns b) u 111)
    (combine (fun r => widen 111 (v (Fin.ofNat 7 r))) k 7)

/-- The executable edge checker reads the producer's data directly. -/
def checkEdge (b : Bool) (u v k : Fin 7 → ℕ) : Bool :=
  allBelow 7 fun j => checkColumn b (u (Fin.ofNat 7 j)) v (k (Fin.ofNat 7 j))

/-- Soundness has exactly the orientation required by `SeparationPlaneOrbitTree.edge`. -/
theorem checkEdge_sound (b : Bool) (u v k : Fin 7 → ℕ) (h : checkEdge b u v k = true) :
    matrixRepresentation (indexGenerator b) * decodeColumns u =
      decodeColumns v * decodeCoefficient k := by
  ext i j
  have hj := allBelow_sound h j.val j.isLt
  simp only [ofNat_val] at hj
  have he := residuesEq_sound _ _ _ hj i.val i.isLt
  exact (generatorProduct_entry b u i j).symm.trans
    (he.trans (coordinateProduct_entry v k i j))

/-- One producer transition, independent of any complete orbit dataset. -/
structure EdgeInput where
  letter : Bool
  parent : Fin 7 → ℕ
  child : Fin 7 → ℕ
  coefficient : Fin 7 → ℕ

/-- Batches can be independently kernel-checked and assembled without reevaluation. -/
def checkBatch (n : ℕ) (edges : ℕ → EdgeInput) : Bool :=
  allBelow n fun i => checkEdge (edges i).letter (edges i).parent
    (edges i).child (edges i).coefficient

theorem checkBatch_sound (n : ℕ) (edges : ℕ → EdgeInput) (h : checkBatch n edges = true)
    (i : ℕ) (hi : i < n) :
    matrixRepresentation (indexGenerator (edges i).letter) * decodeColumns (edges i).parent =
      decodeColumns (edges i).child * decodeCoefficient (edges i).coefficient :=
  checkEdge_sound _ _ _ _ (allBelow_sound h i hi)
end Lyons.OrderCertificate.PlaneOrbitArithmetic
