module

public import Theory.SpecificGroups.ONan.ProjectiveOrder.CosetIndex.LowerBound.OrbitTree
public import Theory.LinearAlgebra.Matrix.ReducedRowSpace

/-!
# Packed input for the fixed-plane orbit certificate

The orbit producer in `../source/GenerateOrbit.py` writes base-eight rows,
least significant digit first. This module fixes their mathematical decoding
and the common input interface for the independent edge and distinctness
checks. No property of external data is assumed. Reduced row bases connect
matrix distinctness to row-space distinctness, even with varying pivot patterns.
-/

@[expose] public section

namespace ONan.OrderCertificate

private lemma eq_of_base_eight_digits (n a b : ℕ)
    (ha : a < 8 ^ n) (hb : b < 8 ^ n)
    (h : ∀ j : Fin n, a / 8 ^ j.val % 8 = b / 8 ^ j.val % 8) : a = b := by
  induction n generalizing a b with
  | zero => simp only [pow_zero] at ha hb; omega
  | succ n ih =>
    have ha' : a / 8 < 8 ^ n := by
      rw [Nat.div_lt_iff_lt_mul (by decide)]
      simpa [pow_succ] using ha
    have hb' : b / 8 < 8 ^ n := by
      rw [Nat.div_lt_iff_lt_mul (by decide)]
      simpa [pow_succ] using hb
    have hab : a / 8 = b / 8 := ih _ _ ha' hb' (fun j => by
      simpa only [Nat.div_div_eq_div_mul, ← pow_succ', Fin.val_succ] using h j.succ)
    have hmod : a % 8 = b % 8 := by simpa using h 0
    omega

/-- Decode a base-eight row, reducing each extracted digit in the field of seven elements. -/
def decodeOrbitRow {n : ℕ} (a : ℕ) (j : Fin n) : ZMod 7 :=
  (a / 8 ^ j.val % 8 : ℕ)

/-- A bounded base-eight code whose digits are canonical field representatives. -/
def ValidOrbitRowCode (n a : ℕ) : Prop := a < 8 ^ n ∧ ∀ j : Fin n, a / 8 ^ j.val % 8 < 7

/-- Canonical bounded base-eight row codes are determined by their decoded rows. -/
lemma decodeOrbitRow_injective {n a b : ℕ} (ha : ValidOrbitRowCode n a) (hb : ValidOrbitRowCode n b)
    (h : (decodeOrbitRow a : Fin n → ZMod 7) = decodeOrbitRow b) : a = b := by
  apply eq_of_base_eight_digits n a b ha.1 hb.1
  intro j
  have hj := congrArg ZMod.val (congrFun h j)
  simpa only [decodeOrbitRow, ZMod.val_natCast, Nat.mod_eq_of_lt (ha.2 j),
    Nat.mod_eq_of_lt (hb.2 j)] using hj

/-- Numerical input shared by the two independent branches of the tree certificate.
The data alone makes no correctness claim; its properties are proved separately. -/
structure PackedOrbitData where
  rowCode : Fin 122760 → Fin 8 → ℕ
  coefficientCode : Fin 122760 → Fin 8 → ℕ
  pivot : Fin 122760 → Fin 8 → Fin 45
  parent : Fin 122760 → Fin 122760
  letter : Fin 122760 → Bool

namespace PackedOrbitData

/-- The eight rows at each orbit node. -/
def rows (D : PackedOrbitData) (i : Fin 122760) :
    Matrix (Fin 8) (Fin 45) (ZMod 7) :=
  fun r => decodeOrbitRow (D.rowCode i r)

/-- The square change of row coordinates at each tree edge. -/
def coefficient (D : PackedOrbitData) (i : Fin 122760) :
    Matrix (Fin 8) (Fin 8) (ZMod 7) :=
  fun r => decodeOrbitRow (D.coefficientCode i r)

/-- Distinct canonical row codes decode to distinct matrices. -/
theorem rows_injective_of_codes (D : PackedOrbitData)
    (valid : ∀ i r, ValidOrbitRowCode 45 (D.rowCode i r))
    (distinct : Function.Injective D.rowCode) : Function.Injective D.rows := by
  intro i j h
  apply distinct
  funext r
  exact decodeOrbitRow_injective (valid i r) (valid j r) (congrFun h r)

/-- A strictly sorted enumeration of the first row codes certifies all matrix distinctness.
No separate permutation certificate is needed: strictness implies the ordering map is
injective, hence surjective on the finite index type. -/
lemma rows_injective_of_sorted_first_rows (D : PackedOrbitData)
    (order : Fin 122760 → Fin 122760)
    (valid : ∀ i, ValidOrbitRowCode 45 (D.rowCode i 0))
    (sorted : StrictMono (fun i => D.rowCode (order i) 0)) : Function.Injective D.rows := by
  have horder : Function.Injective order := fun a b h =>
    sorted.injective (congrArg (fun i => D.rowCode i 0) h)
  have hsurj := Finite.surjective_of_injective horder
  intro i j h
  obtain ⟨a, rfl⟩ := hsurj i
  obtain ⟨b, rfl⟩ := hsurj j
  apply congrArg order
  apply sorted.injective
  exact decodeOrbitRow_injective (valid _) (valid _) (congrFun h 0)

/-- Reduced bases have independent rows by their identity minors. -/
theorem independent (D : PackedOrbitData)
    (h : ∀ i, Matrix.IsReducedRowBasis (D.rows i) (D.pivot i)) (i : Fin 122760) :
    Function.Injective (D.rows i).vecMul :=
  RowSpaces.vecMul_injective_of_pivots _ _ (h i).identity_minor

/-- Distinct reduced matrices represent distinct row spaces. -/
theorem distinct (D : PackedOrbitData)
    (h : ∀ i, Matrix.IsReducedRowBasis (D.rows i) (D.pivot i))
    (hinj : Function.Injective D.rows) :
    Function.Injective (fun i => LinearMap.range (D.rows i).vecMulLinear) := by
  let : Fact (1 < 7) := ⟨by decide⟩
  exact Matrix.range_vecMulLinear_injective_of_reduced D.rows D.pivot h hinj

end PackedOrbitData
end ONan.OrderCertificate
