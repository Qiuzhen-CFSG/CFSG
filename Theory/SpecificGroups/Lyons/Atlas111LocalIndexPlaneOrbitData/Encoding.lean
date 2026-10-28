module

public import Theory.SpecificGroups.Lyons.Atlas111LocalIndexPlaneOrbit

/-!
# Exact encodings for the Lyons plane tree

The producer in `Atlas111PlaneOrbitSource/GenerateOrbit.py` packs the seven
columns separately in base eight, with row zero in the least significant
position. Coefficient records pack rows of `K`; decoding them as columns gives
the required transpose. No external evaluator is used by the soundness proofs.

Bounds and digits below five make this encoding faithful over `ZMod 5`.
For distinctness it suffices to sort the first packed columns and check adjacent
strict inequalities, provided those columns are distinct. A strictly sorted
self-enumeration of a finite index set is automatically a permutation: no
separate inverse table or pairwise matrix comparisons are needed. The complete
numerical enumeration and its closed checks are separate obligations.

The radix-uniqueness induction is adapted from this repository's
`HaradaNorton/Order/LocalIndex/PackedColumns.lean`, with an explicit digit-validity
hypothesis because the packing radix differs from the field characteristic.
-/

@[expose] public section
namespace Lyons.OrderCertificate.PlaneOrbitData
open Matrix

/-- The seven packed transposed rows in the external producer's record. -/
abbrev PackedRows := Fin 7 → ℕ

/-- A base-eight digit, with the least significant digit numbered zero. -/
def digit (x r : ℕ) : ℕ := x / 8 ^ r % 8

/-- A packed record interpreted as a column matrix. -/
def columns (rows : PackedRows) : Matrix (Fin 111) (Fin 7) (ZMod 5) :=
  fun r j => (digit (rows j) r.val : ZMod 5)

/-- The producer records rows of `K`, while the tree needs `K.transpose`. -/
def coefficient (rows : PackedRows) : Matrix (Fin 7) (Fin 7) (ZMod 5) :=
  fun r j => (digit (rows j) r.val : ZMod 5)

/-- Canonical digits and a length bound exclude modular aliases and hidden digits. -/
def ValidColumn (x : ℕ) : Prop :=
  x < 8 ^ 111 ∧ ∀ r : Fin 111, digit x r.val < 5

instance (x : ℕ) : Decidable (ValidColumn x) :=
  inferInstanceAs (Decidable (x < 8 ^ 111 ∧ ∀ r : Fin 111, digit x r.val < 5))

private theorem eq_of_digits_eq (n x y : ℕ) (hx : x < 8 ^ n) (hy : y < 8 ^ n)
    (h : ∀ j < n, digit x j = digit y j) : x = y := by
  induction n generalizing x y with
  | zero => simp only [pow_zero] at hx hy; omega
  | succ n ih =>
    have hx' : x / 8 < 8 ^ n := (Nat.div_lt_iff_lt_mul (by decide)).mpr (by
      simpa only [pow_succ] using hx)
    have hy' : y / 8 < 8 ^ n := (Nat.div_lt_iff_lt_mul (by decide)).mpr (by
      simpa only [pow_succ] using hy)
    have hq : x / 8 = y / 8 := ih (x / 8) (y / 8) hx' hy' (by
      intro j hj
      simpa only [digit, Nat.div_div_eq_div_mul, pow_succ'] using h (j + 1) (by omega))
    have hr : x % 8 = y % 8 := by simpa [digit] using h 0 (by omega)
    omega

/-- Equality after decoding implies equality of canonical packed columns. -/
theorem eq_of_column_eq {x y : ℕ} (hx : ValidColumn x) (hy : ValidColumn y)
    (h : ∀ r : Fin 111, (digit x r.val : ZMod 5) = (digit y r.val : ZMod 5)) :
    x = y := by
  apply eq_of_digits_eq 111 x y hx.1 hy.1
  intro r hr
  have he := congrArg ZMod.val (h ⟨r, hr⟩)
  simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (hx.2 ⟨r, hr⟩),
    Nat.mod_eq_of_lt (hy.2 ⟨r, hr⟩)] using he

/-- The first column alone can serve as an exact separating key. -/
theorem firstColumn_eq_of_columns_eq {U V : PackedRows}
    (hU : ValidColumn (U 0)) (hV : ValidColumn (V 0))
    (h : columns U = columns V) : U 0 = V 0 := by
  apply eq_of_column_eq hU hV
  intro r
  exact congrFun (congrFun h r) 0

/-- Equality of decoded matrices recovers every canonical packed column. -/
theorem rows_eq_of_columns_eq {U V : PackedRows}
    (hU : ∀ j, ValidColumn (U j)) (hV : ∀ j, ValidColumn (V j))
    (h : columns U = columns V) : U = V := by
  funext j
  apply eq_of_column_eq (hU j) (hV j)
  intro r
  exact congrFun (congrFun h r) j

/-- Concatenation of all seven columns, used if first columns do not separate nodes. -/
def fullKey (rows : PackedRows) : ℕ :=
  ∑ j : Fin 7, rows j * 8 ^ (111 * j.val)

/-- Kernel-executable shape check, allowing every increasing pivot pattern. -/
def checkReduced (rows : PackedRows) (pivot : Fin 7 → Fin 111) : Bool :=
  decide ((∀ i j, i < j → pivot i < pivot j) ∧
    (∀ i j, digit (rows j) (pivot i).val % 5 = if i = j then 1 else 0) ∧
    (∀ r j, r < pivot j → digit (rows j) r.val % 5 = 0))

/-- The numerical shape check certifies a reduced column basis. -/
def reducedBasisOfCheck {rows : PackedRows} {pivot : Fin 7 → Fin 111}
    (h : checkReduced rows pivot = true) : ReducedColumnBasis (columns rows) := by
  have hc := of_decide_eq_true h
  refine ⟨pivot, hc.1, ?_, ?_⟩
  · intro i j
    change (digit (rows j) (pivot i).val : ZMod 5) = _
    rw [← ZMod.natCast_mod, hc.2.1 i j]
    split_ifs <;> rfl
  · intro r j hr
    change (digit (rows j) r.val : ZMod 5) = 0
    rw [← ZMod.natCast_mod, hc.2.2 r j hr]
    rfl

/-- A strictly sorted self-enumeration certifies injectivity without an inverse table. -/
theorem injective_of_sorted {n : ℕ} (key : Fin n → ℕ) (order : Fin n → Fin n)
    (h : StrictMono (fun i => key (order i))) : Function.Injective key := by
  have ho : Function.Injective order := by
    intro i j hij
    exact h.injective (congrArg key hij)
  have hs := Finite.surjective_of_injective ho
  intro i j hij
  obtain ⟨a, rfl⟩ := hs i
  obtain ⟨b, rfl⟩ := hs j
  exact congrArg order (h.injective hij)

/-- Sorted canonical first columns certify distinct column matrices. -/
theorem columns_injective_of_sorted {n : ℕ}
    (rows : Fin n → PackedRows) (order : Fin n → Fin n)
    (hvalid : ∀ i, ValidColumn (rows i 0))
    (hsorted : StrictMono (fun i => rows (order i) 0)) :
    Function.Injective (fun i => columns (rows i)) := by
  intro i j hij
  exact injective_of_sorted (fun i => rows i 0) order hsorted
    (firstColumn_eq_of_columns_eq (hvalid i) (hvalid j) hij)

/-- Only adjacent comparisons are needed in the sorted first-column certificate. -/
theorem columns_injective_of_adjacent {n : ℕ}
    (rows : Fin (n + 1) → PackedRows) (order : Fin (n + 1) → Fin (n + 1))
    (hvalid : ∀ i, ValidColumn (rows i 0))
    (hadjacent : ∀ i : Fin n, rows (order i.castSucc) 0 < rows (order i.succ) 0) :
    Function.Injective (fun i => columns (rows i)) :=
  columns_injective_of_sorted rows order hvalid (Fin.strictMono_iff_lt_succ.mpr hadjacent)

/-- Sorting the complete exact encodings is a fallback when first columns collide. -/
theorem columns_injective_of_fullKey_sorted {n : ℕ}
    (rows : Fin n → PackedRows) (order : Fin n → Fin n)
    (hvalid : ∀ i j, ValidColumn (rows i j))
    (hsorted : StrictMono (fun i => fullKey (rows (order i)))) :
    Function.Injective (fun i => columns (rows i)) := by
  intro i j hij
  apply injective_of_sorted (fun i => fullKey (rows i)) order hsorted
  exact congrArg fullKey (rows_eq_of_columns_eq (hvalid i) (hvalid j) hij)

end Lyons.OrderCertificate.PlaneOrbitData
