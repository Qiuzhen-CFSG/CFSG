module

public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup.AmalgamBound.WordTable
public import Theory.AtlasPort.LinearGroups.G2.WeylMaps
public import Mathlib.Algebra.Field.ZMod
/-!
# From generator actions to binary G₂ word coordinates

A packed label records the image of each split-octonion basis vector. Checking
left multiplication by the two actual generators suffices to recover every
row by word induction. A finite identity evaluating each row word from an
arbitrary row then proves the full multiplication law, without expanding
products of long octonion words. These helpers are consumed by `Actual`.

Source application: Aschbacher--Smith F.1.12 and Definition F.4.3. Root maps
come from the licensed ATLAS port (Gerald Höhn and the ATLAS contributors,
ATLAS Research and Attribution License 1.0, `LICENSES/ATLAS.txt`).
-/

@[expose] public section

open Atlas.G2 Atlas.SplitOctonion
namespace Atlas.G2.LieAutomorphismExtensions.BinaryAmalgamBound.Actual

/-- Column `c`: entry `(r,c)` is bit `8*r+c` of the published label. -/
def column (T : WordTable) (i : Fin 96) (c : Fin 8) : Carrier (ZMod 2) :=
  fun r => ((T.label i >>> (8*r.val+c.val)) % 2 : Nat)

def evalFrom (T : WordTable) (j : Fin 96) : List Bool → Fin 96
  | [] => j
  | b :: w => T.mul (if b then 2 else 1) (evalFrom T j w)

def row (T : WordTable) (x y : Model (ZMod 2)) (i : Fin 96) : Model (ZMod 2) :=
  groupWord x y (T.word i)

structure ActionTable (T : WordTable) (x y : Model (ZMod 2)) : Prop where
  zero : ∀ c, column T 0 c = basisVector c
  step : ∀ (b : Bool) i c, (if b then y else x).val (column T i c) =
    column T (T.mul (if b then 2 else 1) i) c
  word_zero : T.word 0 = []
  product : ∀ i j, T.mul i j = evalFrom T j (T.word i)
  separate : ∀ i j, (∀ c, column T i c = column T j c) → i = j

/-- Six blocks of sixteen keep individual kernel computations small. -/
def block (b : Fin 6) (i : Fin 16) : Fin 96 := ⟨16*b.val+i.val, by omega⟩

theorem forall_blocks (P : Fin 96 → Prop)
    (h : ∀ b i, P (block b i)) (i : Fin 96) : P i := by
  have he : block (@Fin.divNat 6 16 i) (@Fin.modNat 6 16 i) = i := by
    apply Fin.ext
    simp only [block, Fin.divNat, Fin.modNat]
    omega
  exact he ▸ h _ _

/-- Equality of all matrix entries recovers the complete 64-bit label. -/
theorem labels_eq {S T : WordTable} {i j : Fin 96}
    (hi : S.label i < 2^64) (hj : T.label j < 2^64)
    (h : ∀ c, column S i c = column T j c) : S.label i = T.label j := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < 64
  · let c : Fin 8 := ⟨k % 8, by omega⟩
    let r : Fin 8 := ⟨k / 8, by omega⟩
    have he := congrArg (fun v : Carrier (ZMod 2) => (v r).val) (h c)
    simp only [column, ZMod.val_natCast, Nat.mod_mod, c, r] at he
    have hr : 8*(k/8)+k%8=k := by omega
    rw [hr] at he
    simp only [Nat.testBit, Nat.one_and_eq_mod_two, he]
  · have hp : 2^64 ≤ 2^k := Nat.pow_le_pow_right (by decide) (by omega)
    simp only [Nat.testBit, Nat.shiftRight_eq_div_pow,
      Nat.div_eq_of_lt (hi.trans_le hp), Nat.div_eq_of_lt (hj.trans_le hp)]

variable {T : WordTable} {x y : Model (ZMod 2)}

theorem model_ext {g h : Model (ZMod 2)}
    (he : ∀ c, g.val (basisVector c) = h.val (basisVector c)) : g = h := by
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  exact linearMap_ext _ _ he

theorem evalFrom_zero (T : WordTable) (w : List Bool) :
    evalFrom T 0 w = T.eval 1 2 w := by
  induction w with
  | nil => rfl
  | cons b w ih => simp only [evalFrom, WordTable.eval, ih]

theorem ActionTable.word_action (h : ActionTable T x y) (w : List Bool)
    (j : Fin 96) (c : Fin 8) :
    (groupWord x y w).val (column T j c) = column T (evalFrom T j w) c := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    change (if b then y else x).val ((groupWord x y w).val (column T j c)) = _
    rw [ih]
    exact h.step b _ c

theorem ActionTable.row_action (h : ActionTable T x y) (hT : T.Valid)
    (i : Fin 96) (c : Fin 8) :
    (row T x y i).val (basisVector c) = column T i c := by
  rw [← h.zero c]
  exact (h.word_action (T.word i) 0 c).trans
    (congrArg (fun j => column T j c) ((evalFrom_zero T _).trans (hT.words i)))

theorem ActionTable.row_one (h : ActionTable T x y) : row T x y 0 = 1 := by
  rw [row, h.word_zero]; rfl

theorem ActionTable.row_mul (h : ActionTable T x y) (hT : T.Valid)
    (i j : Fin 96) : row T x y (T.mul i j) = row T x y i * row T x y j := by
  apply model_ext
  intro c
  rw [h.row_action hT]
  change _ = (row T x y i).val ((row T x y j).val (basisVector c))
  rw [h.row_action hT, row, h.word_action, h.product]

theorem ActionTable.row_injective (h : ActionTable T x y) (hT : T.Valid) :
    Function.Injective (row T x y) := by
  intro i j he
  apply h.separate
  intro c
  rw [← h.row_action hT, ← h.row_action hT, he]

theorem row_mem (T : WordTable) (H : Subgroup (Model (ZMod 2)))
    (hx : x ∈ H) (hy : y ∈ H) (i : Fin 96) : row T x y i ∈ H := by
  unfold row
  generalize T.word i = w
  induction w with
  | nil => exact H.one_mem
  | cons b w ih =>
    exact H.mul_mem (by cases b <;> assumption) ih
end Atlas.G2.LieAutomorphismExtensions.BinaryAmalgamBound.Actual
