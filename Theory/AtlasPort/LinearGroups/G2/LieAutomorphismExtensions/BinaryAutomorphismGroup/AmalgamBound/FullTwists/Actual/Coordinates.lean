module

public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup.AmalgamBound.Actual.Coordinates
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup.AmalgamBound.FullTwists.Data

/-!
# Three-generator word coordinates for the full binary G₂ parabolics

Generator actions on packed matrix columns recover the actual root words by
induction. The same induction proves the multiplication law from finite row
transitions, avoiding repeated evaluation of long octonion words. Distinct
packed labels then separate the actual elements.

This extends the method in `AmalgamBound.Actual.Coordinates` without changing
its fixed 96-row interface. The consumer is `FullTwists.Actual`.
Source application: Aschbacher--Smith F.1.12(I)(3), q = 2, pp.262--263.
Coordinates follow Gerald Höhn and the ATLAS contributors, ATLAS Research
and Attribution License 1.0 (`LICENSES/ATLAS.txt`).
-/

@[expose] public section
open Atlas.G2 Atlas.SplitOctonion
namespace Atlas.G2.LieAutomorphismExtensions.BinaryAmalgamBound.FullTwists.Actual

/-- Entry `(r,c)` is bit `8*r+c` of the packed matrix. -/
def column (label : Nat) (c : Fin 8) : Carrier (ZMod 2) :=
  fun r => ((label >>> (8*r.val+c.val)) % 2 : Nat)

structure Coordinates (n : Nat) where
  mul : Fin n → Fin n → Fin n
  word : Fin n → List (Fin 3)
  label : Fin n → Nat
  generator : Fin 3 → Fin n

namespace Coordinates
variable {n : Nat}

def evalFrom (T : Coordinates n) (j : Fin n) : List (Fin 3) → Fin n
  | [] => j
  | b :: w => T.mul (T.generator b) (T.evalFrom j w)

def groupWord (g : Fin 3 → Model (ZMod 2)) : List (Fin 3) → Model (ZMod 2)
  | [] => 1
  | b :: w => g b * groupWord g w

def row (T : Coordinates n) (g : Fin 3 → Model (ZMod 2)) (i : Fin n) :=
  groupWord g (T.word i)

structure ActionTable [NeZero n] (T : Coordinates n)
    (g : Fin 3 → Model (ZMod 2)) : Prop where
  zero : ∀ c, column (T.label 0) c = basisVector c
  step : ∀ b i c, (g b).val (column (T.label i) c) =
    column (T.label (T.mul (T.generator b) i)) c
  words : ∀ i, T.evalFrom 0 (T.word i) = i
  product : ∀ i j, T.mul i j = T.evalFrom j (T.word i)
  separate : ∀ i j, (∀ c, column (T.label i) c = column (T.label j) c) → i = j

variable [NeZero n] {T : Coordinates n} {g : Fin 3 → Model (ZMod 2)}

theorem ActionTable.word_action (h : T.ActionTable g) (w : List (Fin 3))
    (j : Fin n) (c : Fin 8) :
    (groupWord g w).val (column (T.label j) c) =
      column (T.label (T.evalFrom j w)) c := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    change (g b).val ((groupWord g w).val (column (T.label j) c)) = _
    rw [ih]
    exact h.step b _ c

theorem ActionTable.row_action (h : T.ActionTable g) (i : Fin n) (c : Fin 8) :
    (T.row g i).val (basisVector c) = column (T.label i) c := by
  rw [← h.zero c]
  exact (h.word_action (T.word i) 0 c).trans
    (congrArg (fun j => column (T.label j) c) (h.words i))

theorem ActionTable.row_mul (h : T.ActionTable g) (i j : Fin n) :
    T.row g (T.mul i j) = T.row g i * T.row g j := by
  apply BinaryAmalgamBound.Actual.model_ext
  intro c
  rw [h.row_action]
  change _ = (T.row g i).val ((T.row g j).val (basisVector c))
  rw [h.row_action, row, h.word_action, h.product]

theorem ActionTable.row_injective (h : T.ActionTable g) :
    Function.Injective (T.row g) := by
  intro i j he
  apply h.separate
  intro c
  rw [← h.row_action, ← h.row_action, he]

omit [NeZero n] in
theorem row_mem (T : Coordinates n) (g : Fin 3 → Model (ZMod 2))
    (H : Subgroup (Model (ZMod 2))) (hg : ∀ b, g b ∈ H) (i : Fin n) :
    T.row g i ∈ H := by
  unfold row
  generalize T.word i = w
  induction w with
  | nil => exact H.one_mem
  | cons b w ih => exact H.mul_mem (hg b) ih
end Coordinates

/-- Eight-row blocks bound the size of each kernel computation. -/
def block {n : Nat} (b : Fin n) (i : Fin 8) : Fin (n*8) :=
  ⟨8*b.val+i.val, by omega⟩

theorem forall_blocks {n : Nat} (P : Fin (n*8) → Prop)
    (h : ∀ b i, P (block b i)) (i : Fin (n*8)) : P i := by
  have he : block (@Fin.divNat n 8 i) (@Fin.modNat n 8 i) = i := by
    apply Fin.ext
    simp only [block, Fin.divNat, Fin.modNat]
    omega
  exact he ▸ h _ _

theorem labels_eq {a b : Nat} (ha : a < 2^64) (hb : b < 2^64)
    (h : ∀ c, column a c = column b c) : a = b := by
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
      Nat.div_eq_of_lt (ha.trans_le hp), Nat.div_eq_of_lt (hb.trans_le hp)]

def leftCoordinates : Coordinates 192 :=
  ⟨leftMul, leftWord, leftLabel, fun b => ⟨b.val+1, by omega⟩⟩
def rightCoordinates : Coordinates 192 :=
  ⟨rightMul, rightWord, rightLabel, fun b => ⟨b.val+1, by omega⟩⟩

def commonGenerator : Model (ZMod 2) := rootC 1 * rootE 1 * rootF 1
def leftGenerators : Fin 3 → Model (ZMod 2) :=
  ![commonGenerator, rootF 1 * weylS, rootC 1]
def rightGenerators : Fin 3 → Model (ZMod 2) :=
  ![commonGenerator, rootE 1 * weylR, rootC 1]

end Atlas.G2.LieAutomorphismExtensions.BinaryAmalgamBound.FullTwists.Actual
