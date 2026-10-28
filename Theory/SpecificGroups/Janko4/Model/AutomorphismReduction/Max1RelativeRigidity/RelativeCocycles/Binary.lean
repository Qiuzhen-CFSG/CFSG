module
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.Image.StarData
open Janko4.Cardinality.KernelCount Janko4.Cardinality.QuotientCount.Image
/-!
# Binary calculation for relative cocycles in the actual J₄ max1 subgroup

The two maps below implement the certified right-conjugation masks. Their
natural-number specifications connect them to `KernelOrbits.Coordinates`.
The four letters keep inverse group words distinct, even when their actions
coincide. `wordDelta` uses the right-cocycle recurrence.

The five words fix mask three. They were discovered from the literal ATLAS
`J4G1-max1W1` action; their stabilizer property is checked here independently.
The group interpretation is supplied in `WordSoundness`.
-/
@[expose] public section
namespace Janko4.Max1RelativeRigidity.RelativeCocycles
abbrev V := BitVec 11
def act (masks : Fin 11 → ℕ) (z : V) : V :=
  (List.ofFn (fun i : Fin 11 => if z.getLsbD i.val then BitVec.ofNat 11 (masks i) else 0)).foldr (· ^^^ ·) 0
lemma fold_toNat (l : List V) : (l.foldr (· ^^^ ·) 0).toNat = (l.map BitVec.toNat).foldr Nat.xor 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.foldr_cons, List.map_cons, BitVec.toNat_xor, ih]; rfl
lemma act_toNat (masks : Fin 11 → ℕ) (hm : ∀ i, masks i < 2048) (z : V) :
    (act masks z).toNat = maskImage masks z.toNat := by
  simp only [act, fold_toNat, maskImage, List.map_ofFn]
  congr 2
  funext i
  split_ifs <;> simp_all [BitVec.getLsbD, Nat.mod_eq_of_lt (hm i)]
def actX : V → V := act xMasks

def actY : V → V := act yMasks

set_option maxRecDepth 10000 in
private theorem actX_sq_all : ∀ z : V, actX (actX z) = z := by
  decide +kernel

theorem actX_sq (z : V) : actX (actX z) = z := actX_sq_all z

set_option maxRecDepth 10000 in
private theorem actY_cube_all : ∀ z : V, actY (actY (actY z)) = z := by
  decide +kernel

theorem actY_cube (z : V) : actY (actY (actY z)) = z := actY_cube_all z

inductive Letter where
  | X | Y | Xi | Yi
  deriving DecidableEq
open Letter
def actLetter : Letter → V → V
  | X => actX
  | Y => actY
  | Xi => actX
  | Yi => fun z => actY (actY z)
def deltaLetter (a b : V) : Letter → V
  | X => a
  | Y => b
  | Xi => actX a
  | Yi => actY (actY b)
def wordDelta (w : List Letter) (a b : V) : V :=
  w.foldl (fun z l => actLetter l z ^^^ deltaLetter a b l) 0
def wordAct (w : List Letter) (z : V) : V := w.foldl (fun z l => actLetter l z) z
def word0 : List Letter := [X]
theorem word0_fixes : wordAct word0 3 = 3 := by decide +kernel
def word1 : List Letter := [Y, Y, Y]
theorem word1_fixes : wordAct word1 3 = 3 := by decide +kernel
def word2 : List Letter := [Y, X, Y, X, Y, Y, X, Yi, Yi, Xi, Yi, Xi, Yi]
theorem word2_fixes : wordAct word2 3 = 3 := by decide +kernel
def word3 : List Letter := [Y, Y, X, Y, X, Y, X, Y, X, Yi, Xi, Yi, Xi, Yi, Xi, Yi, Yi]
theorem word3_fixes : wordAct word3 3 = 3 := by decide +kernel
def word4 : List Letter := [Y, Y, X, Y, Y, X, Y, Y, X, Y, X, Y, X, Y, Xi, Yi, Xi, Yi, Xi, Yi, Yi, Xi, Yi, Yi, Xi, Yi, Yi]
theorem word4_fixes : wordAct word4 3 = 3 := by decide +kernel
def Line (z : V) : Prop := z = 0 ∨ z = 3

theorem actX_toNat (z : V) : (actX z).toNat = maskImage xMasks z.toNat := by
  exact act_toNat xMasks (by decide +kernel) z

theorem actY_toNat (z : V) : (actY z).toNat = maskImage yMasks z.toNat := by
  exact act_toNat yMasks (by decide +kernel) z

end Janko4.Max1RelativeRigidity.RelativeCocycles
