module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Model
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Coefficients.Action
/-!
# Sound certificates for cached subgroup-word actions

Packed block checks inspect all 128 little-endian entries without repeatedly
looking up their expected block. The soundness proof covers all 189 blocks of
the fixed 24192-point set. Certified segment tables compose as literal walks;
normalizing letter 2 to 0 uses their definitionally identical action tables.

Source: Coordinates/Model.lean, Coefficients/Action.lean, and the unchanged
Presentation/source/discovery/ data. The final SubgroupActions module uses
these lemmas to discharge SubgroupActionsCorrect without geometric premises.
-/

@[expose] public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Coefficients.SubgroupActionCertificate

def runTrees (ts : List BlockTree) (x : Nat) : Nat :=
  ts.foldl (fun x t => treeLookup t x % 24192) x

def checkPack (f : Nat → Nat) : Nat → Nat → Nat → Bool
  | _, _, 0 => true
  | p, x, n+1 => (p % 32768 == f x) && checkPack f (p >>> 15) (x+1) n

def checkBlocks (t : BlockTree) (ts : List BlockTree) (start count : Nat) : Bool :=
  (List.range count).all fun b =>
    checkPack (runTrees ts) (blockGet t (start+b)) ((start+b)*128) 128

def Represents (t : BlockTree) (w : List (Fin 4)) : Prop :=
  ∀ x : Point, treeLookup t x.val % 24192 = (fastWalk w x).val

theorem checkPack_sound (f : Nat → Nat) (p x n : Nat)
    (h : checkPack f p x n = true) (i : Fin n) :
    (p >>> (15*i.val)) % 32768 = f (x+i.val) := by
  induction n generalizing p x with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    have hh : (p % 32768 == f x) = true ∧ checkPack f (p >>> 15) (x+1) n = true := by
      simpa only [checkPack, Bool.and_eq_true] using h
    rcases i with ⟨i, hi⟩
    cases i with
    | zero => simpa only [Nat.mul_zero, Nat.shiftRight_zero, Nat.add_zero, beq_iff_eq]
        using hh.1
    | succ i =>
      have hrec := ih (p >>> 15) (x+1) hh.2 ⟨i, by omega⟩
      have he : 15 + 15*i = 15*(i+1) := by omega
      have hx : x+1+i = x+(i+1) := by omega
      simpa only [← Nat.shiftRight_add, he, hx] using hrec

theorem checks_sound (t : BlockTree) (ts : List BlockTree) (size count : Nat)
    (hn : size * count = 189)
    (h : ∀ q : Fin count, checkBlocks t ts (q.val * size) size = true) (x : Point) :
    treeLookup t x.val = runTrees ts x.val := by
  have hs : 0 < size := by nlinarith
  let b := x.val / 128
  have hb : b < 189 := by dsimp [b]; have := x.isLt; omega
  have hq : b / size < count := (Nat.div_lt_iff_lt_mul hs).mpr (by simpa only [Nat.mul_comm count size, hn] using hb)
  have hi : b % size < size := Nat.mod_lt _ hs
  have he : b / size * size + b % size = b := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod b size
  have hx := List.all_eq_true.mp (h ⟨b / size, hq⟩)
    (b % size) (List.mem_range.mpr hi)
  simp only [he] at hx
  have hr := checkPack_sound (runTrees ts) (blockGet t b) (b*128) 128 hx
    ⟨x.val % 128, Nat.mod_lt _ (by decide)⟩
  have he' : b*128 + x.val % 128 = x.val := by dsimp [b]; omega
  simpa only [he', treeLookup, b] using hr

theorem fastWalk_append (u v : List (Fin 4)) (x : Point) :
    fastWalk (u ++ v) x = fastWalk v (fastWalk u x) := by
  simp only [fastWalk, List.foldl_append]

theorem runTrees_eq_fastWalk (ps : List (BlockTree × List (Fin 4)))
    (h : ∀ t w, (t, w) ∈ ps → Represents t w) (x : Point) :
    runTrees (ps.map Prod.fst) x.val = (fastWalk (ps.flatMap Prod.snd) x).val := by
  induction ps generalizing x with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨t, w⟩
    change runTrees (ps.map Prod.fst) (treeLookup t x.val % 24192) =
      (fastWalk (w ++ ps.flatMap Prod.snd) x).val
    rw [h t w (by simp)]
    rw [ih (fun t' w' hm => h t' w' (by simp [hm]))]
    rw [fastWalk_append]

theorem represents_of_checks (t : BlockTree) (ps : List (BlockTree × List (Fin 4)))
    (hp : ∀ t w, (t, w) ∈ ps → Represents t w)
    (size count : Nat) (hn : size * count = 189)
    (hc : ∀ q : Fin count, checkBlocks t (ps.map Prod.fst) (q.val * size) size = true) :
    Represents t (ps.flatMap Prod.snd) := by
  intro x
  rw [checks_sound t _ size count hn hc x, runTrees_eq_fastWalk ps hp x]
  exact Nat.mod_eq_of_lt (fastWalk _ x).isLt

def normalizeLetter (l : Fin 4) : Fin 4 := if l = 2 then 0 else l

theorem fastStep_normalizeLetter (l : Fin 4) (x : Point) :
    fastStep (normalizeLetter l) x = fastStep l x := by
  fin_cases l <;> rfl

theorem fastWalk_normalize (w : List (Fin 4)) (x : Point) :
    fastWalk (w.map normalizeLetter) x = fastWalk w x := by
  induction w generalizing x with
  | nil => rfl
  | cons l w ih =>
    simpa only [List.map_cons, fastWalk, List.foldl_cons, fastStep_normalizeLetter]
      using ih (fastStep l x)
theorem actionA_represents : Represents actionATree [0] := by intro x; rfl

theorem actionB_represents : Represents actionBTree [1] := by intro x; rfl

theorem actionBInv_represents : Represents actionBInvTree [3] := by intro x; rfl

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Coefficients.SubgroupActionCertificate
