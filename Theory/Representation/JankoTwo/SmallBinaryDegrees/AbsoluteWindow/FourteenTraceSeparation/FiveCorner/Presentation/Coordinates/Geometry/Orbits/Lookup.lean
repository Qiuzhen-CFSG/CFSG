module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Geometry.Orbits.Data
import Mathlib.Tactic.FinCases

/-!
# Comparison with the original fixed action

One checked equality per 128-entry block identifies each compact table with
its unchanged source array. The block extraction lemma then identifies every
letter move and every finite word walk. No coset or group action is assumed.

Source: Coordinates/Model.lean and Coordinates/source/README.md.
-/

@[expose] public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Geometry.Orbits

set_option maxRecDepth 4096 in
private theorem blocksA : ∀ i : Fin 189, entry 1920 packedA i.val = actionA[i.val]! := by
  decide +kernel
set_option maxRecDepth 4096 in
private theorem blocksB : ∀ i : Fin 189, entry 1920 packedB i.val = actionB[i.val]! := by
  decide +kernel
set_option maxRecDepth 4096 in
private theorem blocksBInv : ∀ i : Fin 189, entry 1920 packedBInv i.val = actionBInv[i.val]! := by
  decide +kernel
set_option maxRecDepth 4096 in
private theorem blocksLabels : ∀ i : Fin 189, entry 1920 packedLabels i.val = orbitLabels[i.val]! := by
  decide +kernel
set_option maxRecDepth 4096 in
private theorem blocksRoots : ∀ i : Fin 8, entry 1920 packedRoots i.val = orbitRoots[i.val]! := by
  decide +kernel

lemma entryA (x : Point) : entry 15 packedA x.val = lookup 15 actionA x.val :=
  entry_eq_lookup _ _ _ _ (blocksA ⟨x.val/128, by omega⟩)
lemma entryB (x : Point) : entry 15 packedB x.val = lookup 15 actionB x.val :=
  entry_eq_lookup _ _ _ _ (blocksB ⟨x.val/128, by omega⟩)
lemma entryBInv (x : Point) : entry 15 packedBInv x.val = lookup 15 actionBInv x.val :=
  entry_eq_lookup _ _ _ _ (blocksBInv ⟨x.val/128, by omega⟩)
lemma entryLabels (x : Point) : entry 15 packedLabels x.val = lookup 15 orbitLabels x.val :=
  entry_eq_lookup _ _ _ _ (blocksLabels ⟨x.val/128, by omega⟩)
lemma entryRoots (i : Fin 1008) : entry 15 packedRoots i.val = lookup 15 orbitRoots i.val :=
  entry_eq_lookup _ _ _ _ (blocksRoots ⟨i.val/128, by omega⟩)

def letterTable (l : ℕ) : ℕ :=
  if l == 0 || l == 2 then packedA else if l == 1 then packedB else packedBInv

def move (l x : ℕ) : ℕ := entry 15 (letterTable l) x % 24192

def run (w : List ℕ) (x : ℕ) : ℕ := w.foldl (fun x l => move l x) x

lemma move_eq_step (l : Fin 4) (x : Point) : move l.val x.val = (step l x).val := by
  fin_cases l
  · change entry 15 packedA x.val % 24192 = lookup 15 actionA x.val % 24192
    rw [entryA]
  · change entry 15 packedB x.val % 24192 = lookup 15 actionB x.val % 24192
    rw [entryB]
  · change entry 15 packedA x.val % 24192 = lookup 15 actionA x.val % 24192
    rw [entryA]
  · change entry 15 packedBInv x.val % 24192 = lookup 15 actionBInv x.val % 24192
    rw [entryBInv]

lemma run_eq_walk (w : List (Fin 4)) (x : Point) :
    run (w.map Fin.val) x.val = (walk w x).val := by
  induction w generalizing x with
  | nil => rfl
  | cons l w ih =>
    change run (w.map Fin.val) (move l.val x.val) = (walk w (step l x)).val
    rw [move_eq_step]
    exact ih (step l x)

def fastOrbit (x : Point) : Fin 1008 :=
  ⟨entry 15 packedLabels x.val % 1008, Nat.mod_lt _ (by decide)⟩
def fastRoot (i : Fin 1008) : Point :=
  ⟨entry 15 packedRoots i.val % 24192, Nat.mod_lt _ (by decide)⟩

lemma fastOrbit_eq (x : Point) : fastOrbit x = orbit x := by
  apply Fin.ext
  exact congrArg (· % 1008) (entryLabels x)
lemma fastRoot_eq (i : Fin 1008) : fastRoot i = root i := by
  apply Fin.ext
  exact congrArg (· % 24192) (entryRoots i)

/-- The cache comparison is proved in Maps.lean. -/
def leftCheck (x : ℕ) : Bool := run (leftWord.map Fin.val) x == entry 15 packedLeft x
/-- The cache comparison is proved in Maps.lean. -/
def rightCheck (x : ℕ) : Bool := run (rightWord.map Fin.val) x == entry 15 packedRight x

def leftMove (x : Point) : Point :=
  ⟨entry 15 packedLeft x.val % 24192, Nat.mod_lt _ (by decide)⟩
def rightMove (x : Point) : Point :=
  ⟨entry 15 packedRight x.val % 24192, Nat.mod_lt _ (by decide)⟩

def cachedSubgroup (t : CoefficientTheory.PowerIndex) (x : Point) : Point :=
  rightMove^[t.2.val] (leftMove^[t.1.val] x)

def powers (x : Point) : CoefficientTheory.PowerIndex :=
  (⟨entry 5 packedPowers x.val % 5, Nat.mod_lt _ (by decide)⟩,
    ⟨entry 5 packedPowers x.val / 5 % 5, Nat.mod_lt _ (by decide)⟩)

def representativeCheck (i : ℕ) : Bool :=
  run ((representativeWord ⟨i % 1008, Nat.mod_lt _ (by decide)⟩).map Fin.val) 0 ==
    (fastRoot ⟨i % 1008, Nat.mod_lt _ (by decide)⟩).val

def orbitCheck (n : ℕ) : Bool :=
  let x : Point := ⟨n % 24192, Nat.mod_lt _ (by decide)⟩
  (cachedSubgroup (powers x) (fastRoot (fastOrbit x))).val == n

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Geometry.Orbits
