module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Model
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Coefficients.Data

/-!
# Certified balanced action lookup

The block comparisons below check all 189 original blocks of each action and
of the orbit labels. Thus the faster walk is exactly the walk from Model.lean,
including its letter convention and reductions modulo the point count.
The two subgroup-action trees are only candidate cached actions here; proving
that they evaluate the long subgroup words is a separate finite obligation.

Source: Coordinates/source/README.md and Coefficients/source/generate.py.
-/

@[expose] public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Coefficients

set_option maxRecDepth 2048 in
private theorem blocks :
    (∀ q : Fin 189, blockGet actionATree q.val = actionA[q.val]!) ∧
    (∀ q : Fin 189, blockGet actionBTree q.val = actionB[q.val]!) ∧
    (∀ q : Fin 189, blockGet actionBInvTree q.val = actionBInv[q.val]!) ∧
    (∀ q : Fin 189, blockGet labelTree q.val = orbitLabels[q.val]!) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

def fastStep : Fin 4 → Point → Point := treeStep actionATree actionBTree actionBInvTree

theorem fastStep_eq : fastStep = step :=
  treeStep_eq _ _ _ blocks.1 blocks.2.1 blocks.2.2.1

def fastWalk (w : List (Fin 4)) (x : Point) : Point :=
  w.foldl (fun x l => fastStep l x) x

theorem fastWalk_eq (w : List (Fin 4)) (x : Point) : fastWalk w x = walk w x := by
  simp only [fastWalk, fastStep_eq, walk]

def fastOrbit (x : Point) : Fin 1008 :=
  ⟨treeLookup labelTree x.val % 1008, Nat.mod_lt _ (by decide)⟩

theorem fastOrbit_eq (x : Point) : fastOrbit x = orbit x := by
  apply Fin.ext
  change treeLookup labelTree x.val % 1008 = lookup 15 orbitLabels x.val % 1008
  rw [treeLookup_eq _ _ blocks.2.2.2]

def leftAction (x : Point) : Point :=
  ⟨treeLookup leftTree x.val % 24192, Nat.mod_lt _ (by decide)⟩

def rightAction (x : Point) : Point :=
  ⟨treeLookup rightTree x.val % 24192, Nat.mod_lt _ (by decide)⟩

/-- Exactly the two cached-word comparisons still to be checked. -/
def SubgroupActionsCorrect : Prop :=
  leftAction = walk leftWord ∧ rightAction = walk rightWord

/-- Checking with the certified fast walker discharges the original walk contract. -/
theorem subgroupActionsCorrect_of_fast
    (hL : ∀ x, leftAction x = fastWalk leftWord x)
    (hR : ∀ x, rightAction x = fastWalk rightWord x) : SubgroupActionsCorrect := by
  constructor
  · funext x
    rw [hL, fastWalk_eq]
  · funext x
    rw [hR, fastWalk_eq]

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Coefficients
