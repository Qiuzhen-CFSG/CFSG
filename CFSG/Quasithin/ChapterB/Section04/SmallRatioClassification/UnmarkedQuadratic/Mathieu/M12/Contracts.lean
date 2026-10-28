module
public import CFSG.Quasithin.ChapterB.Section04.SmallRatioClassification.UnmarkedQuadratic.Mathieu.M12.Data
public import Theory.Representation.MathieuCodeRestriction.QuadraticActors.Obstruction

@[expose] public section
namespace CFSG.Quasithin.ChapterB.SmallRatioClassification.UnmarkedQuadratic.Mathieu.M12
open Data Sporadic.Mathieu.M12ExceptionalExtension.OverlapExtensions

theorem prefix_zero : prefixMatrix 0 = 1 := by decide +kernel
theorem matrix_zero : matrix 0 = 1 := by decide +kernel
theorem prefix_word_zero : prefixWord 0 = [] := by decide +kernel

def prefixCheck (i : Fin 90) : Prop := i ≠ 0 →
  prefixParent i < i ∧
  prefixWord i = prefixWord (prefixParent i) ++ [prefixLast i] ∧
  prefixMatrix (prefixParent i) * baseMatrix (prefixLast i) = prefixMatrix i


def matrixCheck (i : Fin 128) : Prop := i ≠ 0 →
  parent i < i ∧
  Sporadic.Mathieu.M12ExceptionalExtension.OverlapExtensions.Data.overlapWords i =
    Sporadic.Mathieu.M12ExceptionalExtension.OverlapExtensions.Data.overlapWords (parent i) ++ [last i] ∧
  matrix (parent i) * generatorMatrix (last i) = matrix i

def squareWitness (i : Fin 128) : Fin 10 × Fin 10 :=
  (⟨squareWitnessTable[i.val]! / 10 % 10, Nat.mod_lt _ (by decide)⟩,
   ⟨squareWitnessTable[i.val]! % 10, Nat.mod_lt _ (by decide)⟩)

def squareCheck (i : Fin 128) : Prop := vertex (squareIndex i) = i ∨
  ((matrix i - 1) * (matrix i - 1)) (squareWitness i).1 (squareWitness i).2 ≠ 0

def rejectionCheck (v w : Fin 36) : Prop := adjacent v w = true ∨
  (if nonedge v w < 100 then displacement v * displacement w
    else displacement w * displacement v)
    ⟨nonedge v w / 10 % 10, Nat.mod_lt _ (by decide)⟩
    ⟨nonedge v w % 10, Nat.mod_lt _ (by decide)⟩ ≠ 0

def neighborsCheck (v : Fin 36) : Prop := ∀ w : Fin 36,
  v ≠ 0 → w ≠ 0 → w ≠ v → adjacent v w = true →
  (Finset.univ.filter (fun k => adjacent v k && adjacent w k)).card ≤ 4

def rankCheck (v : Fin 36) : Prop := ∀ w : Fin 36,
  v ≠ 0 → w ≠ 0 → w ≠ v → adjacent v w = true →
  selected v w * rightInverse v w = 1

end CFSG.Quasithin.ChapterB.SmallRatioClassification.UnmarkedQuadratic.Mathieu.M12
