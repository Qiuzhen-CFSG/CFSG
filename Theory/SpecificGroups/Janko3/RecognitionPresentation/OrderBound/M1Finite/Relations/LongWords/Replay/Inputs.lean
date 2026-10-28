module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Finite.Relations.LongWords.WordCalculus

/-! Kernel checked dependency slice of the local word rewriting certificate.
The source equations are explicit inputs; this module assumes no group order. -/

@[expose] public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.Relations.LongWords.Replay
variable {G : Type*} [Group G]

def sourceWord : Nat → List Nat
  | 0 => [0, 0]
  | 1 => [1, 1, 1, 1]
  | 2 => [0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2]
  | 3 => [2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2]
  | 4 => [0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 1, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 0, 2]
  | 5 => [2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0]
  | 6 => [2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0]
  | _ => []

structure Inputs (G : Type*) [Group G] where
  g : Nat → G
  inverse : ∀ n, g (inverseLetter n) = (g n)⁻¹
  relation : ∀ r, readWord g (sourceWord r) = 1

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.Relations.LongWords.Replay
