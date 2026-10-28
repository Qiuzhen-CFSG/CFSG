module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.PairImages

/-!
# Parity certificates for the marked primed-(b) obstruction

Six bits of the actual kernel action equations sum to a contradiction.
The two checks are independent one-mask identities, avoiding enumeration of
pairs of 2048-element fibres. Source: KW (1988), Proposition 2.3.4(ii).
-/

public section
namespace Janko4.LocalStructure.ElementaryEightGeometry
open Cardinality.QuotientCount.Image SylowCore

theorem first_parity : ∀ m : Fin 2048,
    Bool.xor (Bool.xor
      ((maskImage (actionRows 0 1) m.val ^^^ m.val).testBit 0)
      ((maskImage (actionRows 0 1) m.val ^^^ m.val).testBit 1))
      ((maskImage (actionRows 0 2) m.val ^^^ m.val).testBit 3) = false := by
  decide +kernel

theorem second_parity : ∀ n : Fin 2048,
    Bool.xor (Bool.xor (Bool.xor
      ((maskImage (actionRows 0 2) n.val ^^^ n.val).testBit 4)
      ((maskImage pairActionRows n.val ^^^ n.val).testBit 0))
      ((maskImage pairActionRows n.val ^^^ n.val).testBit 1))
      ((maskImage (actionRows 0 1) n.val ^^^ n.val).testBit 3) = false := by
  decide +kernel

end Janko4.LocalStructure.ElementaryEightGeometry
