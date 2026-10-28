import Theory.GroupAction.C4SquareActionDichotomySetup
namespace C4SquareExtension.ActionDichotomy
@[reducible] def q (n : Nat) : Multiplicative (ZMod 4) := Multiplicative.ofAdd (n : ZMod 4)
-- no table use: test Valid forall p implies simple true for this known pair
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
example : ∀ p : OuterCode, Valid (0,0,0,1) (1,0,0,0) p → True := by decide
end C4SquareExtension.ActionDichotomy
