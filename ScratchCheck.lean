import Theory.GroupAction.C4SquareActionDichotomySetup
namespace C4SquareExtension.ActionDichotomy
variable (p : OuterCode)
#synth Decidable (Valid (0,0,0,1) (1,0,0,0) p)
#synth Decidable (Witness (0,0,0,1) (1,0,0,0) p)
#synth Decidable (Valid (0,0,0,1) (1,0,0,0) p → Witness (0,0,0,1) (1,0,0,0) p)
end C4SquareExtension.ActionDichotomy
