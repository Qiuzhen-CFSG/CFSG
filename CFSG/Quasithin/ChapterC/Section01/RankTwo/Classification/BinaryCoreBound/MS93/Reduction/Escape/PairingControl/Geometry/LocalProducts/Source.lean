module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Source

/-!
# The remaining source stages for the local products

Step (6) bounds the literal P-conjugate span for every backward choice.
The edge choice must exist, and P joined with the actual critical endpoint
Z-layer must generate G_alpha. These are proof obligations of the R_4/R_mu
argument, not additional standing hypotheses of the source theorem.

The residual-span interface is the proved consequence of those outputs.
It supplies the local-product continuation with a choice and a bound on
its actual span, without assuming a forward normal product. The continuation
must still prove the triple-commutator and Z-containment assertions and
transport the local products to the forward point on the original path.

Source: MS93 (1993), (4.3.2)(6) and the subsequent paragraph, printed p.885.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.LocalProducts
variable {M : Type*} [Group M] {R : Subgroup M} {geometry : MS93.Geometry R}

/-- The geometric outputs before the residual and local-product deductions. -/
structure StepSixFacts (p : Counterexample geometry) : Prop where
  backward : Nonempty (BackwardChoice p)
  bound : ∀ choice : BackwardChoice p, ∀ d, Before p.a p.a' d 4 → choice.W ≤ Q R d
  generation : ∀ choice : BackwardChoice p, choice.P ⊔ Z R p.a' = stabilizer R p.a

/-- The span input to the continuation, with no forward-product conclusion. -/
structure ResidualSpanFacts (p : Counterexample geometry) : Prop where
  backward : Nonempty (BackwardChoice p)
  residual : ∀ choice : BackwardChoice p, ⁅choice.W, Ltilde R p.a⁆ ≤ Vcirc R p.a

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.LocalProducts
