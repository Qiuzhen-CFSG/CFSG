module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.BorelContracts

/-!
# The intermediate parabolic in the actual component action quotient

In the characteristic-two models, a parabolic containing the chosen Sylow
normalizer is specified by that containment. Maximality here is among
proper parabolics invariant under the supplied Sylow subgroup. In
particular it is neither ambient normality nor maximality allowing the
whole component.

`QuotientParabolic` is an intermediate output to be constructed from the
two-local and characteristic-two maximality conditions. It contains no
restriction to the surviving families and no Borel equality. The residual
inspection can therefore be developed with this explicit premise while
its producer proves the parabolic recognition independently.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.43, printed p.1140, the characteristic-two paragraphs.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.ParabolicInspection

variable {G : Type*} [Group G]

/-- A maximal proper invariant overgroup of the chosen Sylow normalizer.
In the incoming Lie models these are precisely the standard parabolics
maximal subject to invariance under `S`. -/
structure MaximalInvariantParabolic (L S P : Subgroup G) : Prop where
  contains_borel : ChapterF.Source.borel L S ≤ P
  proper : P < L
  invariant : S ≤ normalizer (P : Set G)
  maximal : ∀ Q : Subgroup G, ChapterF.Source.borel L S ≤ Q → Q < L →
    S ≤ normalizer (Q : Set G) → P ≤ Q → Q ≤ P

/-- The literal `M_L⁺` in `I/C_I(L)`, with the actual images of `L` and `S`.
This predicate is not assumed by `ReducedConfiguration`. -/
def QuotientParabolic {Yplus S M I L V₁ V₂ : Subgroup G}
    (c : ReducedConfiguration Yplus S M I L V₁ V₂) : Prop :=
  MaximalInvariantParabolic (c.toComponentAction.image L) (c.toComponentAction.image S)
    (c.toComponentAction.image M ⊓ c.toComponentAction.image L)

end CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.ParabolicInspection
