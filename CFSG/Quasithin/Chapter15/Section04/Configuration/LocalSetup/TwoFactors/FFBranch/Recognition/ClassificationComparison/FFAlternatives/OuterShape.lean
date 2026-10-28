module

public import CFSG.Quasithin.ChapterB.Section05.OuterSixThreeShape
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.NonQuasisimple

/-!
# Extract the actual outer factors without a fixed-space splitting

The old full record implies the separate group configuration by retaining
its exact factors, product map and conjugation witnesses. The converse is
not asserted. Source: Aschbacher–Smith, B.5.6(4), printed p.105.
-/

public section
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
variable {D : Type*} [Group D] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) D V}

/-- Retain all actual group maps, without using any of the four module fields. -/
def OuterSixThreeCase.toGroupShape (h : OuterSixThreeCase ρ) :
    ChapterB.OuterSixThreeShape D where
  first := h.first
  second := h.second
  product := h.product
  product_apply := h.product_apply
  firstEquiv := h.firstEquiv
  secondEquiv := h.secondEquiv
  element := h.element
  generates := h.generates
  firstOuter := h.firstOuter
  secondOuter := h.secondOuter

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
