module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OrderTwo.MathieuTwelve.Algebra

/-!
# The remaining centerless M₁₂ model calculation

The first clause is the actual automorphism-generation assertion for an outer
involution. The second is the identity ⟨sL⟩ = [C_TL(s),r], with the original
ambient involution, its marked quotient image and its actual coordinates all
retained. The algebra module constructs those coordinates; this contract does
not assume s = sL, centrality of TC, or the final noncommuting witness.

This is a specification for the model prerequisite, not an assertion that it
holds. Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 16.4.9(1), printed p.1189, case (III) with O₂(L) = 1.
-/

@[expose] public section

open Subgroup Theory.GroupTheory.DoubleCoverCentralizer
namespace CFSG.Quasithin.Chapter16.Intersections.OrderTwo.MathieuTwelve

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g : G} {L R : Subgroup G}

/-- The intrinsic model outputs still required in the centerless branch. -/
def CenterlessLocalCalculation (h : IntersectionSetup T z L g R) (r : G) : Prop :=
  (normalizer (L : Set G) ≤ (centralizer (L : Set G) ⊔ L) ⊔ zpowers r) ∧
    ∀ s : R, orderOf (s : G) = 2 → ∀ u : L ⧸ center L,
      ¬ TwoCentral u →
      (centerQuotientEquivActionImage L u : ActionQuotient L) =
        actionMap (h.le_sylow.trans h.sylow_normalizes) s →
      ∀ v ∈ componentSylow T L, ∀ c ∈ commutingSylow T L,
        (s : G) = v * c →
        zpowers v = ⁅componentSylow T L ⊓ involutionCentralizer (s : G), zpowers r⁆

end CFSG.Quasithin.Chapter16.Intersections.OrderTwo.MathieuTwelve
