module

public import Stellmacher.SectionNine.NineFiveSupportData

/-!
# Support selection inputs for the two-conjugate argument in (9.5)

This record is not an existence assertion. Its producer must select an actual
lifted four-element factor from the faithful terminal quotient module and
prove the intersection controls. The span and the choice of conjugator are
deliberately absent: those come from the penultimate residual argument on
printed p.53, following the factor decomposition on printed p.52.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven

universe u

public structure NineFiveSupportSeed
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (prev : ctx.Γ.Vertex) (actor : G) where
  support : Subgroup G
  support_le : support ≤ VAt ctx.Γ ctx.criticalPath.a'
  center_card : Nat.card (ZAt ctx.Γ ctx.criticalPath.a') = 2
  center_le : ZAt ctx.Γ ctx.criticalPath.a' ≤ support
  support_index : QuotientCardEq support (ZAt ctx.Γ ctx.criticalPath.a') 4
  commutator_le : ⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ≤ support
  residual_normalizes : EAt ctx.Γ ctx.criticalPath.a' ≤
    Subgroup.normalizer (support : Set G)
  support_intersection : ∀ conjugator : G,
    conjugator ∈ twoCoreIn (EAt ctx.Γ
      (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)) →
    support ≠ support.map (MulAut.conj conjugator⁻¹).toMonoidHom →
    support ⊓ support.map (MulAut.conj conjugator⁻¹).toMonoidHom =
      ZAt ctx.Γ ctx.criticalPath.a'
  neighbor_intersection : ∀ conjugator : G,
    conjugator ∈ twoCoreIn (EAt ctx.Γ
      (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)) →
    VAt ctx.Γ ctx.criticalPath.a' =
      support ⊔ support.map (MulAut.conj conjugator⁻¹).toMonoidHom →
    support ≠ support.map (MulAut.conj conjugator⁻¹).toMonoidHom →
    Nat.card (VAt ctx.Γ ctx.criticalPath.a' ⊓ VAt ctx.Γ prev : Subgroup G) = 2 ^ 3

end Stellmacher.SectionNine
