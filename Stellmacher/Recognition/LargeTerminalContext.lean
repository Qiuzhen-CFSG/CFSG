module

public import Stellmacher.SectionEleven.MultipleMaximalRichTerminal

/-!
# The actual large terminal context retained for global recognition

This bundles the original pair and Sylow terminal context from Section11,
the commuting critical endpoints at distance three, and the proved absence
of quotient transvections. The ambient two-local structure is retained as
well. It is obtained after excluding the strongly embedded and odd-core
alternatives in the N2 reduction. The graph group is the actual generated
join, with its prescribed ambient Sylow restriction and inclusion.

The context exposes the hypotheses of the proved large Section Ten lemmas;
it assumes no full involution-centralizer equality, core order, or global
model recognition. It supplements the original local type without changing
that definition. Source: Stellmacher, Section11 and(10.1).
-/

namespace Stellmacher.Recognition
open Later SectionsFiveToSeven SectionEleven
universe u

/-- The source's large Section Ten data with its original ambient context. -/
public structure LargeTerminalContext
    {G : Type u} [Group G] [Finite G] (S0 : Sylow 2 G) where
  first : Subgroup G
  second : Subgroup G
  terminal : SylowTerminalContext G S0 first second
  localStructure : ∀ U : Subgroup G, IsTwoLocal U →
    Group.IsSolvable U ∧ IsCharacteristicTwoType U
  commuting : ⁅terminal.Γ.z terminal.criticalPath.a,
    terminal.Γ.z terminal.criticalPath.a'⁆ = ⊥
  length_three : terminal.criticalPath.length = 3
  noTransvections :
    ∀ actor : (first ⊔ second : Subgroup G),
      actor ∈ VAt terminal.Γ terminal.criticalPath.firstStep →
      actor ∉ QAt terminal.Γ terminal.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt terminal.Γ terminal.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt terminal.Γ terminal.criticalPath.a')
        (ZAt terminal.Γ terminal.criticalPath.a') 2

end Stellmacher.Recognition
