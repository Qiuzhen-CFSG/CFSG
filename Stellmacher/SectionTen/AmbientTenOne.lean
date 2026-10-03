module
public import Stellmacher.SectionTen.TenOneSmallAlternative
public import Stellmacher.SectionTen.TenOneTransvectionSmallFirst
public import Stellmacher.SectionTen.TenOneLargeAlternative

/-!
# The complete ambient (10.1) classification

For the original ambient-retaining Section Ten context, the prescribed
subgroups W, W0 and Wnext satisfy the common index and derived equations
and one of the two source configurations. The graph stays in G while the
involution centralizer obstruction stays in the original ambient H.

Split on whether a first-module actor outside the terminal core acts as
a transvection on the quotient module. The proved transvection reduction
supplies the exact small model, and its complete alternative includes the
ambient nonsolvable centralizer. Otherwise the complete large alternative
supplies the Frobenius20 quotient and all order and structure fields.

Source: Stellmacher (10.1), printed59–65. The following legacy wrapper
uses the identity embedding to preserve its original public interface.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ambient_lemma_ten_one
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex) (W W0 Wnext : Subgroup G)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hW : W=conjugateClosure
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ middle))
    (hWnext : Wnext=GeneratedNeighborhoodV ctx.Γ middle)
    (hW0 : W0=NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle) ⊓ Wnext) :
    AmbientLemmaTenOneConclusion ctx middle W W0 Wnext := by
  classical
  by_cases hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
    actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
      (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
        ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2
  · exact ten_one_large_conclusion ctx middle W W0 Wnext hpath hW hWnext hW0 hno
  · push Not at hno
    obtain ⟨actor,hactor,hout,hindex⟩ := hno
    obtain ⟨hsmall,hmodel⟩ :=
      ten_one_transvection_small_first ctx middle hpath actor hactor hout hindex
    exact ten_one_small_conclusion ctx middle W W0 Wnext hpath hW hWnext hW0 hsmall hmodel

end Stellmacher.SectionTen
