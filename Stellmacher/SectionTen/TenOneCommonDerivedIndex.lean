module
public import Stellmacher.SectionTen.TenOneSmallCommonConclusions
public import Stellmacher.SectionTen.TenOneLargeDerived

/-!
# Common derived and index conclusions for Section Ten

This module combines the proved source-case producers for the common
neighborhood. In the small `(8, SL₂(2))` case it exposes all three immediate
quotient indices, including the intermediate `Wnext/W₀` index four. In the
large case it consumes only the source intersection-cardinality and
no-transvection outputs; the proved large-derived theorem supplies the common
equality and its quotient by the middle centre. The source-large calculations
for the remaining `W/W'`, `Wnext/W₀`, and residual-core joins remain separate
producers and are intentionally not smuggled in as assumptions here.

The disjunction in `ten_one_common_derived_of_source_case` consists of source
case data, not any desired common conclusion. Definitions of `W`, `W₀`, and
`Wnext` remain explicit so this assembly can feed the corrected (10.1) record.

Source: Stellmacher (10.1), printed pp. 59--65, especially the common
derived equality after (4), the small case (6), and the large case (12)--(14).
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_common_derived_of_source_case
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (W W0 Wnext : Subgroup G)
    (hW : W = conjugateClosure
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ middle))
    (hWnext : Wnext = GeneratedNeighborhoodV ctx.Γ middle)
    (hW0 : W0 = NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle) ⊓ Wnext)
    (hcase :
      (Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8 ∧
        QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
          (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two) ∨
      (Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep ⊓
          VAt ctx.Γ ctx.criticalPath.a' : Subgroup G) = 8 ∧
        (∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
          actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
            (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
              ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2))) :
    DerivedAmbient Wnext =
      VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ ctx.criticalPath.a' := by
  rcases hcase with ⟨hsmall, hmodel⟩ | ⟨hlarge, hno⟩
  · exact (ten_one_small_common_conclusions ctx middle W W0 Wnext hpath hW hWnext hW0
      hsmall hmodel).2
  · rw [hWnext]
    exact ten_one_large_derived ctx middle hpath hlarge hno

public theorem ten_one_small_common_index_chain
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (W W0 Wnext : Subgroup G)
    (hW : W = conjugateClosure
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ middle))
    (hWnext : Wnext = GeneratedNeighborhoodV ctx.Γ middle)
    (hW0 : W0 = NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle) ⊓ Wnext)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two) :
    QuotientCardEq W0 W 2 ∧ QuotientCardEq Wnext W (2 ^ 3) ∧
      QuotientCardEq Wnext W0 4 ∧
      DerivedAmbient Wnext =
        VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ ctx.criticalPath.a' := by
  obtain ⟨hindices, hderived⟩ := ten_one_small_common_conclusions ctx middle W W0 Wnext
    hpath hW hWnext hW0 hsmall hmodel
  exact ⟨hindices.1, hindices.2, by
    rw [hW0, hWnext]
    exact ten_one_small_neighborhood_core_index ctx middle hpath hsmall hmodel, hderived⟩

end Stellmacher.SectionTen
