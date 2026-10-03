module
public import Stellmacher.SectionTen.TenOneSmallCommonConclusions
public import Stellmacher.SectionTen.TenOneSmallSylowLower
public import Stellmacher.SectionTen.TenOneSmallSylowUpper
public import Stellmacher.SectionTen.TenOneSmallResidualExtraspecial
public import Stellmacher.SectionTen.TenOneSmallNonsolvableCentralizer

/-!
# The complete small alternative of Stellmacher (10.1)

For the actual ambient Section Ten context, an order-eight first module
with first local quotient SL₂(2) gives the complete small alternative.
The supplied W is its literal conjugate closure; the full conclusion also
retains the supplied definitions of W0 and the generated neighborhood.
The nonsolvable involution centralizer remains in the original ambient H.

The assembly combines the proved Sylow bounds, opening local quotient,
generated-center equality, middle C4×C4 residual model, and first
extraspecial residual of order32. The completed small centralizer argument
supplies the actual embedded nonsolvable involution witness. Combining
these with the proved common index and derived-intersection equations
gives the full ambient conclusion. No classification field or obstruction
is added as a hypothesis.

Source: Stellmacher (10.1)(a), Journal of Algebra 190 (1997), printed
pp.59–62. The two public exports isolate the small alternative and its
combination with the common conclusions for the final (10.1) case split.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_small_alternative
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex) (W W0 Wnext : Subgroup G)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hW : W=conjugateClosure
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ middle))
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep)=8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two) :
    AmbientLemmaTenOneAlternative ctx middle W W0 Wnext := by
  apply AmbientLemmaTenOneAlternative.a
  · exact ⟨ten_one_small_sylow_card_lower ctx middle hpath hsmall hmodel,
      ten_one_small_sylow_card_upper ctx middle hpath hsmall hmodel⟩
  · exact ⟨hmodel,(sectionTenOpeningData ctx middle hpath).quotient_model⟩
  · exact ⟨(hW.trans (ten_one_small_generated_eq_center ctx middle hpath hsmall)).symm,
      ten_one_middle_residual_c4_square ctx middle hpath hsmall hmodel⟩
  · exact ⟨hsmall,ten_one_small_residual_extraspecial ctx middle hpath hsmall hmodel⟩
  · exact ten_one_small_nonsolvable_centralizer ctx middle hpath hsmall hmodel

public theorem ten_one_small_conclusion
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex) (W W0 Wnext : Subgroup G)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hW : W=conjugateClosure
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ middle))
    (hWnext : Wnext=GeneratedNeighborhoodV ctx.Γ middle)
    (hW0 : W0=NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle) ⊓ Wnext)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep)=8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two) :
    AmbientLemmaTenOneConclusion ctx middle W W0 Wnext := by
  have hc := ten_one_small_common_conclusions ctx middle W W0 Wnext hpath hW hWnext hW0 hsmall hmodel
  exact ⟨⟨hW,hWnext,hW0⟩,hc.1,hc.2,
    ten_one_small_alternative ctx middle W W0 Wnext hpath hW hsmall hmodel⟩

end Stellmacher.SectionTen
