module
public import Stellmacher.SectionTen.TenOneWreathExclusion
/-!
# A quotient transvection forces the first small case in (10.1)

An actual first-module actor outside the terminal core with order-two
displacement on terminal V/Z forces the first module to have order eight
and its local quotient to be SL2(2). These are precisely the inputs used
by the small-case Section Ten producers.

The exact quotient-facing (9.5) alternatives give the terminal small case
or its wreath alternative. The proved wreath exclusion eliminates the
latter. Existing endpoint alignment transports both module cardinality
and the literal local quotient model back to the first step.

Source: Stellmacher (10.1), printed p.60/PDF p.50, alternatives (5),(6) and
the exclusion of (5), `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}
public theorem ten_one_transvection_small_first
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (actor : G)
    (hactor : actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep)
    (hout : actor ∉ QAt ctx.Γ ctx.criticalPath.a')
    (hindex : QuotientCardEq
      (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
        ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2) :
    Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8 ∧
      QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
        (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two := by
  have hcases := ten_one_quotient_transvection_cases ctx middle hpath actor hactor hout hindex
  have hsmall := hcases.resolve_right (by
    rintro ⟨hlarge, hmodel, hIcard⟩
    exact ten_one_wreath_alternative_false ctx middle hpath actor hactor hindex hlarge hmodel hIcard)
  exact ⟨(nine_seven_endpoint_module_card ctx.toLocalContext.toSectionNineLocalContext).trans hsmall.1,
    (nine_seven_endpoint_quotient_model_iff ctx.toLocalContext.toSectionNineLocalContext).mpr hsmall.2⟩
end Stellmacher.SectionTen
