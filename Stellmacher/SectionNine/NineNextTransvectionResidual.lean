module
public import Stellmacher.SectionNine.NineNextTransvectionFactor
public import Stellmacher.SectionNine.NineResidualElementary
public import Theory.GroupTheory.ElementaryQuotientImage

/-!
# Elementary residual images from next-orbit transvections

An actual transvection on a next-orbit quotient V/Z forces the local
two-residual image in the ordinary two-core quotient to be elementary
abelian at three. Both the ambient and graph contexts remain explicit.

The existing transvection-factor theorem supplies the literal quotient
action, its exact two-core kernel, and a canonical Section One factor.
Local residual identification and the canonical factor product make the
residual image elementary three in the action range. The exact-kernel
quotient equivalence transfers this to the ordinary two-core quotient.

This is the local (1.7)/(7.7) consequence used in Stellmacher (9.8),
printed p.55, and (9.10), printed p.57.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_next_residual_elementary_of_transvection
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length) (vertex : ctx.Γ.Vertex)
    (horbit : IsConjugateVertex ctx.Γ ctx.criticalPath.firstStep vertex)
    (actor : GAt ctx.Γ vertex)
    (hindex : QuotientCardEq
      (⁅VAt ctx.Γ vertex, Subgroup.zpowers (actor : G)⁆ ⊔ ZAt ctx.Γ vertex)
      (ZAt ctx.Γ vertex) 2) :
    IsElementaryAbelian 3
      (((EAt ctx.Γ vertex).subgroupOf (GAt ctx.Γ vertex)).map
        (QuotientGroup.mk' (pCore 2 (GAt ctx.Γ vertex)))) := by
  obtain ⟨hN,hW,action,_,hkernel,_,_,_,hyp,hfactor⟩ :=
    nine_next_transvection_factor ctx hb vertex horbit actor hindex
  let _ := hN
  let _ := hW
  obtain ⟨alignment,halignment⟩ := horbit
  have hadj : ctx.Γ.adjacent vertex (ctx.Γ.act alignment ctx.criticalPath.a) := by
    rw [← halignment]
    exact adjacent_act ctx.Γ alignment (ctx.Γ.adjacent_symm ctx.criticalPath.firstStep_adj)
  have hkerRange : action.rangeRestrict.ker = pCore 2 (GAt ctx.Γ vertex) := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hkernel
  have helementary := nine_local_residual_isElementaryAbelian_of_factor ctx.toLocalContext
    vertex (ctx.Γ.act alignment ctx.criticalPath.a) hadj action.rangeRestrict
    action.rangeRestrict_surjective hkerRange.symm.le hyp _ hfactor
  exact Subgroup.elementary_quotient_image_of_exact_kernel _ _ action.rangeRestrict
    action.rangeRestrict_surjective hkerRange helementary

end Stellmacher.SectionNine
