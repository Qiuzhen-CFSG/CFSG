module

public import Stellmacher.SectionEight.EightFourOppositeClosure
public import Stellmacher.SectionEight.EightFourSylowOffenderGeneration

/-!
# The opposite-center closure has the full barred offender image

In the noncommuting local Section Eight critical-pair context, the normal closure
S1 of the opposite endpoint center inside the first-step stabilizer maps
onto the full offender join for the faithful action on the initial center.
The quotient-module witness keeps that original module and its exact action.
The canonical public theorem is a wrapper through the identical local graph.
The central-first-step hypothesis and the source's nontrivial fixed-center
closure branch are retained explicitly, although the two image bounds do
not require them.

For the upper bound, the graph and local index argument makes every
first-step-stabilizer conjugate of the opposite center project into the
offender join. For the lower bound, S1 contains the opposite center and is
normal in the distinguished Sylow. The local Sylow-generation theorem uses
the unique-maximal residual structure and the selected SL2(2) factors from
(8.1) and (1.7) to put the whole offender join in its image. Antisymmetry
gives the equality; offender membership alone would not suffice.

This is the opening image assertion in Stellmacher (8.4), journal p.38 of
`refs/files/stellmacher-n-group.pdf`. Combined with the re-exported
fixed-centralizer transport, it gives source (3), used on pp.39–40. Neither
the later normality assertion nor (8.3), (6.4), or numbered (7.8) is used.
-/

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven CosetGraphContext

universe u

public theorem eight_four_opposite_closure_image_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (_hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (_hbranch : (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype ≠ w.oneJFixedPoints S) :
    let _ := w.groupX
    let _ := MulDistribMulAction.compHom (ZAt ctx.Γ ctx.criticalPath.a) w.action
    ((oppositeClosureLocal ctx).subgroupOf (GAt ctx.Γ ctx.criticalPath.a)).map w.projection =
      SectionOne.oneJ (V := ZAt ctx.Γ ctx.criticalPath.a)
        ((S.subgroupOf (GAt ctx.Γ ctx.criticalPath.a)).map w.projection) := by
  let := w.groupX
  let := MulDistribMulAction.compHom (ZAt ctx.Γ ctx.criticalPath.a) w.action
  exact le_antisymm (opposite_closure_image_le_oneJ_local ctx w)
    (eight_four_oneJ_le_of_normal_sylow_local ctx w (oppositeClosureLocal ctx)
      (opposite_closure_normal_sylow_local ctx) (opposite_center_le_opposite_closure_local ctx))

public theorem eight_four_opposite_closure_image
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (_hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (_hbranch : (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype ≠ w.oneJFixedPoints S) :
    let _ := w.groupX
    let _ := MulDistribMulAction.compHom (ZAt ctx.Γ ctx.criticalPath.a) w.action
    ((oppositeClosure ctx).subgroupOf (GAt ctx.Γ ctx.criticalPath.a)).map w.projection =
      SectionOne.oneJ (V := ZAt ctx.Γ ctx.criticalPath.a)
        ((S.subgroupOf (GAt ctx.Γ ctx.criticalPath.a)).map w.projection) := by
  exact eight_four_opposite_closure_image_local ctx.toLocalContext _hcenter w _hbranch

end Stellmacher.SectionEight
