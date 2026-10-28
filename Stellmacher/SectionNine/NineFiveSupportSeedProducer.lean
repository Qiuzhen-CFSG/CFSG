module

public import Stellmacher.SectionNine.NineFiveSupportLift
public import Stellmacher.SectionNine.NineFiveSupportSeed
public import Stellmacher.SectionNine.NineFiveNeighborIntersection

/-!
# Canonical support seed for Stellmacher (9.5)

The faithful terminal quotient action supplies the canonical Section One
factor selected by the transvection. Its four-element quotient support lifts
to the terminal module and satisfies every source field of
`NineFiveSupportSeed`: the center and index-four layer, the prescribed
commutator, residual normalization, and distinct conjugate intersection.
The neighboring intersection is discharged by the graph theorem proved from
the previous-commutation control and the complementary-factor fixed-space
calculation. The quotient action, factor, and support image are retained in
the existential result for later order-eight and wreath recognition.

Source: Stellmacher (9.5), printed pp.52–53/PDF pp.42–43 of
`refs/files/stellmacher-n-group.pdf`; the faithful quotient and
transvection factor are the formalized (9.3)–(9.4) inputs.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext
universe u

public theorem nine_five_support_seed
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length) (prev : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath
      (ctx.criticalPath.length - 2) prev)
    (actor : G)
    (hactor : actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep ∧
      actor ∉ QAt ctx.Γ ctx.criticalPath.a')
    (hindex : QuotientCardEq
      (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
        ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2)
    (hcontain : ⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ≤
      VAt ctx.Γ prev) :
    ∃ hN : ((ZAt ctx.Γ ctx.criticalPath.a').subgroupOf
      (VAt ctx.Γ ctx.criticalPath.a')).Normal,
    let _ := hN
    let P := GAt ctx.Γ ctx.criticalPath.a'
    let U := VAt ctx.Γ ctx.criticalPath.a'
    let Z := ZAt ctx.Γ ctx.criticalPath.a'
    ∃ hW : IsElementaryAbelian 2 (U ⧸ Z.subgroupOf U),
    let _ := hW
    ∃ action : P →* MulAut (U ⧸ Z.subgroupOf U),
      (∀ mover : P, ∀ point : U,
        action mover (QuotientGroup.mk' (Z.subgroupOf U) point) =
          QuotientGroup.mk' (Z.subgroupOf U)
            ⟨(mover : G) * (point : G) * (mover : G)⁻¹,
              (Subgroup.mem_normalizer_iff.mp
                (stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.a' mover.property)
                  point).mp point.property⟩) ∧
      action.ker = pCore 2 P ∧
      SectionOne.Hypotheses action.range (U ⧸ Z.subgroupOf U) ∧
    ∃ factor : Subgroup action.range,
      SectionOne.IsOneSevenFactor (V := U ⧸ Z.subgroupOf U) factor ∧
    ∃ seed : NineFiveSupportSeed ctx.toLocalContext prev actor,
      (seed.support.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U)) =
        commutatorAction factor (U ⧸ Z.subgroupOf U) := by
  let actorP : GAt ctx.Γ ctx.criticalPath.a' :=
    ⟨actor, (lemma_seven_four ctx.sectionSeven ctx.Γ ctx.criticalPath).first_containment.2
      hactor.1⟩
  obtain ⟨hcenterCard, hN, hW, action, hact, hkernel, hinv, htwo, hrank, hyp,
    factor, hfactor, hfactorActor, support, hsupport, hcenter, hsupportIndex,
    hcommutator, hnormal, himage, hintersection⟩ :=
    nine_five_support_lift ctx hb actorP hindex
  let _ := hN
  let _ := hW
  let seed : NineFiveSupportSeed ctx.toLocalContext prev actor := {
    support := support
    support_le := hsupport
    center_card := hcenterCard
    center_le := hcenter
    support_index := hsupportIndex
    commutator_le := hcommutator
    residual_normalizes := hnormal
    support_intersection := hintersection
    neighbor_intersection := nine_five_neighbor_intersection ctx hb prev hpath
      actorP hactor.1 hcontain hN hW action hact hyp factor hfactor hfactorActor
      hrank support hsupport hcenter himage }
  exact ⟨hN, hW, action, hact, hkernel, hyp, factor, hfactor, seed, himage⟩

end Stellmacher.SectionNine
