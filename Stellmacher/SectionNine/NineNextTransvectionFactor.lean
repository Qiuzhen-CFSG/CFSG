module
public import Stellmacher.SectionNine.NineNextTransvectionActor
public import Stellmacher.SectionOne.CoreKernelTransvectionFactor

/-!
# A canonical transvection factor in the next-orbit quotient

For a next-orbit vertex at critical distance greater than one, the source
order-two displacement condition selects a canonical Section One factor
inside the literal automorphism range of the quotient V/Z. The returned
normality witness, elementary abelian structure, conjugation action,
two-core kernel, and induced involution are precisely those used to prove
the displacement condition. The canonical factor retains its four-element
support and odd-core normality.

The neighbor stabilizer is solvable by the Section Seven local hypotheses.
The quotient action from `NineNextTransvectionActor` therefore satisfies
the generic core-kernel transvection factor theorem. This is the concrete
specialization used in Stellmacher (9.4)(1), printed p.51 of
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext
universe u

public theorem nine_next_transvection_factor
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
    ∃ hN : ((ZAt ctx.Γ vertex).subgroupOf (VAt ctx.Γ vertex)).Normal,
      let _ := hN
      let P := GAt ctx.Γ vertex
      let U := VAt ctx.Γ vertex
      let Z := ZAt ctx.Γ vertex
      ∃ hW : IsElementaryAbelian 2 (U ⧸ Z.subgroupOf U),
      let _ := hW
      ∃ action : P →* MulAut (U ⧸ Z.subgroupOf U),
        (∀ mover : P, ∀ point : U,
          action mover (QuotientGroup.mk' (Z.subgroupOf U) point) =
            QuotientGroup.mk' (Z.subgroupOf U)
              ⟨(mover : G) * (point : G) * (mover : G)⁻¹,
                (Subgroup.mem_normalizer_iff.mp
                  (stabilizer_le_normalizer_v ctx.Γ vertex mover.property) point).mp
                    point.property⟩) ∧
        action.ker = pCore 2 P ∧
        _root_.IsInvolution (action actor) ∧
        Nat.card (Subgroup.zpowers (action actor)) = 2 ∧
        Nat.card (commutatorAction (Subgroup.zpowers (action actor))
          (U ⧸ Z.subgroupOf U)) = 2 ∧
        SectionOne.Hypotheses action.range (U ⧸ Z.subgroupOf U) ∧
        SectionOne.IsOneSevenFactor (V := U ⧸ Z.subgroupOf U)
          (⁅SectionOne.oddCore action.range,
              Subgroup.zpowers (action.rangeRestrict actor)⁆ ⊔
            Subgroup.zpowers (action.rangeRestrict actor)) := by
  obtain ⟨hN, hW, action, haction, hkernel, hinvolution, hcard, hrank⟩ :=
    nine_next_transvection_actor ctx hb vertex horbit actor hindex
  let _ := hN
  let _ := hW
  have hsolvable : Group.IsSolvable (GAt ctx.Γ vertex) := by
    obtain ⟨mover, hmover⟩ := horbit
    apply stabilizer_solvable_of_neighbor ctx.sectionSeven ctx.Γ
      (l := ctx.Γ.act mover ctx.criticalPath.a)
    apply (SevenSix.mem_neighborhood_iff_adjacent ctx.Γ).mpr
    rw [← hmover]
    exact adjacent_act ctx.Γ mover
      (ctx.Γ.adjacent_symm ctx.criticalPath.firstStep_adj)
  exact ⟨hN, hW, action, haction, hkernel, hinvolution, hcard, hrank,
    SectionOne.core_kernel_transvection_factor hsolvable action hkernel actor hrank⟩

end Stellmacher.SectionNine
