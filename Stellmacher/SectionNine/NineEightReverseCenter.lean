module
public import Stellmacher.SectionNine.NineEightTerminalTransvection
public import Stellmacher.SectionNine.NineEightNoncontainedResidual
public import Stellmacher.SectionNine.NineNextTransvectionResidual

/-!
# Reverse center containment forced in the second branch of (9.8)

Under the original (9.8) containment, suppose the first extracted neighbor
center escapes the initial stabilizer. Then the first-step center lies
in the terminal module. This eliminates the nonreverse-containment case
without using the unfinished (9.7) or (9.8).

If the reverse containment failed, (1.2) and the fixed-coatom argument
would give an actual transvection on the terminal V/Z quotient.
Endpoint alignment transports its commutator index back to the first step.
The canonical-factor residual theorem then makes the first-step residual
image in its ordinary two-core quotient elementary three, contradicting
the proper-normalizer obstruction supplied by the extracted center.

Source: Stellmacher (9.8), printed p.55/PDF p.45, contradiction to (*)
in the case Zfirst is not contained in Vterminal.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

private theorem transvection_at_first_of_terminal
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (actor : GAt ctx.Γ ctx.criticalPath.a')
    (hindex : QuotientCardEq
      (⁅VAt ctx.Γ ctx.criticalPath.a',Subgroup.zpowers (actor : G)⁆ ⊔ ZAt ctx.Γ ctx.criticalPath.a')
      (ZAt ctx.Γ ctx.criticalPath.a') 2) :
    ∃ firstActor : GAt ctx.Γ ctx.criticalPath.firstStep,
      QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.firstStep,Subgroup.zpowers (firstActor : G)⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.firstStep) (ZAt ctx.Γ ctx.criticalPath.firstStep) 2 := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  obtain ⟨alignment,_,halignment⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  let e := MulAut.conj alignment⁻¹
  have hactor : (actor : G) ∈ (GAt Γ cp.firstStep).map e.toMonoidHom := by
    have heq : GAt Γ cp.a' = (GAt Γ cp.firstStep).map e.toMonoidHom := by
      change stabilizer Γ cp.a' = _
      rw [← halignment,stabilizer_act]
      rfl
    exact heq.le actor.property
  obtain ⟨first,hfirst,hfirstActor⟩ := hactor
  refine ⟨⟨first,hfirst⟩,?_⟩
  have hV : VAt Γ cp.a' = (VAt Γ cp.firstStep).map e.toMonoidHom := by
    change v Γ cp.a' = _
    rw [← halignment,v_act]
  have hZ : ZAt Γ cp.a' = (ZAt Γ cp.firstStep).map e.toMonoidHom := by
    change z Γ cp.a' = _
    rw [← halignment,z_act]
  have hcyclic : Subgroup.zpowers (actor : G) = (Subgroup.zpowers first).map e.toMonoidHom := by
    rw [MonoidHom.map_zpowers,hfirstActor]
  change Nat.card (⁅VAt Γ cp.a',Subgroup.zpowers (actor : G)⁆ ⊔ ZAt Γ cp.a' : Subgroup G) =
    2 * Nat.card (ZAt Γ cp.a') at hindex
  rw [hV,hZ,hcyclic,← Subgroup.map_commutator,← Subgroup.map_sup,
    Subgroup.card_map_of_injective e.injective,Subgroup.card_map_of_injective e.injective] at hindex
  exact hindex

public theorem nine_eight_reverse_center_contained_of_extracted_escape
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 3 < ctx.criticalPath.length)
    (hcontain : ZAt ctx.Γ ctx.criticalPath.a' ≤ VAt ctx.Γ ctx.criticalPath.firstStep)
    (neighbor : ctx.Γ.Vertex) (hneighbor : neighbor ∈ neighborhood ctx.Γ ctx.criticalPath.a')
    (hindex : QuotientCardEq (GeneratedNeighborhoodV ctx.Γ ctx.criticalPath.a)
      (GeneratedNeighborhoodV ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ neighbor) 2)
    (hnot : ¬ ZAt ctx.Γ ctx.criticalPath.a ≤ GAt ctx.Γ neighbor)
    (hescape : ¬ ZAt ctx.Γ neighbor ≤ GAt ctx.Γ ctx.criticalPath.a) :
    ZAt ctx.Γ ctx.criticalPath.firstStep ≤ VAt ctx.Γ ctx.criticalPath.a' := by
  by_contra hreverseNot
  have hlong : 1 < ctx.criticalPath.length := by omega
  obtain ⟨actor,_,_,_,htransvection⟩ :=
    nine_eight_terminal_transvection_of_reverse_noncontainment ctx hlong hreverseNot
  obtain ⟨firstActor,hfirstTransvection⟩ := transvection_at_first_of_terminal ctx actor htransvection
  have helementary := nine_next_residual_elementary_of_transvection ctx hlong
    ctx.criticalPath.firstStep ⟨1,ctx.Γ.act_one _⟩ firstActor hfirstTransvection
  exact nine_eight_noncontained_residual_image_not_elementary_three ctx hb hcontain
    neighbor hneighbor hindex hnot hescape helementary

end Stellmacher.SectionNine
