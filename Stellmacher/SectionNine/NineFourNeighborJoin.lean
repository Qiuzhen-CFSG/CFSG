module
public import Stellmacher.SectionNine.LemmaNineThree
public import Stellmacher.SectionNine.CubicLocalAction
public import Stellmacher.SectionNine.NineSevenNormalityObstructions

/-!
# Generating the initial neighborhood from a normalized pair

For critical distance greater than one, consider the first-step module and
one other module at a neighbor of the initial vertex. If the next residual
two-core normalizes their join, this join is the full initial neighborhood
module and is normalized by the initial stabilizer.

By (7.6)(b), the next residual two-core is not contained in the initial
core. The cubic local action supplied by (9.3) therefore makes that core
transitive on the two neighbors other than the first step. Invariance of
the pair's join brings both of their modules into it, and the definition
of the neighborhood join gives equality. Its own stabilizer normalizes it.

This proves the neighborhood-generation inference in the proof of (9.4)(4),
printed p.51 of `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_four_initial_neighborhood_eq_join
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (remote : ctx.Γ.Vertex)
    (hremote : remote ∈ Neighborhood ctx.Γ ctx.criticalPath.a)
    (hne : remote ≠ ctx.criticalPath.firstStep)
    (hnormal : twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep) ≤
      Subgroup.normalizer ((VAt ctx.Γ ctx.criticalPath.firstStep ⊔
        VAt ctx.Γ remote : Subgroup G) : Set G)) :
    GeneratedNeighborhoodV ctx.Γ ctx.criticalPath.a =
      VAt ctx.Γ ctx.criticalPath.firstStep ⊔ VAt ctx.Γ remote ∧
    GAt ctx.Γ ctx.criticalPath.a ≤
      Subgroup.normalizer ((VAt ctx.Γ ctx.criticalPath.firstStep ⊔
        VAt ctx.Γ remote : Subgroup G) : Set G) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let R := twoCoreIn (EAt Γ cp.firstStep)
  let W := VAt Γ cp.firstStep ⊔ VAt Γ remote
  have hmodel := (lemma_nine_three_ambient ctx hb cp.a ⟨1, Γ.act_one _⟩).1
  have hRnot : ¬ R ≤ QAt Γ cp.a :=
    (lemma_seven_six ctx.sectionSeven Γ cp).next_residual_core.1
  have hRQ : R ≤ QAt Γ cp.firstStep := by
    change twoCoreIn (Γ.twoResidualAt cp.firstStep) ≤ Γ.twoCoreAt cp.firstStep
    rw [Γ.twoResidualAt_def, Γ.twoCoreAt_def, residual_core_eq_inter_core]
    exact inf_le_right
  have hRle : R ≤ GAt Γ cp.a ⊓ GAt Γ cp.firstStep :=
    hRQ.trans ((local_cores_le_edge_sylow ctx.sectionSeven Γ cp).2.trans
      cp.S_le_edge_stabilizers)
  have htrans := (cubic_local_action_of_sl2Two_quotient Γ ctx.sectionSeven
    cp.a hmodel).punctured_transitivity cp.firstStep cp.firstStep_adj R hRle hRnot
  have hjoin : GeneratedNeighborhoodV Γ cp.a = W := by
    apply le_antisymm
    · apply sSup_le
      rintro moduleGroup ⟨neighbor, hneighbor, rfl⟩
      by_cases hnext : neighbor = cp.firstStep
      · subst neighbor
        exact le_sup_left
      obtain ⟨mover, hmover⟩ := htrans ⟨hremote, hne⟩ ⟨hneighbor, hnext⟩
      change v Γ neighbor ≤ W
      rw [← hmover, v_act]
      rintro point ⟨original, horiginal, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (hnormal (R.inv_mem mover.property)) original).mp
        ((le_sup_right : VAt Γ remote ≤ W) horiginal)
    · exact sup_le
        (nine_seven_neighbor_module_le_neighborhood Γ cp.firstStep_adj)
        (nine_seven_neighbor_module_le_neighborhood Γ
          ((mem_neighborhood_iff_adjacent Γ).mp hremote))
  refine ⟨hjoin, ?_⟩
  change GAt Γ cp.a ≤ Subgroup.normalizer (W : Set G)
  rw [← hjoin]
  exact nine_seven_stabilizer_normalizes_neighborhood Γ cp.a

end Stellmacher.SectionNine
