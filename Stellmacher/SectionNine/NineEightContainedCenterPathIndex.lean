module
public import Stellmacher.SectionNine.NineEightContainedCenterBackwardIndex
public import Stellmacher.SectionNine.NineSevenNearbyNeighborhoodContraction
public import Stellmacher.SectionNine.NineSevenGoldschmidtPaths


/-!
# The source (9.7) interface for the first branch of Stellmacher (9.8)

The contained-center branch has an index-two intersection between every
backward-neighbor V-module and the first-step module. Cubic two-arc
transitivity transports one such pair to offsets one and three of the
actual critical path. The same actor transports both subgroup factors,
so conjugation preserves the intersection and its index.

The conclusion is exactly the path-index hypothesis used by (9.7), with
no invocation of the unfinished numbered theorem. Source: the first
branch of Stellmacher (9.8), printed p.55/PDF p.45 of
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
open scoped Pointwise commutatorElement
universe u

public theorem nine_eight_contained_center_path_index
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 3 < ctx.criticalPath.length)
    (hcontain : ZAt ctx.Γ ctx.criticalPath.a' ≤ VAt ctx.Γ ctx.criticalPath.firstStep)
    (neighbor : ctx.Γ.Vertex) (hneighbor : neighbor ∈ neighborhood ctx.Γ ctx.criticalPath.a')
    (hcontained : ZAt ctx.Γ neighbor ≤ GAt ctx.Γ ctx.criticalPath.a)
    (hindex : QuotientCardEq (GeneratedNeighborhoodV ctx.Γ ctx.criticalPath.a)
      (GeneratedNeighborhoodV ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ neighbor) 2)
    (hnot : ¬ ZAt ctx.Γ ctx.criticalPath.a ≤ GAt ctx.Γ neighbor)
    (hnoncomm : ⁅ZAt ctx.Γ ctx.criticalPath.a, ZAt ctx.Γ neighbor⁆ ≠ ⊥) :
    ∃ third, IsCriticalPathOffset ctx.Γ ctx.criticalPath 3 third ∧
      QuotientCardEq (VAt ctx.Γ ctx.criticalPath.firstStep)
        (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ third) 2 := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hlong : 1 < cp.length := by change 3 < cp.length at hb; omega
  have hmodel := (lemma_nine_three_ambient ctx hlong cp.a ⟨1, Γ.act_one _⟩).1
  obtain ⟨previous, hpreviousAdj, hpreviousNe⟩ := goldschmidt_neighbor_other Γ cp.a cp.firstStep
    (cubic_local_action_of_sl2Two_quotient Γ ctx.sectionSeven cp.a hmodel).degree
  have hprevious := (mem_neighborhood_iff_adjacent Γ).mpr hpreviousAdj
  have hbackward := nine_eight_contained_center_backward_index ctx hb hcontain neighbor hneighbor
    hcontained hindex hnot hnoncomm previous hprevious hpreviousNe
  have hb' : 3 < cp.length := hb
  let second := cp.path ⟨2, by omega⟩
  let third := cp.path ⟨3, by omega⟩
  have hleft : Γ.adjacent second cp.firstStep := by
    have hedge := cp.path_adj ⟨1, by omega⟩
    change Γ.adjacent (cp.path ⟨1, by omega⟩) second at hedge
    rw [cp.path_first] at hedge
    exact Γ.adjacent_symm hedge
  have hright : Γ.adjacent second third := cp.path_adj ⟨2, by omega⟩
  have hdistinct : cp.firstStep ≠ third := by
    have hh := nine_seven_path_vertices_ne Γ cp 1 3 (by omega) (by omega)
    rwa [cp.path_first] at hh
  obtain ⟨aligner, haligner⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity cp.firstStep
    ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj))
    ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hleft))
  have horbit : IsConjugateVertex Γ cp.a second := ⟨aligner, haligner⟩
  obtain ⟨mover, hmovePrevious, _, hmoveFirst⟩ := nine_seven_two_arc_transport ctx.sectionSeven Γ
    hpreviousAdj cp.firstStep_adj hpreviousNe hleft hright hdistinct horbit
    (lemma_nine_three_ambient ctx hlong second horbit).1
  have hcardPrevious : Nat.card (VAt Γ previous) = Nat.card (VAt Γ cp.firstStep) := by
    change Nat.card (v Γ previous) = Nat.card (v Γ cp.firstStep)
    rw [← hmovePrevious, v_act]
    exact (Subgroup.card_map_of_injective (MulAut.conj mover⁻¹).injective).symm
  have hmap : (VAt Γ previous ⊓ VAt Γ cp.firstStep).map (MulAut.conj mover⁻¹).toMonoidHom =
      VAt Γ cp.firstStep ⊓ VAt Γ third := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj mover⁻¹).injective]
    change (v Γ previous).map _ ⊓ (v Γ cp.firstStep).map _ = _
    rw [← v_act, ← v_act, hmovePrevious, hmoveFirst]
  have hcardIntersection : Nat.card (VAt Γ previous ⊓ VAt Γ cp.firstStep : Subgroup G) =
      Nat.card (VAt Γ cp.firstStep ⊓ VAt Γ third : Subgroup G) := by
    rw [← hmap]
    exact (Subgroup.card_map_of_injective (MulAut.conj mover⁻¹).injective).symm
  refine ⟨third, ⟨⟨3, by omega⟩, rfl, rfl⟩, ?_⟩
  change Nat.card (VAt Γ previous) = 2 * Nat.card (VAt Γ previous ⊓ VAt Γ cp.firstStep : Subgroup G) at hbackward
  change Nat.card (VAt Γ cp.firstStep) = 2 * Nat.card (VAt Γ cp.firstStep ⊓ VAt Γ third : Subgroup G)
  rwa [hcardPrevious, hcardIntersection] at hbackward

end Stellmacher.SectionNine
