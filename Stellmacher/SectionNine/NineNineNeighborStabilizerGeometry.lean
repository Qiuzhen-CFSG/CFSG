module
public import Stellmacher.SectionNine.NineThreeCenterSplitting

/-!
# Two neighbor-stabilizer consequences for (9.9)

At a vertex in the initial critical endpoint's orbit, (9.3) gives the cubic
local quotient. A subgroup contained in one edge stabilizer intersects the
stabilizer of every other neighbor with index at most two, since the vertex
core is contained in both edge stabilizers. If it is not contained in the
second stabilizer, its commutator with that neighbor's center is nontrivial:
otherwise conjugation fixes the center line, and distinct neighboring centers
force the corresponding vertex to be fixed as well.

This is the local-action implication in the second exclusion in Stellmacher
(9.9), printed p.56/PDF p.46 of `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_nine_neighbor_stabilizer_geometry
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    {middle left right : ctx.Γ.Vertex}
    (hmiddle : IsConjugateVertex ctx.Γ ctx.criticalPath.a middle)
    (hleft : ctx.Γ.adjacent middle left)
    (hright : ctx.Γ.adjacent middle right)
    (U : Subgroup G) (hU : U ≤ GAt ctx.Γ middle ⊓ GAt ctx.Γ left)
    (hnot : ¬ U ≤ GAt ctx.Γ right) :
    Nat.card U ≤ 2 * Nat.card (U ⊓ GAt ctx.Γ right : Subgroup G) ∧
      ⁅U, ZAt ctx.Γ right⁆ ≠ ⊥ := by
  let Γ := ctx.Γ
  let edge := GAt Γ middle ⊓ GAt Γ left
  let Q := QAt Γ middle
  obtain ⟨hmodel, hfour⟩ := lemma_nine_three_ambient ctx hb middle hmiddle
  have hedge : Nat.card edge = 2 * Nat.card Q :=
    (cubic_local_action_of_sl2Two_quotient Γ ctx.sectionSeven middle hmodel).edge_card left hleft
  have hQmiddle : Q ≤ GAt Γ middle := by
    change Γ.twoCoreAt middle ≤ _
    rw [Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hQleft : Q ≤ GAt Γ left :=
    ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core middle left
      ((mem_neighborhood_iff_adjacent Γ).mpr hleft) default).2.2
  have hQright : Q ≤ GAt Γ right :=
    ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core middle right
      ((mem_neighborhood_iff_adjacent Γ).mpr hright) default).2.2
  have hQedge : Q ≤ edge := le_inf hQmiddle hQleft
  have hidx : Q.relIndex edge = 2 := by
    have hmul := (Q.subgroupOf edge).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQedge).toEquiv, hedge] at hmul
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hmul
  have hidxU : (U ⊓ Q).relIndex U ≤ 2 := by
    rw [Subgroup.inf_relIndex_left]
    exact (Subgroup.relIndex_le_of_le_right hU (by rw [hidx]; decide)).trans_eq hidx
  have hcard : Nat.card U ≤ 2 * Nat.card (U ⊓ Q : Subgroup G) := by
    have hmul := ((U ⊓ Q).subgroupOf U).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show U ⊓ Q ≤ U from inf_le_left)).toEquiv] at hmul
    change (U ⊓ Q).relIndex U * Nat.card (U ⊓ Q : Subgroup G) = Nat.card U at hmul
    rw [← hmul]
    exact Nat.mul_le_mul_right _ hidxU
  refine ⟨hcard.trans (Nat.mul_le_mul_left 2
    (Subgroup.card_le_of_le (inf_le_inf_left U hQright))), ?_⟩
  intro hcomm
  have hcentral := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  apply hnot
  intro actor hactor
  apply (Set.ext_iff.mp (Γ.stabilizer_def right) actor).mpr
  by_contra hne
  have hfixMiddle := (Set.ext_iff.mp (Γ.stabilizer_def middle) actor).mp (hU hactor).1
  have hactAdj := adjacent_act Γ actor hright
  rw [hfixMiddle] at hactAdj
  have hsplit := nine_three_center_split ctx hb hmiddle hright hactAdj
    (fun h => hne h.symm)
  have hmap : (ZAt Γ right).map (MulAut.conj actor⁻¹).toMonoidHom = ZAt Γ right :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.centralizer_le_normalizer _
        ((Subgroup.centralizer (ZAt Γ right : Set G)).inv_mem (hcentral hactor)))
  have hcenterEq : ZAt Γ (Γ.act actor right) = ZAt Γ right := by
    change z Γ (Γ.act actor right) = _
    rw [z_act]
    exact hmap
  have hbot : ZAt Γ right = ⊥ := by
    have hd := hsplit.2.1
    rw [hcenterEq] at hd
    exact disjoint_self.mp hd
  exact ((nine_seven_center_join ctx middle hmiddle).2 right
    ((mem_neighborhood_iff_adjacent Γ).mpr hright)).1 hbot

end Stellmacher.SectionNine
