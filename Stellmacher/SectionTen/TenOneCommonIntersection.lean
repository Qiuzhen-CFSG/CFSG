module
public import Stellmacher.SectionTen.OpeningData
public import Stellmacher.SectionNine.NineFivePenultimateResidualGeneration
public import Stellmacher.SectionNine.NineSevenResidualTwoArc
public import Stellmacher.SectionNine.NineSevenNormalityObstructions
public import Stellmacher.SectionEight.GeneratedEightSixFirstCommutator
public import Stellmacher.SectionFiveToSeven.NeighborJoinCore

/-!
# The common neighbor-module intersection in Stellmacher (10.1)

At the offset-two vertex of the ambient distance-three critical path, the
intersection of the first and terminal neighbor modules is invariant under
the entire middle stabilizer. Every two distinct neighboring modules have
this same intersection. It centralizes their generated neighborhood group,
and contains that group's derived subgroup.

The (9.5) residual-generation theorem puts the middle residual in the join
of the endpoint cores. The commutator estimate for that join and the middle
center give intersection invariance. The middle core also normalizes both
modules; the cubic edge/core product and the residual Sylow supplement
complete invariance under the stabilizer. The genuine cubic action aligns
any ordered pair of distinct neighbors with the critical-path pair, proving
equality of intersections. Neighbor modules lie in the middle core, so they
normalize one another; their pairwise commutators lie in those intersections.
Taking the generated join gives the derived bound.

The public middle-edge core-product lemma also supports normalization
transfers for subgroups between the middle center and the common intersection.

This is the case-independent geometric part of the common derived equality
in Stellmacher (10.1), printed pp.59–65, using the penultimate-core argument
from (9.5), printed pp.52–53, `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
open scoped IsMulCommutative commutatorElement
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

private theorem core_le_stabilizer
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (vertex : ctx.Γ.Vertex) : QAt ctx.Γ vertex ≤ GAt ctx.Γ vertex := by
  rw [QAt, q, ctx.Γ.twoCoreAt_def]
  exact twoCoreIn_le _

private theorem core_le_neighbor
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    {vertex neighbor : ctx.Γ.Vertex} (hadj : ctx.Γ.adjacent vertex neighbor) :
    QAt ctx.Γ vertex ≤ GAt ctx.Γ neighbor :=
  ((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core vertex neighbor
    ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hadj) default).2.2

private theorem middle_path_eq
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle) :
    ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,
      Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ = middle := by
  obtain ⟨index, hindex, rfl⟩ := hpath
  apply congrArg ctx.criticalPath.path
  apply Fin.ext
  simpa [ctx.critical_length] using hindex.symm

private theorem first_path_offset
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B) :
    IsCriticalPathOffset ctx.Γ ctx.criticalPath (ctx.criticalPath.length - 2)
      ctx.criticalPath.firstStep := by
  refine ⟨⟨1, by rw [ctx.critical_length]; decide⟩, ?_, ?_⟩
  · simp [ctx.critical_length]
  · exact ctx.criticalPath.path_first

public theorem ten_one_middle_edge_core_product
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle) :
    QAt ctx.Γ middle ⊔ QAt ctx.Γ ctx.criticalPath.firstStep =
      GAt ctx.Γ middle ⊓ GAt ctx.Γ ctx.criticalPath.firstStep := by
  obtain ⟨_, hfirst, _, _⟩ := sectionTenOpeningGeometry ctx middle hpath
  let Qa := QAt ctx.Γ middle
  let Qn := QAt ctx.Γ ctx.criticalPath.firstStep
  let edge := GAt ctx.Γ middle ⊓ GAt ctx.Γ ctx.criticalPath.firstStep
  let joined := Qa ⊔ Qn
  have hcard : Nat.card edge = 2 * Nat.card Qa :=
    (cubic_local_action_of_sl2Two_quotient ctx.Γ ctx.sectionSeven middle
      (sectionTenOpeningData ctx middle hpath).quotient_model).edge_card _ hfirst
  have hQa : Qa ≤ edge := le_inf (core_le_stabilizer ctx _) (core_le_neighbor ctx hfirst)
  have hQn : Qn ≤ edge := le_inf (core_le_neighbor ctx (ctx.Γ.adjacent_symm hfirst))
    (core_le_stabilizer ctx _)
  have hjoin : joined ≤ edge := sup_le hQa hQn
  have hnot : ¬ Qn ≤ Qa := by
    have hescape := nine_seven_residual_core_escapes_neighbor
      ctx.toLocalContext.toSectionNineLocalContext ctx.criticalPath.firstStep middle
      ⟨1, ctx.Γ.act_one _⟩ (ctx.Γ.adjacent_symm hfirst)
    intro hle
    apply hescape
    apply le_trans ?_ hle
    change twoCoreIn (ctx.Γ.twoResidualAt ctx.criticalPath.firstStep) ≤
      ctx.Γ.twoCoreAt ctx.criticalPath.firstStep
    rw [ctx.Γ.twoResidualAt_def, ctx.Γ.twoCoreAt_def, residual_core_eq_inter_core]
    exact inf_le_right
  have hindex : Qa.relIndex edge = 2 := by
    have hcount := (Qa.subgroupOf edge).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQa).toEquiv] at hcount
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (hcount.trans hcard)
  have hdiv : Qa.relIndex joined ∣ 2 := by
    rw [← hindex]
    exact dvd_of_mul_right_eq (joined.relIndex edge)
      (Subgroup.relIndex_mul_relIndex Qa joined edge le_sup_left hjoin)
  have hjoinIndex : Qa.relIndex joined = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with hone | htwo
    · exact False.elim (hnot (le_sup_right.trans (Subgroup.relIndex_eq_one.mp hone)))
    · exact htwo
  have hjoinCard : Nat.card joined = 2 * Nat.card Qa := by
    have hcount := (Qa.subgroupOf joined).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show Qa ≤ joined from le_sup_left)).toEquiv] at hcount
    change Qa.relIndex joined * Nat.card Qa = Nat.card joined at hcount
    rw [hjoinIndex] at hcount
    exact hcount.symm
  exact Subgroup.eq_of_le_of_card_ge hjoin (by rw [hcard, hjoinCard])

public theorem ten_one_common_intersection_normalized
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle) :
    GAt ctx.Γ middle ≤ Subgroup.normalizer
      ((VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ ctx.criticalPath.a' : Subgroup G) : Set G) := by
  let I := VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ ctx.criticalPath.a'
  obtain ⟨_, hfirst, hterminal, _⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hb : 1 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  have hfour := (lemma_nine_three_ambient ctx.toAmbientSectionNineContext hb
    ctx.criticalPath.a ⟨1, ctx.Γ.act_one _⟩).2
  have hZ : ZAt ctx.Γ middle ≤ I := le_inf
    (nine_seven_neighbor_center_le_module ctx.Γ (ctx.Γ.adjacent_symm hfirst))
    (nine_seven_neighbor_center_le_module ctx.Γ (ctx.Γ.adjacent_symm hterminal))
  have hjoin : QAt ctx.Γ ctx.criticalPath.firstStep ⊔ QAt ctx.Γ ctx.criticalPath.a' ≤
      Subgroup.normalizer (I : Set G) := by
    have h := (nine_five_penultimate_join_action_of_initial_four
      ctx.toAmbientSectionNineContext hfour hb ctx.criticalPath.firstStep
      (first_path_offset ctx) I le_rfl).2
    rw [middle_path_eq ctx middle hpath, sup_eq_left.mpr hZ] at h
    exact h
  have hE : EAt ctx.Γ middle ≤ Subgroup.normalizer (I : Set G) := by
    have h := nine_five_penultimate_residual_le_join_of_initial_four
      ctx.toAmbientSectionNineContext hfour hb ctx.criticalPath.firstStep
      (first_path_offset ctx)
    rw [middle_path_eq ctx middle hpath] at h
    exact h.trans hjoin
  have hQ : QAt ctx.Γ middle ≤ Subgroup.normalizer (I : Set G) :=
    (le_inf ((core_le_neighbor ctx hfirst).trans (stabilizer_le_normalizer_v ctx.Γ _))
      ((core_le_neighbor ctx hterminal).trans (stabilizer_le_normalizer_v ctx.Γ _))).trans
        Subgroup.inf_normalizer_le_normalizer_inf
  have hedge : GAt ctx.Γ middle ⊓ GAt ctx.Γ ctx.criticalPath.firstStep ≤
      Subgroup.normalizer (I : Set G) := by
    rw [← ten_one_middle_edge_core_product ctx middle hpath]
    exact sup_le hQ (le_sup_left.trans hjoin)
  let sylow : Sylow 2
    (GAt ctx.Γ middle ⊓ GAt ctx.Γ ctx.criticalPath.firstStep : Subgroup G) := default
  have hsylow := ((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core middle
    ctx.criticalPath.firstStep ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst) sylow).1
  have hsup : EAt ctx.Γ middle ⊔ sylowTwoAmbient _ sylow = GAt ctx.Γ middle := by
    change ctx.Γ.twoResidualAt middle ⊔ _ = _
    rw [ctx.Γ.twoResidualAt_def]
    exact twoResidualIn_sup_sylow hsylow
  rw [← hsup]
  exact sup_le hE ((Subgroup.map_subtype_le _).trans hedge)

private theorem neighbor_module_elementary
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    {neighbor : ctx.Γ.Vertex} (hadj : ctx.Γ.adjacent middle neighbor) :
    IsElementaryAbelian 2 (VAt ctx.Γ neighbor) := by
  obtain ⟨_, hfirst, _, _⟩ := sectionTenOpeningGeometry ctx middle hpath
  obtain ⟨actor, hactor⟩ := (lemma_seven_one ctx.sectionSeven ctx.Γ).local_transitivity
    middle ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst)
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hadj)
  have hb : 1 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  let _ : IsElementaryAbelian 2 (VAt ctx.Γ ctx.criticalPath.firstStep) :=
    ((lemma_seven_five ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq).longer_case hb).1
  rw [← hactor, VAt, v_act]
  exact IsElementaryAbelian.map (MulAut.conj (actor : G)⁻¹).toMonoidHom

private theorem common_intersection_le_neighbor
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    {neighbor : ctx.Γ.Vertex} (hadj : ctx.Γ.adjacent middle neighbor) :
    VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ ctx.criticalPath.a' ≤
      VAt ctx.Γ neighbor := by
  obtain ⟨_, hfirst, _, _⟩ := sectionTenOpeningGeometry ctx middle hpath
  obtain ⟨actor, hactor⟩ := (lemma_seven_one ctx.sectionSeven ctx.Γ).local_transitivity
    middle ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst)
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hadj)
  have hnorm := ten_one_common_intersection_normalized ctx middle hpath
  have hmap := Subgroup.mem_normalizer_iff_map_conj_eq.mp
    (hnorm ((GAt ctx.Γ middle).inv_mem actor.property))
  change _ ≤ v ctx.Γ neighbor
  rw [← hactor, v_act]
  rw [← hmap]
  exact Subgroup.map_mono inf_le_left

public theorem ten_one_common_intersection_centralizes
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle) :
    VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ ctx.criticalPath.a' ≤
      Subgroup.centralizer (GeneratedNeighborhoodV ctx.Γ middle : Set G) := by
  apply Subgroup.le_centralizer_iff.mpr
  rw [GeneratedNeighborhoodV]
  apply sSup_le
  rintro subgroup ⟨neighbor, hneighbor, rfl⟩
  have hadj := (mem_neighborhood_iff_adjacent ctx.Γ).mp hneighbor
  let _ := neighbor_module_elementary ctx middle hpath hadj
  intro element helement
  rw [Subgroup.mem_centralizer_iff]
  intro other hother
  exact setLike_mul_comm (common_intersection_le_neighbor ctx middle hpath hadj hother) helement

/-- The middle stabilizer aligns any ordered pair of distinct neighbors with
the critical-path pair. -/
public theorem ten_one_neighbor_pair_alignment
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    {left right : ctx.Γ.Vertex}
    (hleft : ctx.Γ.adjacent middle left) (hright : ctx.Γ.adjacent middle right)
    (hne : left ≠ right) :
    ∃ actor : G, actor ∈ GAt ctx.Γ middle ∧
      ctx.Γ.act actor ctx.criticalPath.firstStep = left ∧
      ctx.Γ.act actor ctx.criticalPath.a' = right := by
  obtain ⟨_, hfirst, hterminal, hends⟩ := sectionTenOpeningGeometry ctx middle hpath
  obtain ⟨first, hfirstMove⟩ := (lemma_seven_one ctx.sectionSeven ctx.Γ).local_transitivity
    middle ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst)
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hleft)
  have hfirstFix : ctx.Γ.act (first : G) middle = middle :=
    (Set.ext_iff.mp (ctx.Γ.stabilizer_def middle) _).mp first.property
  have hterminalAdj := adjacent_act ctx.Γ (first : G) hterminal
  rw [hfirstFix] at hterminalAdj
  have hterminalNe : ctx.Γ.act (first : G) ctx.criticalPath.a' ≠ left := by
    intro heq
    apply hends
    have hcancel := congrArg (ctx.Γ.act (first : G)⁻¹) (hfirstMove.trans heq.symm)
    simpa only [← ctx.Γ.act_mul, mul_inv_cancel, ctx.Γ.act_one] using hcancel
  have hout : ¬ QAt ctx.Γ left ≤ QAt ctx.Γ middle := by
    have hpen : ctx.Γ.adjacent (ctx.criticalPath.path
        ⟨ctx.criticalPath.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) left := by
      rw [middle_path_eq ctx middle hpath]
      exact hleft
    have h := nine_five_penultimate_neighbor_core_not_le
      ctx.toLocalContext.toSectionNineLocalContext left hpen
    change ¬ QAt ctx.Γ left ≤ QAt ctx.Γ (ctx.criticalPath.path
      ⟨ctx.criticalPath.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) at h
    rwa [middle_path_eq ctx middle hpath] at h
  have htrans := (cubic_local_action_of_sl2Two_quotient ctx.Γ ctx.sectionSeven middle
    (sectionTenOpeningData ctx middle hpath).quotient_model).punctured_transitivity
      left hleft (QAt ctx.Γ left)
      (le_inf (core_le_neighbor ctx (ctx.Γ.adjacent_symm hleft))
        (core_le_stabilizer ctx left)) hout
  obtain ⟨second, hsecondMove⟩ := htrans
    ⟨(mem_neighborhood_iff_adjacent ctx.Γ).mpr hterminalAdj, hterminalNe⟩
    ⟨(mem_neighborhood_iff_adjacent ctx.Γ).mpr hright, hne.symm⟩
  have hsecondFix : ctx.Γ.act (second : G) left = left :=
    (Set.ext_iff.mp (ctx.Γ.stabilizer_def left) _).mp
      (core_le_stabilizer ctx left second.property)
  refine ⟨(first : G) * (second : G), (GAt ctx.Γ middle).mul_mem first.property
    (core_le_neighbor ctx (ctx.Γ.adjacent_symm hleft) second.property), ?_, ?_⟩
  · rw [ctx.Γ.act_mul, hfirstMove, hsecondFix]
  · rw [ctx.Γ.act_mul]
    exact hsecondMove

public theorem ten_one_neighbor_intersection
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    {left right : ctx.Γ.Vertex}
    (hleft : ctx.Γ.adjacent middle left) (hright : ctx.Γ.adjacent middle right)
    (hne : left ≠ right) :
    VAt ctx.Γ left ⊓ VAt ctx.Γ right =
      VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ ctx.criticalPath.a' := by
  obtain ⟨actor, hactor, hfirst, hterminal⟩ :=
    ten_one_neighbor_pair_alignment ctx middle hpath hleft hright hne
  have hmap := Subgroup.mem_normalizer_iff_map_conj_eq.mp
    (ten_one_common_intersection_normalized ctx middle hpath
      ((GAt ctx.Γ middle).inv_mem hactor))
  rw [← hfirst, ← hterminal, VAt, VAt, v_act, v_act]
  rw [← Subgroup.map_inf _ _ _ (MulAut.conj actor⁻¹).injective]
  exact hmap

public theorem ten_one_generated_derived_le_intersection
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle) :
    DerivedAmbient (GeneratedNeighborhoodV ctx.Γ middle) ≤
      VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ ctx.criticalPath.a' := by
  let I := VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ ctx.criticalPath.a'
  let family : Set (Subgroup G) := {module | ∃ neighbor,
    neighbor ∈ Neighborhood ctx.Γ middle ∧ module = VAt ctx.Γ neighbor}
  have hb : 2 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  have hcore : GeneratedNeighborhoodV ctx.Γ middle ≤ QAt ctx.Γ middle :=
    nine_seven_neighborhood_le_own_core ctx.toLocalContext.toSectionNineLocalContext
      hb middle
  have hmodule (neighbor : ctx.Γ.Vertex) (hadj : ctx.Γ.adjacent middle neighbor) :
      VAt ctx.Γ neighbor ≤ QAt ctx.Γ middle :=
    (show VAt ctx.Γ neighbor ≤ GeneratedNeighborhoodV ctx.Γ middle from
      le_sSup ⟨neighbor, (mem_neighborhood_iff_adjacent ctx.Γ).mpr hadj, rfl⟩).trans hcore
  have hcomm (left right : ctx.Γ.Vertex)
      (hleft : ctx.Γ.adjacent middle left) (hright : ctx.Γ.adjacent middle right) :
      ⁅VAt ctx.Γ left, VAt ctx.Γ right⁆ ≤ I := by
    by_cases heq : left = right
    · subst right
      let _ := neighbor_module_elementary ctx middle hpath hleft
      apply (show ⁅VAt ctx.Γ left, VAt ctx.Γ left⁆ = ⊥ from ?_).le.trans bot_le
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro first hfirst
      rw [Subgroup.mem_centralizer_iff]
      intro second hsecond
      exact setLike_mul_comm hsecond hfirst
    · dsimp only [I]
      rw [← ten_one_neighbor_intersection ctx middle hpath hleft hright heq]
      apply le_inf
      · rw [Subgroup.commutator_comm]
        exact Subgroup.le_normalizer_iff_commutator_le_right.mp
          ((hmodule right hright).trans ((core_le_neighbor ctx hleft).trans
            (stabilizer_le_normalizer_v ctx.Γ left)))
      · exact Subgroup.le_normalizer_iff_commutator_le_right.mp
          ((hmodule left hleft).trans ((core_le_neighbor ctx hright).trans
            (stabilizer_le_normalizer_v ctx.Γ right)))
  have hcontain : ∀ subgroup ∈ family, subgroup ≤ GAt ctx.Γ middle := by
    rintro subgroup ⟨neighbor, hneighbor, rfl⟩
    exact (hmodule neighbor ((mem_neighborhood_iff_adjacent ctx.Γ).mp hneighbor)).trans
      (core_le_stabilizer ctx middle)
  have hnorm := ten_one_common_intersection_normalized ctx middle hpath
  change (_root_.commutator (GeneratedNeighborhoodV ctx.Γ middle)).map _ ≤ I
  rw [Subgroup.map_subtype_commutator]
  change ⁅sSup family, sSup family⁆ ≤ I
  apply SectionEight.eight_six_commutator_sSup_le family _ I (GAt ctx.Γ middle) hnorm hcontain
  rintro subgroup ⟨neighbor, hneighbor, rfl⟩
  rw [Subgroup.commutator_comm]
  apply SectionEight.eight_six_commutator_sSup_le family _ I (GAt ctx.Γ middle) hnorm hcontain
  rintro subgroup ⟨other, hother, rfl⟩
  exact hcomm other neighbor ((mem_neighborhood_iff_adjacent ctx.Γ).mp hother)
    ((mem_neighborhood_iff_adjacent ctx.Γ).mp hneighbor)

end Stellmacher.SectionTen
