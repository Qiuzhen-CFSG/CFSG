module

public import Stellmacher.SectionEight.GeneratedContext
public import Stellmacher.SectionFiveToSeven.Result7_5
public import Stellmacher.SectionFiveToSeven.Result7_6.GraphFacts
public import Stellmacher.SectionFiveToSeven.Result7_6.LocalFacts
public import Stellmacher.SectionFiveToSeven.HypothesisTwoToSectionSeven

/-! # Local BackwardModuleControl for generated Stellmacher (8.5)

The Section Seven hypotheses belong to the graph group. No Hypothesis Two
is imposed on that group. Source: printed pp.40–41, proof of (8.5).
-/

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven CosetGraphContext

private theorem adjacent_join_top
    {G : Type*} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (h7 : SectionSevenHypotheses G S P1 P2)
    (Γ : CosetGraphContext G S P1 P2) (cp : CriticalPath Γ)
    {left right : Γ.Vertex} (hadj : Γ.adjacent left right) :
    stabilizer Γ left ⊔ stabilizer Γ right = ⊤ := by
  have hstart : stabilizer Γ cp.a ⊔ stabilizer Γ cp.firstStep = ⊤ := by
    rcases cp.edge_stabilizers_are_P with hedge | hedge
    · simpa [hedge.1, hedge.2] using h7.generated
    · simpa [hedge.1, hedge.2, sup_comm] using h7.generated
  obtain ⟨actor, halign | halign⟩ :=
    (lemma_seven_one h7 Γ).edge_not_vertex_transitive.1 cp.firstStep_adj hadj
  all_goals
    have hmap := congrArg
      (fun subgroup : Subgroup G => subgroup.map (MulAut.conj actor⁻¹).toMonoidHom)
      hstart
    have hleft := stabilizer_act Γ actor cp.a
    have hright := stabilizer_act Γ actor cp.firstStep
    simp only [conjugateBy] at hleft hright
    rw [Subgroup.map_sup, ← hleft, ← hright, halign.1, halign.2] at hmap
    simpa [sup_comm] using hmap

private theorem length_gt_three
    {G : Type*} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hlength : 2 < ctx.criticalPath.length)
    (hfirst : ⁅ZAt ctx.Γ ctx.criticalPath.a, ZAt ctx.Γ ctx.criticalPath.a'⁆ =
      ZAt ctx.Γ ctx.criticalPath.firstStep)
    (hlast : ⁅ZAt ctx.Γ ctx.criticalPath.a, ZAt ctx.Γ ctx.criticalPath.a'⁆ =
      ZAt ctx.Γ (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1, by omega⟩)) :
    3 < ctx.criticalPath.length := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let h7 := ctx.sectionSeven
  by_contra hnot
  have hthree : cp.length = 3 := by dsimp [cp]; omega
  let last := cp.path ⟨cp.length - 1, by omega⟩
  have hadj : Γ.adjacent cp.firstStep last := by
    have hedge := cp.path_adj ⟨1, by omega⟩
    have heq : (⟨1, by omega⟩ : Fin cp.length).succ =
        ⟨cp.length - 1, by omega⟩ := by apply Fin.ext; simp; omega
    simpa [heq, cp.path_first, last] using hedge
  have heq : z Γ cp.firstStep = z Γ last := hfirst.symm.trans hlast
  have hnormal : (z Γ cp.firstStep).Normal := by
    apply Subgroup.normalizer_eq_top_iff.mp
    apply top_unique
    rw [← adjacent_join_top h7 Γ cp hadj]
    exact sup_le (stabilizer_le_normalizer_z Γ cp.firstStep)
      (by rw [heq]; exact stabilizer_le_normalizer_z Γ last)
  let _ := SevenSix.z_isElementaryAbelian_of_neighbor h7 Γ
    ((SevenSix.mem_neighborhood_iff_adjacent Γ).mpr hadj)
  have hcore : z Γ cp.firstStep ≤ pCore 2 G :=
    le_sSup ⟨hnormal, IsElementaryAbelian.isPGroup 2 _⟩
  apply ctx.commutator_ne
  rw [hfirst]
  exact le_bot_iff.mp (hcore.trans_eq h7.twoCore_eq_bot)

private theorem backward_module_core
    {G : Type*} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (Γ : CosetGraphContext G S P1 P2) (cp : CriticalPath Γ)
    (hlength : 3 < cp.length) (backward : Γ.Vertex)
    (hbackward : backward ∈ neighborhood Γ cp.a) :
    v Γ backward ≤ q Γ cp.firstStep := by
  rw [v, Γ.vAt_def]
  refine sSup_le fun subgroup hsubgroup => ?_
  obtain ⟨vertex, hvertex, rfl⟩ := hsubgroup
  apply SevenSix.critical_minimality Γ cp
  let walk : Fin 4 → Γ.Vertex := ![vertex, backward, cp.a, cp.firstStep]
  have hwalk : ∀ index : Fin 3, Γ.adjacent (walk index.castSucc) (walk index.succ) := by
    intro index
    fin_cases index
    · exact Γ.adjacent_symm ((SevenSix.mem_neighborhood_iff_adjacent Γ).mp hvertex)
    · exact Γ.adjacent_symm ((SevenSix.mem_neighborhood_iff_adjacent Γ).mp hbackward)
    · exact cp.firstStep_adj
  have hbound : Γ.distance vertex cp.firstStep ≤ 3 :=
    Γ.distance_le_of_path 3 walk hwalk
  exact hbound.trans_lt hlength

private theorem commutator_le_index_two
    {G : Type*} [Group G] (moduleGroup line actor : Subgroup G)
    (hindex : (line.subgroupOf moduleGroup).index = 2)
    (hmodule : actor ≤ Subgroup.normalizer (moduleGroup : Set G))
    (hline : actor ≤ Subgroup.normalizer (line : Set G)) :
    ⁅moduleGroup, actor⁆ ≤ line := by
  rw [Subgroup.commutator_comm]
  apply Subgroup.commutator_le.mpr
  intro element helement vector hvector
  have hconj : element * vector * element⁻¹ ∈ moduleGroup :=
    (Subgroup.mem_normalizer_iff.mp (hmodule helement) vector).mp hvector
  have hmem := (line.subgroupOf moduleGroup).mul_mem_iff_of_index_two hindex
    (a := ⟨element * vector * element⁻¹, hconj⟩)
    (b := ⟨vector⁻¹, moduleGroup.inv_mem hvector⟩)
  apply hmem.mpr
  change element * vector * element⁻¹ ∈ line ↔ vector⁻¹ ∈ line
  rw [line.inv_mem_iff]
  exact (Subgroup.mem_normalizer_iff.mp (hline helement) vector).symm

private theorem proper_four_subgroup_index
    {G : Type*} [Group G] [Finite G] (moduleGroup line : Subgroup G)
    (hfour : Nat.card moduleGroup = 4) (hle : line ≤ moduleGroup)
    (hne : line ≠ ⊥) (hproper : line ≠ moduleGroup) :
    (line.subgroupOf moduleGroup).index = 2 := by
  have hpos := Nat.card_pos (α := line)
  have hnotone : Nat.card line ≠ 1 := fun hone => hne (Subgroup.card_eq_one.mp hone)
  have hbound : Nat.card line < 4 := by
    have hlecard := Subgroup.card_le_of_le hle
    rw [hfour] at hlecard
    apply lt_of_le_of_ne hlecard
    intro heq
    exact hproper (Subgroup.eq_of_le_of_card_ge hle (by omega))
  have hdvd : Nat.card line ∣ 4 := hfour ▸ Subgroup.card_dvd_of_le hle
  have htwo : Nat.card line = 2 := by
    have hcases : Nat.card line = 2 ∨ Nat.card line = 3 := by omega
    rcases hcases with hcases | hcases
    · exact hcases
    · norm_num [hcases] at hdvd
  have hcard : Nat.card (line.subgroupOf moduleGroup) = 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
    exact htwo
  have hproduct := (line.subgroupOf moduleGroup).card_mul_index
  rw [hcard, hfour] at hproduct
  omega

private theorem terminal_card_four
    {G : Type*} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hfour : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4) :
    Nat.card (ZAt ctx.Γ ctx.criticalPath.a') = 4 := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let h7 := ctx.sectionSeven
  have hlength := cp.length_pos
  let last := cp.path ⟨cp.length - 1, by omega⟩
  have hlastadj : Γ.adjacent cp.a' last := by
    have hedge := cp.path_adj ⟨cp.length - 1, by omega⟩
    have hi : (⟨cp.length - 1, by omega⟩ : Fin cp.length).succ =
        ⟨cp.length, Nat.lt_succ_self cp.length⟩ := by apply Fin.ext; simp; omega
    rw [hi, cp.path_end] at hedge
    exact Γ.adjacent_symm hedge
  have hfirstcentral : ⁅z Γ cp.firstStep, stabilizer Γ cp.firstStep⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (hcenter.trans (SevenSix.centerAmbient_le_centralizer _))
  obtain ⟨actor, horientation⟩ :=
    (lemma_seven_one h7 Γ).edge_not_vertex_transitive.1 cp.firstStep_adj hlastadj
  have halignment : Γ.act actor cp.a = cp.a' ∧
      Γ.act actor cp.firstStep = last := by
    rcases horientation with halignment | hswapped
    · exact halignment
    · exfalso
      have hendcentral : ⁅z Γ cp.a', stabilizer Γ cp.a'⁆ = ⊥ := by
        rw [← hswapped.2, z_act, stabilizer_act, conjugateBy,
          ← Subgroup.map_commutator, hfirstcentral, Subgroup.map_bot]
      apply ctx.commutator_ne
      rw [Subgroup.commutator_comm]
      apply bot_unique
      have h74 := lemma_seven_four h7 Γ cp
      exact (Subgroup.commutator_mono le_rfl
        (h74.first_containment.1.trans h74.first_containment.2)).trans hendcentral.le
  change Nat.card (z Γ cp.a') = 4
  rw [← halignment.1, z_act, Subgroup.card_map_of_injective
    (MulAut.conj actor⁻¹).injective]
  exact hfour

public theorem eight_five_backward_module_control_local
    {G : Type*} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hfour : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (_hquotient : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : 2 < ctx.criticalPath.length)
    (hfirst : ⁅ZAt ctx.Γ ctx.criticalPath.a, ZAt ctx.Γ ctx.criticalPath.a'⁆ =
      ZAt ctx.Γ ctx.criticalPath.firstStep)
    (hlast : ⁅ZAt ctx.Γ ctx.criticalPath.a, ZAt ctx.Γ ctx.criticalPath.a'⁆ =
      ZAt ctx.Γ (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1, by omega⟩))
    (backward : ctx.Γ.Vertex)
    (hbackward : backward ∈ neighborhood ctx.Γ ctx.criticalPath.a)
    (_hdistinct : backward ≠ ctx.criticalPath.firstStep)
    (_hgenerate : (GAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ backward) ⊔
      ZAt ctx.Γ ctx.criticalPath.a' = GAt ctx.Γ ctx.criticalPath.a) :
    VAt ctx.Γ backward ≤ QAt ctx.Γ ctx.criticalPath.firstStep ∧
      (VAt ctx.Γ backward ≤ GAt ctx.Γ ctx.criticalPath.a' →
        ⁅ZAt ctx.Γ ctx.criticalPath.a', VAt ctx.Γ backward⁆ ≤
          ZAt ctx.Γ ctx.criticalPath.a) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let residual := ⁅z Γ cp.a, z Γ cp.a'⁆
  let h7 := ctx.sectionSeven
  have hcore := backward_module_core Γ cp
    (length_gt_three ctx hlength hfirst hlast) backward hbackward
  refine ⟨hcore, fun hterminal => ?_⟩
  have h74 := lemma_seven_four h7 Γ cp
  have hRinitial : residual ≤ z Γ cp.a :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp
      (h74.reverse_containment.1.trans (stabilizer_le_normalizer_z Γ cp.a))
  have hRterminal : residual ≤ z Γ cp.a' := by
    dsimp [residual]
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((h74.first_containment.1.trans h74.first_containment.2).trans
        (stabilizer_le_normalizer_z Γ cp.a'))
  have hproper : residual ≠ z Γ cp.a' := by
    have hquad : ⁅⁅z Γ cp.a', z Γ cp.a⁆, z Γ cp.a⁆ = ⊥ := h74.quadratic.1
    rw [Subgroup.commutator_comm (z Γ cp.a') (z Γ cp.a)] at hquad
    change ⁅residual, z Γ cp.a⁆ = ⊥ at hquad
    intro heq
    rw [heq, Subgroup.commutator_comm] at hquad
    exact ctx.commutator_ne hquad
  have hindex := proper_four_subgroup_index (z Γ cp.a') residual
    (terminal_card_four ctx hcenter hfour) hRterminal ctx.commutator_ne hproper
  have hVG : v Γ backward ≤ stabilizer Γ cp.firstStep := by
    apply hcore.trans
    rw [q, Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hRcentral : residual ≤ Subgroup.centralizer (v Γ backward : Set G) := by
    rw [show residual = z Γ cp.firstStep from hfirst]
    exact (hcenter.trans (SevenSix.centerAmbient_le_centralizer _)).trans
      (Subgroup.centralizer_le hVG)
  have hVcentral : v Γ backward ≤ Subgroup.centralizer (residual : Set G) := by
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hRcentral
  exact (commutator_le_index_two (z Γ cp.a') residual (v Γ backward) hindex
    (hterminal.trans (stabilizer_le_normalizer_z Γ cp.a'))
    (hVcentral.trans (Subgroup.centralizer_le_normalizer _))).trans hRinitial

end Stellmacher.SectionEight
