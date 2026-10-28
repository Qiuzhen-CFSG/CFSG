module

public import Stellmacher.SectionNine.NineThreeInitialExtractionInputs
public import Stellmacher.SectionNine.NineNextCenterCommutator
public import Stellmacher.SectionEight.GeneratedEightSixNextConjugateGeometry

/-!
# The small-module branch of ambient Stellmacher (9.6)

Critical minimality puts the third-step neighbor-center module in the terminal
core. The initial center lies in the first-step module but not in that core,
so the intersection of the first and third modules is proper. The center at
the second step lies in both modules. If that center has order four and the
first module has order at most eight, finite subgroup indices force index two.
The quotient-model branch also gives the independent bound
`|V_{a+1}| ≤ 16`: the edge Sylow has index three modulo the core, so only
three conjugates of the order-four initial center occur, with a common
order-two line and commutator contained in that line.

These reductions use only the genuine Section Nine local context. The ambient
(9.3) producer must supply the second center's order; the order-sixteen case
of (9.6) remains separate. Source: Stellmacher, printed p.53 / PDF p.43,
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix
open SectionEight

universe u

/-! The next theorem is the cardinality part of (9.6), separated from the
index-two argument so the latter can use the active (9.4) exclusion branch. -/

public theorem nine_six_first_module_card_le
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hfour : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two) :
    Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) ≤ 16 := by
  let graph := ctx.Γ
  let path := ctx.criticalPath
  let actors := GAt graph path.firstStep
  have hlineCard : Nat.card (ZAt graph path.firstStep) = 2 :=
    nine_next_center_order_of_initial_four ctx hfour
  have hlineLe : ZAt graph path.firstStep ≤ ZAt graph path.a := by
    change z graph path.firstStep ≤ z graph path.a
    rw [(lemma_seven_five ctx.sectionSeven graph path ctx.commutator_eq).next_center.1]
    obtain ⟨_, sylow, hsylow⟩ :=
      (edge_sylow_data ctx.sectionSeven graph path).1
    rw [z, graph.zAt_def]
    exact le_sSup ⟨sylow, congrArg omegaOneCenter hsylow.symm⟩
  obtain ⟨hsylowLe, sylow, hsylow⟩ :=
    (edge_sylow_data ctx.sectionSeven graph path).2
  have hcoreLe : QAt graph path.firstStep ≤ actors := by
    change graph.twoCoreAt path.firstStep ≤ graph.vertexStabilizer path.firstStep
    rw [graph.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hnative : (QAt graph path.firstStep).subgroupOf actors ≤ sylow := by
    apply (Subgroup.map_le_map_iff_of_injective actors.subtype_injective).mp
    rw [Subgroup.map_subgroupOf_eq_of_le hcoreLe, hsylow]
    exact (local_cores_le_edge_sylow ctx.sectionSeven graph path).2
  have hindex := eight_six_sylow_index_three_of_quotient actors _ sylow hnative hquot
  obtain ⟨first, second, third, hconjugates⟩ :
      ∃ first second third : actors, ∀ actor : actors,
        conjugateBy (ZAt graph path.a) actor =
            conjugateBy (ZAt graph path.a) first ∨
          conjugateBy (ZAt graph path.a) actor =
            conjugateBy (ZAt graph path.a) second ∨
          conjugateBy (ZAt graph path.a) actor =
            conjugateBy (ZAt graph path.a) third := by
    apply eight_six_three_conjugates_of_index_three _ actors sylow
    · rw [hsylow]
      exact (edge_sylow_data ctx.sectionSeven graph path).1.1.trans
        (stabilizer_le_normalizer_z graph path.a)
    · exact hindex
  have hback : path.a ∈ neighborhood graph path.firstStep :=
    (mem_neighborhood_iff_adjacent graph).mpr
      (graph.adjacent_symm path.firstStep_adj)
  have hclosure := eight_six_neighbor_join_eq_conjugate_closure
    ctx.sectionSeven graph path.firstStep path.a hback
  have hcommon (actor : actors) :
      ZAt graph path.firstStep ≤ conjugateBy (ZAt graph path.a) actor :=
    eight_six_common_line_le_conjugate _ _ _ hlineLe
      (stabilizer_le_normalizer_z graph path.firstStep) actor
  have hcomm : ⁅VAt graph path.firstStep, VAt graph path.firstStep⁆ ≤
      ZAt graph path.firstStep := by
    rw [← nine_next_module_commutator_of_initial_four ctx hfour]
    exact Subgroup.commutator_mono le_rfl
      (neighbor_join_le_core_of_length_gt_one graph path (by omega) path.firstStep)
  rw [hclosure] at hcomm ⊢
  exact eight_six_three_conjugates_card_le _ _ _ first second third hfour hlineCard
    (hcommon first) (hcommon second) (hcommon third) hconjugates hcomm

public theorem nine_six_third_module_le_terminal_core
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (third : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 3 third) :
    VAt ctx.Γ third ≤ QAt ctx.Γ ctx.criticalPath.a' := by
  obtain ⟨index, hindex, rfl⟩ := hpath
  have hlength : 3 ≤ ctx.criticalPath.length := by omega
  rw [VAt, v, ctx.Γ.vAt_def]
  apply sSup_le
  rintro center ⟨neighbor, hneighbor, rfl⟩
  have hadj := ctx.Γ.adjacent_symm
    ((mem_neighborhood_iff_adjacent ctx.Γ).mp hneighbor)
  have hindexEq : index = ⟨3, by omega⟩ := Fin.ext hindex
  rw [hindexEq] at hadj
  have hdist := neighbor_path_distance_le ctx.Γ ctx.criticalPath neighbor
    3 ctx.criticalPath.length hlength le_rfl hadj
  rw [ctx.criticalPath.path_end] at hdist
  exact critical_minimality ctx.Γ ctx.criticalPath
    (lt_of_le_of_lt hdist (by omega))

public theorem nine_six_intersection_lt
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (third : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 3 third) :
    VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ third <
      VAt ctx.Γ ctx.criticalPath.firstStep := by
  refine lt_of_le_of_ne inf_le_left ?_
  intro heq
  have hle : VAt ctx.Γ ctx.criticalPath.firstStep ≤ VAt ctx.Γ third :=
    heq.ge.trans inf_le_right
  exact ctx.criticalPath.critical.2
    ((lemma_seven_four ctx.sectionSeven ctx.Γ ctx.criticalPath).first_containment.1.trans
      (hle.trans (nine_six_third_module_le_terminal_core ctx third hpath)))

public theorem nine_six_second_center_le_intersection
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (second third : ctx.Γ.Vertex)
    (hsecond : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 second)
    (hthird : IsCriticalPathOffset ctx.Γ ctx.criticalPath 3 third) :
    ZAt ctx.Γ second ≤
      VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ third := by
  obtain ⟨secondIndex, hsecondIndex, rfl⟩ := hsecond
  obtain ⟨thirdIndex, hthirdIndex, rfl⟩ := hthird
  have hlength : 3 ≤ ctx.criticalPath.length := by omega
  have hfirst : ctx.Γ.adjacent ctx.criticalPath.firstStep
      (ctx.criticalPath.path secondIndex) := by
    have hadj := ctx.criticalPath.path_adj ⟨1, by omega⟩
    have heq : (⟨1, by omega⟩ : Fin ctx.criticalPath.length).succ = secondIndex := by
      apply Fin.ext
      simp only [Fin.val_succ]
      omega
    rw [heq] at hadj
    change ctx.Γ.adjacent (ctx.criticalPath.path ⟨1, by omega⟩)
      (ctx.criticalPath.path secondIndex) at hadj
    rwa [ctx.criticalPath.path_first] at hadj
  have hlast : ctx.Γ.adjacent (ctx.criticalPath.path thirdIndex)
      (ctx.criticalPath.path secondIndex) := by
    have hadj := ctx.criticalPath.path_adj ⟨2, by omega⟩
    have hleft : (⟨2, by omega⟩ : Fin ctx.criticalPath.length).castSucc = secondIndex :=
      Fin.ext hsecondIndex.symm
    have hright : (⟨2, by omega⟩ : Fin ctx.criticalPath.length).succ = thirdIndex := by
      apply Fin.ext
      simp only [Fin.val_succ]
      omega
    rw [hleft, hright] at hadj
    exact ctx.Γ.adjacent_symm hadj
  apply le_inf
  all_goals
    rw [VAt, v, ctx.Γ.vAt_def]
    apply le_sSup
    refine ⟨ctx.criticalPath.path secondIndex, ?_, rfl⟩
    apply (mem_neighborhood_iff_adjacent ctx.Γ).mpr
  · exact hfirst
  · exact hlast

public theorem nine_six_small_module_index
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (second third : ctx.Γ.Vertex)
    (hsecond : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 second)
    (hthird : IsCriticalPathOffset ctx.Γ ctx.criticalPath 3 third)
    (hcenter : Nat.card (ZAt ctx.Γ second) = 4)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) ≤ 8) :
    QuotientCardEq (VAt ctx.Γ ctx.criticalPath.firstStep)
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ third) 2 := by
  have hlt := nine_six_intersection_lt ctx third hthird
  have hcardlt : Nat.card ↥(VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ third) <
      Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) := by
    apply lt_of_le_of_ne (Subgroup.card_le_of_le hlt.le)
    intro heq
    exact hlt.ne (Subgroup.eq_of_le_of_card_ge hlt.le heq.ge)
  have hcardge := Subgroup.card_le_of_le
    (nine_six_second_center_le_intersection ctx second third hsecond hthird)
  rw [hcenter] at hcardge
  obtain ⟨index, hindex⟩ := Subgroup.card_dvd_of_le hlt.le
  have hindexGe : 2 ≤ index := by nlinarith
  have hindexEq : index = 2 := by nlinarith
  change Nat.card _ = 2 * Nat.card _
  rw [hindex, hindexEq, Nat.mul_comm]

public theorem nine_six_second_center_card
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (second : ctx.Γ.Vertex)
    (hsecond : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 second) :
    Nat.card (ZAt ctx.Γ second) = Nat.card (ZAt ctx.Γ ctx.criticalPath.a) := by
  obtain ⟨index, hindex, rfl⟩ := hsecond
  have hlength : 2 ≤ ctx.criticalPath.length := by omega
  have hadj := ctx.criticalPath.path_adj ⟨1, by omega⟩
  have heq : (⟨1, by omega⟩ : Fin ctx.criticalPath.length).succ = index := by
    apply Fin.ext
    simp only [Fin.val_succ]
    omega
  rw [heq] at hadj
  change ctx.Γ.adjacent (ctx.criticalPath.path ⟨1, by omega⟩)
    (ctx.criticalPath.path index) at hadj
  rw [ctx.criticalPath.path_first] at hadj
  obtain ⟨actor, hactor⟩ := (lemma_seven_one ctx.sectionSeven ctx.Γ).local_transitivity
    ctx.criticalPath.firstStep
    ((mem_neighborhood_iff_adjacent ctx.Γ).mpr
      (ctx.Γ.adjacent_symm ctx.criticalPath.firstStep_adj))
    ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hadj)
  change Nat.card (z ctx.Γ (ctx.criticalPath.path index)) = _
  rw [← hactor, z_act]
  exact (Nat.card_congr ((z ctx.Γ ctx.criticalPath.a).equivMapOfInjective
    (MulAut.conj (actor : G)⁻¹).toMonoidHom (MulAut.conj (actor : G)⁻¹).injective).toEquiv).symm

public theorem nine_six_order_sixteen_of_not_index_two
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (second third : ctx.Γ.Vertex)
    (hsecond : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 second)
    (hthird : IsCriticalPathOffset ctx.Γ ctx.criticalPath 3 third)
    (hcenter : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (hbound : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) ≤ 16)
    (hnot : ¬ QuotientCardEq (VAt ctx.Γ ctx.criticalPath.firstStep)
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ third) 2) :
    Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 16 := by
  have hsecondCard : Nat.card (ZAt ctx.Γ second) = 4 :=
    (nine_six_second_center_card ctx second hsecond).trans hcenter
  have hlarge : 8 < Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) := by
    by_contra hsmall
    exact hnot (nine_six_small_module_index ctx second third hsecond hthird
      hsecondCard (by omega))
  have hb : 1 < ctx.criticalPath.length := by
    obtain ⟨index, hindex, _⟩ := hthird
    omega
  let _ : IsElementaryAbelian 2 (VAt ctx.Γ ctx.criticalPath.firstStep) :=
    ((lemma_seven_five ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq).longer_case
      hb).1
  obtain ⟨exponent, hcard⟩ :=
    (IsElementaryAbelian.isPGroup 2 (VAt ctx.Γ ctx.criticalPath.firstStep)).exists_card_eq
  have hexponent : exponent ≤ 4 := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    simpa only [← hcard] using hbound
  rw [hcard] at hlarge ⊢
  interval_cases exponent <;> norm_num at *

public theorem nine_six_intersection_eq_center_of_not_index_two
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (second third : ctx.Γ.Vertex)
    (hsecond : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 second)
    (hthird : IsCriticalPathOffset ctx.Γ ctx.criticalPath 3 third)
    (hcenter : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (hbound : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) ≤ 16)
    (hnot : ¬ QuotientCardEq (VAt ctx.Γ ctx.criticalPath.firstStep)
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ third) 2) :
    VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ third = ZAt ctx.Γ second := by
  have hcard := nine_six_order_sixteen_of_not_index_two ctx second third
    hsecond hthird hcenter hbound hnot
  have hcenterCard := (nine_six_second_center_card ctx second hsecond).trans hcenter
  have hle := nine_six_second_center_le_intersection ctx second third hsecond hthird
  have hcardle := Subgroup.card_le_of_le hle
  rw [hcenterCard] at hcardle
  have hdvd := Subgroup.card_dvd_of_le
    (inf_le_left : VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ third ≤
      VAt ctx.Γ ctx.criticalPath.firstStep)
  rw [hcard] at hdvd
  have hneEight : Nat.card ↥(VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ third) ≠ 8 := by
    intro heq
    apply hnot
    change Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) =
      2 * Nat.card ↥(VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ third)
    rw [hcard, heq]
  have hlt := nine_six_intersection_lt ctx third hthird
  have hneSixteen : Nat.card ↥(VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ third) ≠ 16 := by
    intro heq
    exact hlt.ne (Subgroup.eq_of_le_of_card_ge hlt.le (by omega))
  have hcardEq : Nat.card ↥(VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ third) = 4 := by
    have hdivisors : ∀ number : ℕ, number ∣ 16 →
        number = 1 ∨ number = 2 ∨ number = 4 ∨ number = 8 ∨ number = 16 := by
      intro number hdiv
      have hnumber := Nat.le_of_dvd (by decide : 0 < 16) hdiv
      interval_cases number <;> norm_num at *
    have := hdivisors _ hdvd
    omega
  exact (Subgroup.eq_of_le_of_card_ge hle (by omega)).symm

public theorem nine_six_ambient_of_small_module
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {G : Type u} [Group G] [Finite G]
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (third : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 3 third)
    (hcenter : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) ≤ 8) :
    QuotientCardEq (VAt ctx.Γ ctx.criticalPath.firstStep)
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ third) 2 := by
  have hlength : 3 ≤ ctx.criticalPath.length := by
    obtain ⟨index, hindex, _⟩ := hpath
    omega
  let second := ctx.criticalPath.path ⟨2, by omega⟩
  have hsecond : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 second :=
    ⟨⟨2, by omega⟩, rfl, rfl⟩
  exact nine_six_small_module_index ctx.toLocalContext second third hsecond hpath
    ((nine_six_second_center_card ctx.toLocalContext second hsecond).trans hcenter) hsmall

end Stellmacher.SectionNine
