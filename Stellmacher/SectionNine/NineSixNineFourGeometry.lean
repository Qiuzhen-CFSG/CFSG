module

public import Stellmacher.SectionNine.NineSixResidualCommutatorConjugator
public import Stellmacher.SectionNine.NineSixSmallModule
public import Stellmacher.SectionNine.NineNextSixteenTransvection
public import Stellmacher.SectionNine.CubicEdgeGeneration
public import Stellmacher.SectionNine.NineTenTerminalCenterThirdCentralization
public import Stellmacher.SectionNine.NineThreeSecondExtractionInputs
public import Stellmacher.SectionNine.NineFourReduction
public import Stellmacher.SectionNine.NineSevenShiftedIntersections

/-!
# Genuine path and actor inputs for (9.4) inside (9.6)

Assume the original index-two conclusion of (9.6) fails and the first core
quotient is SL₂(2). Every specified terminal-module element outside the
first core supplies the geometric inputs for the application of (9.4) with
the third critical-path vertex as remote vertex: distance two, actor
centralization, a residual-commutator conjugator, a backward neighbor, the
actual backward-module intersection, all common-neighbor generation
identities, and index-two quotient displacement.

The failed-index reduction gives module order sixteen and the second-center
intersection. A residual-commutator element sends the second vertex to the
initial one; its image of the third vertex is the backward neighbor.
Conjugation transports the actual intersection. The second vertex cannot
be a common neighbor, since its center would equal the initial center and
lie in the terminal core, contradicting criticality. Cubic edge generation
therefore applies to every common neighbor. Short-distance center
containments give the actor's centralization of the third module, and the
faithful elementary-eight quotient gives its transvection displacement.

Source: Stellmacher (9.6), printed p.53 / PDF p.43 of
`refs/files/stellmacher-n-group.pdf`. The subgroup to which (9.4) is applied
and its specific commutator containment remain separate proof obligations;
neither the (9.4) conclusion nor the remaining (9.6) cases are assumed here.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_six_nine_four_geometry
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (third : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 3 third)
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two)
    (hnot : ¬ QuotientCardEq (VAt ctx.Γ ctx.criticalPath.firstStep)
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ third) 2)
    (t : G) (ht : t ∈ VAt ctx.Γ ctx.criticalPath.a')
    (houtside : t ∉ QAt ctx.Γ ctx.criticalPath.firstStep) :
    ∃ x : G,
      x ∈ ⁅EAt ctx.Γ ctx.criticalPath.firstStep,Subgroup.zpowers t⁆ ∧
      ctx.Γ.distance third ctx.criticalPath.firstStep = 2 ∧
      (t ∈ GAt ctx.Γ ctx.criticalPath.firstStep ∧
        t ∈ Subgroup.centralizer (VAt ctx.Γ third : Set G)) ∧
      ctx.Γ.act x third ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
      ctx.Γ.act x third ≠ ctx.criticalPath.firstStep ∧
      VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ (ctx.Γ.act x third) =
        ZAt ctx.Γ ctx.criticalPath.a ∧
      (∀ n : ctx.Γ.Vertex,
        n ∈ Neighborhood ctx.Γ ctx.criticalPath.firstStep →
        n ∈ Neighborhood ctx.Γ (ctx.Γ.act x third) →
        (GAt ctx.Γ ctx.criticalPath.firstStep ⊓ GAt ctx.Γ n) ⊔
          Subgroup.zpowers t = GAt ctx.Γ ctx.criticalPath.firstStep) ∧
      QuotientCardEq (⁅VAt ctx.Γ ctx.criticalPath.firstStep,Subgroup.zpowers t⁆ ⊔
        ZAt ctx.Γ ctx.criticalPath.firstStep) (ZAt ctx.Γ ctx.criticalPath.firstStep) 2 := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hlength : 3 ≤ cp.length := by
    obtain ⟨index,hindex,_⟩ := hpath
    change 3 ≤ ctx.criticalPath.length
    omega
  have hb : 1 < cp.length := by omega
  let second := cp.path ⟨2,by omega⟩
  have hsecond : IsCriticalPathOffset Γ cp 2 second := ⟨⟨2,by omega⟩,rfl,rfl⟩
  have hfirstSecond : Γ.adjacent cp.firstStep second := by
    have hh := cp.path_adj ⟨1,by omega⟩
    change Γ.adjacent (cp.path ⟨1,by omega⟩) second at hh
    rwa [cp.path_first] at hh
  have hsecondThird : Γ.adjacent second third := by
    obtain ⟨index,hindex,rfl⟩ := hpath
    have hh := cp.path_adj ⟨2,by omega⟩
    have heq : (⟨2,by omega⟩ : Fin cp.length).succ = index := Fin.ext (by simp;omega)
    rwa [heq] at hh
  have htail : Γ.distance third cp.a' ≤ cp.length-3 := by
    obtain ⟨index,hindex,rfl⟩ := hpath
    have hh := path_distance_le Γ cp 3 cp.length hlength le_rfl
    have heq : (⟨3,by omega⟩ : Fin (cp.length+1))=index := Fin.ext hindex.symm
    rwa [heq,cp.path_end] at hh
  have hupper : Γ.distance cp.firstStep third ≤ 2 := by
    obtain ⟨index,hindex,rfl⟩ := hpath
    have hh := path_distance_le Γ cp 1 3 (by omega) hlength
    have heq : (⟨3,by omega⟩ : Fin (cp.length+1))=index := Fin.ext hindex.symm
    rwa [heq,cp.path_first] at hh
  have hdistance : Γ.distance third cp.firstStep=2 := by
    rw [Γ.distance_symm]
    have hprefix := nine_eight_adjacent_distance_le Γ (target := cp.a') cp.firstStep_adj
    rw [cp.endpoint_distance] at hprefix
    by_cases hzero : Γ.distance cp.firstStep third=0
    · have heq := (Γ.distance_zero_iff _ _).mp hzero
      rw [heq] at hprefix
      omega
    by_cases hone : Γ.distance cp.firstStep third=1
    · have hh := nine_eight_adjacent_distance_le Γ (target := cp.a')
        ((adjacent_iff_distance_eq_one Γ).mpr hone)
      omega
    omega
  have hfour := (lemma_nine_three_ambient ctx hb cp.a ⟨1,Γ.act_one _⟩).2
  have hbound := nine_six_first_module_card_le ctx.toLocalContext hb hfour hquot
  have hcard := nine_six_order_sixteen_of_not_index_two ctx.toLocalContext
    second third hsecond hpath hfour hbound hnot
  have hinter : VAt Γ cp.firstStep ⊓ VAt Γ third = ZAt Γ second :=
    nine_six_intersection_eq_center_of_not_index_two ctx.toLocalContext
      second third hsecond hpath hfour hbound hnot
  have htP : t ∈ GAt Γ cp.firstStep :=
    (lemma_seven_four ctx.sectionSeven Γ cp).reverse_containment.2 ht
  have hterminal := nine_three_second_extraction_inputs ctx.toLocalContext hb
  let _ : IsElementaryAbelian 2 (VAt Γ cp.a') := hterminal.2.2.1
  have hsquare : t^2=1 := elemPow_eq_one_of_isElementaryAbelian t ht
  have htCore : t ∈ QAt Γ second := hterminal.2.1 ht
  have htSecond : t ∈ GAt Γ second := by
    have hle : QAt Γ second ≤ GAt Γ second := by
      change Γ.twoCoreAt second ≤ Γ.vertexStabilizer second
      rw [Γ.twoCoreAt_def]
      exact twoCoreIn_le _
    exact hle htCore
  have hcentral : t ∈ Subgroup.centralizer (VAt Γ third : Set G) := by
    apply (show VAt Γ cp.a' ≤ Subgroup.centralizer (VAt Γ third : Set G) from ?_) ht
    rw [VAt,v,Γ.vAt_def]
    apply sSup_le
    rintro center ⟨neighbor,hneighbor,rfl⟩
    exact nine_ten_terminal_neighbor_center_centralizes_third ctx.toLocalContext
      third neighbor hpath hneighbor
  obtain ⟨x,hx,hmove⟩ := nine_six_residual_commutator_neighbor_transitive
    ctx.toLocalContext hquot t htP houtside hsquare second cp.a hfirstSecond
    (Γ.adjacent_symm cp.firstStep_adj)
  change Γ.act x second=cp.a at hmove
  have hxP := nine_four_conjugator_mem_stabilizer Γ cp.firstStep t x htP hx
  have hfix : Γ.act x cp.firstStep=cp.firstStep :=
    (Set.ext_iff.mp (Γ.stabilizer_def cp.firstStep) x).mp hxP
  have hback : Γ.act x third ∈ Neighborhood Γ cp.a := by
    apply (mem_neighborhood_iff_adjacent Γ).mpr
    have hh := adjacent_act Γ x hsecondThird
    rwa [hmove] at hh
  have hbackNe : Γ.act x third ≠ cp.firstStep := by
    intro heq
    have hh := distance_act Γ x third cp.firstStep
    rw [hfix,heq,hdistance] at hh
    have hz := (Γ.distance_zero_iff cp.firstStep cp.firstStep).mpr rfl
    omega
  have hbackInter : VAt Γ cp.firstStep ⊓ VAt Γ (Γ.act x third)=ZAt Γ cp.a := by
    have hh := congrArg (fun K : Subgroup G => K.map (MulAut.conj x⁻¹).toMonoidHom) hinter
    rw [Subgroup.map_inf _ _ _ (MulAut.conj x⁻¹).injective,
      ← v_act,← v_act,← z_act,hfix,hmove] at hh
    exact hh
  have hsecondCard : Nat.card (ZAt Γ second)=4 :=
    (nine_six_second_center_card ctx.toLocalContext second hsecond).trans hfour
  have hsecondCore : ZAt Γ second ≤ QAt Γ cp.a' := by
    have hh := path_distance_le Γ cp 2 cp.length (by omega) le_rfl
    rw [cp.path_end] at hh
    exact critical_minimality Γ cp (lt_of_le_of_lt hh (by omega))
  have hgen : ∀ n : Γ.Vertex,
      n ∈ Neighborhood Γ cp.firstStep → n ∈ Neighborhood Γ (Γ.act x third) →
      (GAt Γ cp.firstStep ⊓ GAt Γ n) ⊔ Subgroup.zpowers t=GAt Γ cp.firstStep := by
    intro n hn hnback
    have hne : n ≠ second := by
      intro heq
      subst n
      have hle : ZAt Γ second ≤ ZAt Γ cp.a :=
        (le_inf (nine_seven_neighbor_center_le_module Γ
          ((mem_neighborhood_iff_adjacent Γ).mp hn))
          (nine_seven_neighbor_center_le_module Γ
            ((mem_neighborhood_iff_adjacent Γ).mp hnback))).trans_eq hbackInter
      have hequal := Subgroup.eq_of_le_of_card_ge hle (by rw [hfour,hsecondCard])
      exact cp.critical.2 (hequal.ge.trans hsecondCore)
    exact cubic_edge_sup_zpowers_eq_stabilizer ctx.sectionSeven Γ cp.firstStep n second
      ((mem_neighborhood_iff_adjacent Γ).mp hn) hfirstSecond hne hquot t
      ⟨htP,htSecond⟩ houtside
  exact ⟨x,hx,hdistance,⟨htP,hcentral⟩,hback,hbackNe,hbackInter,hgen,
    nine_next_involution_transvection_of_card_sixteen ctx hb cp.firstStep
      ⟨1,Γ.act_one _⟩ hcard t htP houtside hsquare⟩

end Stellmacher.SectionNine
