module
public import Stellmacher.SectionTen.TenOneLargeFirstFrobenius
public import Stellmacher.SectionNine.NineSevenGoldschmidtOrbits
public import Stellmacher.SectionNine.FrobeniusTwentyLocalAction

/-!
# A large-case predecessor with both center escapes

For the original ambient Section Ten context in the no-transvection branch,
there is a neighbor of the initial vertex, distinct from the first step,
whose center escapes the terminal core and whose core does not contain the
terminal center. No reverse criticality or extra path-selection hypothesis
is assumed.

The initial center splits as the product of any two distinct neighboring
center lines. Critical minimality puts the first-step line in the terminal
core, so the other line must escape it. If the terminal center lay in every
initial-neighbor core, distance-two minimality would put the middle center
in every such core as well. The proved first Frobenius quotient supplies
actual first-edge elements taking the middle vertex to each other first
neighbor. Conjugating the preceding containments by those elements puts the
whole first module in every initial-neighbor core. A single cubic two-arc
transport of the opening module noncontainment contradicts this. All
conjugations use the original graph and ambient embedding.

Source: Stellmacher, Journal of Algebra 190 (1997), printed p.65, the
length-four path selected immediately after (10.1)(20).
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_large_predecessor_selection
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2)
    :
    ∃ previous : ctx.Γ.Vertex, ctx.Γ.adjacent ctx.criticalPath.a previous ∧
      previous≠ctx.criticalPath.firstStep ∧
      ¬ZAt ctx.Γ ctx.criticalPath.a'≤QAt ctx.Γ previous ∧
      ¬ZAt ctx.Γ previous≤QAt ctx.Γ ctx.criticalPath.a' := by
  classical
  have htrans := frobenius_twenty_edge_neighbor_transitivity ctx.sectionSeven ctx.Γ
    ctx.criticalPath.firstStep (ten_one_large_first_frobenius ctx middle hpath hno)
  let Γ:=ctx.Γ
  let cp:=ctx.criticalPath
  have hlength : cp.length=3:=ctx.critical_length
  have hshort : 1<cp.length:=by omega
  obtain ⟨hmiddleOrbit,hfirst,hterminal,hfirstNe⟩:=sectionTenOpeningGeometry ctx middle hpath
  have hopen:=sectionTenOpeningData ctx middle hpath
  have hstartModel:=(lemma_nine_three_ambient ctx.toAmbientSectionNineContext hshort
    cp.a ⟨1,Γ.act_one _⟩).1
  have hpreviousNot (previous:Γ.Vertex) (hprevious:Γ.adjacent cp.a previous)
      (hpreviousNe:previous≠cp.firstStep) : ¬ZAt Γ previous≤QAt Γ cp.a' := by
    have hsplit:=nine_three_center_split ctx.toAmbientSectionNineContext hshort
      (middle:=cp.a) ⟨1,Γ.act_one _⟩ hprevious cp.firstStep_adj hpreviousNe
    have hfirstCore : ZAt Γ cp.firstStep≤QAt Γ cp.a' := by
      apply critical_minimality Γ cp
      have hh:=path_distance_le Γ cp 1 cp.length (by omega) le_rfl
      rw [cp.path_first,cp.path_end] at hh
      change Γ.distance cp.firstStep cp.a'<cp.length
      omega
    intro hle
    apply cp.critical.2
    change ZAt Γ cp.a≤QAt Γ cp.a'
    rw [hsplit.1]
    exact sup_le hle hfirstCore
  by_contra hnone
  have hAll (previous:Γ.Vertex) (hprevious:Γ.adjacent cp.a previous) :
      ZAt Γ cp.a'≤QAt Γ previous := by
    by_cases heq:previous=cp.firstStep
    · rw [heq]
      apply critical_minimality Γ cp
      rw [Γ.distance_symm]
      have hh:=path_distance_le Γ cp 1 cp.length (by omega) le_rfl
      rw [cp.path_first,cp.path_end] at hh
      change Γ.distance cp.firstStep cp.a'<cp.length
      omega
    · by_contra hbad
      exact hnone ⟨previous,hprevious,heq,hbad,hpreviousNot previous hprevious heq⟩
  have hfirstAll (previous:Γ.Vertex) (hprevious:Γ.adjacent cp.a previous) :
      ZAt Γ cp.firstStep≤QAt Γ previous := by
    apply critical_minimality Γ cp
    have htriangle:=Γ.distance_le_of_path 2 ![cp.firstStep,cp.a,previous] (by
      intro i
      fin_cases i
      · exact Γ.adjacent_symm cp.firstStep_adj
      · exact hprevious)
    change Γ.distance cp.firstStep previous≤2 at htriangle
    change Γ.distance cp.firstStep previous<cp.length
    omega
  have hmiddleAll (previous:Γ.Vertex) (hprevious:Γ.adjacent cp.a previous) :
      ZAt Γ middle≤QAt Γ previous := by
    rw [hopen.center_direct_product.1]
    exact sup_le (hfirstAll previous hprevious) (hAll previous hprevious)
  obtain ⟨previous,hprevious,hpreviousNe⟩:=goldschmidt_neighbor_other Γ cp.a cp.firstStep
    (cubic_local_action_of_sl2Two_quotient Γ ctx.sectionSeven cp.a hstartModel).degree
  have hmiddleNe : middle≠cp.a := by
    intro heq
    have hd:=(adjacent_iff_distance_eq_one Γ).mp (heq ▸ hterminal)
    rw [cp.endpoint_distance] at hd
    omega
  have hmodule : VAt Γ cp.firstStep≤QAt Γ previous := by
    change v Γ cp.firstStep≤_
    rw [v,Γ.vAt_def]
    apply sSup_le
    rintro _ ⟨neighbor,hneighbor,rfl⟩
    have hadj:Γ.adjacent cp.firstStep neighbor:=(mem_neighborhood_iff_adjacent Γ).mp hneighbor
    by_cases heq:neighbor=cp.a
    · rw [heq]
      apply critical_minimality Γ cp
      rw [(adjacent_iff_distance_eq_one Γ).mp hprevious]
      exact hshort
    · obtain ⟨actor,hactor,hmove⟩:=htrans cp.a middle neighbor
        (Γ.adjacent_symm cp.firstStep_adj) (Γ.adjacent_symm hfirst) hadj hmiddleNe heq
      have hfix : Γ.act actor⁻¹ cp.a=cp.a :=
        (Set.ext_iff.mp (Γ.stabilizer_def cp.a) _).mp ((GAt Γ cp.a).inv_mem hactor.2)
      have hbackAdj:=adjacent_act Γ actor⁻¹ hprevious
      rw [hfix] at hbackAdj
      have hbound:=Subgroup.map_mono (f:=(MulAut.conj actor⁻¹).toMonoidHom)
        (hmiddleAll (Γ.act actor⁻¹ previous) hbackAdj)
      change (z Γ middle).map _≤(q Γ (Γ.act actor⁻¹ previous)).map _ at hbound
      rw [←z_act,←q_act,hmove,←Γ.act_mul,inv_mul_cancel,Γ.act_one] at hbound
      exact hbound
  have hreverse : IsConjugateVertex Γ middle cp.a := by
    obtain ⟨actor,hactor⟩:=hmiddleOrbit
    refine ⟨actor⁻¹,?_⟩
    rw [←hactor,←Γ.act_mul,mul_inv_cancel,Γ.act_one]
  obtain ⟨actor,hmoveFirst,_,hmoveEnd⟩:=nine_seven_two_arc_transport ctx.sectionSeven Γ
    hfirst hterminal hfirstNe hprevious cp.firstStep_adj hpreviousNe hreverse hstartModel
  apply hopen.terminal_noncontainment
  apply (Subgroup.map_le_map_iff_of_injective (f:=(MulAut.conj actor⁻¹).toMonoidHom)
    (MulAut.conj actor⁻¹).injective).mp
  change (v Γ cp.a').map _≤(q Γ cp.firstStep).map _
  rw [←v_act,←q_act,hmoveEnd,hmoveFirst]
  exact hmodule
end Stellmacher.SectionTen
