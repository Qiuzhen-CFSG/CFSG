module
public import Stellmacher.SectionTen.OpeningData
public import Stellmacher.SectionNine.NineSevenGoldschmidtOrbits
/-!
# Critical-center geometry along small-case four-edge paths

In the actual Section Ten graph, assume the first local quotient is SL₂(2).
For any supplied nonbacktracking four-edge walk starting in the first-step
orbit, its first and second centers lie in the last stabilizer and escape
its two-core. The second and last centers commute. No global geodesic or
pairwise-distinctness hypothesis on the supplied walk is imposed.

Extend the original length-three critical path backwards by one edge.
Splitting the initial four-center into the two neighboring center lines,
together with critical minimality, shows that the new first center escapes
the terminal core. Both centers lie in the terminal stabilizer through the
first module. Cubic four-path transitivity transports this reference and
the original commuting critical centers to the supplied walk, using one
native group conjugation throughout.

Source: Stellmacher (10.1)(a3), printed p.62 after (11), the local center
containments and noncontainments at the middle of the length-eight path.
The ambient Hypothesis Two remains on the original group H.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

private theorem four_path_transport
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two)
    (source target : Fin 5→ctx.Γ.Vertex)
    (hsource : IsConjugateVertex ctx.Γ ctx.criticalPath.firstStep (source 0))
    (htarget : IsConjugateVertex ctx.Γ ctx.criticalPath.firstStep (target 0))
    (hsourceAdj : ∀i:Fin 4,ctx.Γ.adjacent (source i.castSucc) (source i.succ))
    (htargetAdj : ∀i:Fin 4,ctx.Γ.adjacent (target i.castSucc) (target i.succ))
    (hsourceBack : ∀i:Fin 3,source i.castSucc.castSucc≠source i.succ.succ)
    (htargetBack : ∀i:Fin 3,target i.castSucc.castSucc≠target i.succ.succ) :
    ∃mover:G,∀i,ctx.Γ.act mover (source i)=target i := by
  let Γ := ctx.Γ
  obtain ⟨g,hg⟩ := hsource
  let normalized : Fin 5→Γ.Vertex := fun i=>Γ.act g⁻¹ (source i)
  have hnorm : normalized 0=ctx.criticalPath.firstStep := by
    dsimp only [normalized]
    rw [←hg,←Γ.act_mul,mul_inv_cancel,Γ.act_one]
  have hnormAdj (i:Fin 4) : Γ.adjacent (normalized i.castSucc) (normalized i.succ) :=
    adjacent_act Γ g⁻¹ (hsourceAdj i)
  have hnormBack (i:Fin 3) : normalized i.castSucc.castSucc≠normalized i.succ.succ :=
    fun heq=>hsourceBack i (goldschmidt_act_injective Γ g⁻¹ heq)
  have hshort : 1<ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  have hmodels (vertex:Γ.Vertex) (hvertex:IsConjugateVertex Γ ctx.criticalPath.a vertex) :
      QuotientIsModel (GAt Γ vertex) (QAt Γ vertex) SL2Two :=
    (lemma_nine_three_ambient ctx.toAmbientSectionNineContext hshort vertex hvertex).1
  obtain ⟨m,hm⟩ := goldschmidt_four_path_orbit_transport ctx.toLocalContext.toSectionNineLocalContext
    hmodel hmodels normalized target hnorm htarget hnormAdj htargetAdj hnormBack htargetBack
  exact ⟨g⁻¹*m,fun i=>by rw [Γ.act_mul]; exact hm i⟩

public theorem ten_one_small_four_path_center_geometry
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two)
    (path : Fin 5→ctx.Γ.Vertex)
    (horbit : IsConjugateVertex ctx.Γ ctx.criticalPath.firstStep (path 0))
    (hadj : ∀i:Fin 4,ctx.Γ.adjacent (path i.castSucc) (path i.succ))
    (hback : ∀i:Fin 3,path i.castSucc.castSucc≠path i.succ.succ) :
    ZAt ctx.Γ (path 0)≤GAt ctx.Γ (path 4) ∧
      ¬ZAt ctx.Γ (path 0)≤QAt ctx.Γ (path 4) ∧
      ZAt ctx.Γ (path 1)≤GAt ctx.Γ (path 4) ∧
      ¬ZAt ctx.Γ (path 1)≤QAt ctx.Γ (path 4) ∧
      ⁅ZAt ctx.Γ (path 1),ZAt ctx.Γ (path 4)⁆=⊥ := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hlength : cp.length=3 := ctx.critical_length
  have hshort : 1<cp.length := by omega
  let middle := cp.path ⟨2,by omega⟩
  have hmiddle : IsCriticalPathOffset Γ cp 2 middle := ⟨⟨2,by omega⟩,rfl,rfl⟩
  obtain ⟨_,hfirstAdj,hterminalAdj,hfirstNe⟩ := sectionTenOpeningGeometry ctx middle hmiddle
  have hstartModel := (lemma_nine_three_ambient ctx.toAmbientSectionNineContext hshort
    cp.a ⟨1,Γ.act_one _⟩).1
  obtain ⟨previous,hprevious,hpreviousNe⟩ := goldschmidt_neighbor_other Γ cp.a cp.firstStep
    (cubic_local_action_of_sl2Two_quotient Γ ctx.sectionSeven cp.a hstartModel).degree
  obtain ⟨g,hg⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity cp.a
    ((mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj)
    ((mem_neighborhood_iff_adjacent Γ).mpr hprevious)
  have hsplit := nine_three_center_split ctx.toAmbientSectionNineContext hshort
    (middle:=cp.a) ⟨1,Γ.act_one _⟩ hprevious cp.firstStep_adj hpreviousNe
  have hpreviousCenter : ZAt Γ previous≤ZAt Γ cp.a := hsplit.1 ▸ le_sup_left
  have hinitial := (lemma_seven_four ctx.sectionSeven Γ cp).first_containment
  have hpreviousStab : ZAt Γ previous≤GAt Γ cp.a' :=
    hpreviousCenter.trans (hinitial.1.trans hinitial.2)
  have hfirstCore : ZAt Γ cp.firstStep≤QAt Γ cp.a' := by
    apply critical_minimality Γ cp
    have hh := path_distance_le Γ cp 1 cp.length (by omega) le_rfl
    rw [cp.path_first,cp.path_end] at hh
    change Γ.distance cp.firstStep cp.a'<cp.length
    omega
  have hpreviousNot : ¬ZAt Γ previous≤QAt Γ cp.a' := by
    intro hle
    apply cp.critical.2
    change ZAt Γ cp.a≤QAt Γ cp.a'
    rw [hsplit.1]
    exact sup_le hle hfirstCore
  let reference : Fin 5→Γ.Vertex := ![previous,cp.a,cp.firstStep,middle,cp.a']
  have hrefAdj : ∀i:Fin 4,Γ.adjacent (reference i.castSucc) (reference i.succ) := by
    intro i
    fin_cases i
    · exact Γ.adjacent_symm hprevious
    · exact cp.firstStep_adj
    · exact Γ.adjacent_symm hfirstAdj
    · exact hterminalAdj
  have hrefBack : ∀i:Fin 3,reference i.castSucc.castSucc≠reference i.succ.succ := by
    intro i
    fin_cases i
    · exact hpreviousNe
    · change cp.a≠middle
      intro heq
      have hh : Γ.adjacent cp.a cp.a' := heq ▸ hterminalAdj
      have hd := (adjacent_iff_distance_eq_one Γ).mp hh
      rw [cp.endpoint_distance] at hd
      omega
    · exact hfirstNe
  obtain ⟨mover,hmove⟩ := four_path_transport ctx hmodel reference path
    ⟨g,hg⟩ horbit hrefAdj hadj hrefBack hback
  let e := MulAut.conj mover⁻¹
  have hprevMap : (ZAt Γ previous).map e.toMonoidHom=ZAt Γ (path 0) := by
    rw [←z_act]
    exact congrArg (ZAt Γ) (hmove 0)
  have hstartMap : (ZAt Γ cp.a).map e.toMonoidHom=ZAt Γ (path 1) := by
    rw [←z_act]
    exact congrArg (ZAt Γ) (hmove 1)
  have htermMap : (ZAt Γ cp.a').map e.toMonoidHom=ZAt Γ (path 4) := by
    rw [←z_act]
    exact congrArg (ZAt Γ) (hmove 4)
  have hstabMap : (GAt Γ cp.a').map e.toMonoidHom=GAt Γ (path 4) := by
    change conjugateBy (stabilizer Γ cp.a') mover⁻¹=stabilizer Γ (path 4)
    rw [←stabilizer_act]
    exact congrArg (GAt Γ) (hmove 4)
  have hcoreMap : (QAt Γ cp.a').map e.toMonoidHom=QAt Γ (path 4) := by
    rw [←q_act]
    exact congrArg (QAt Γ) (hmove 4)
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact hprevMap ▸ hstabMap ▸ Subgroup.map_mono hpreviousStab
  · intro hle
    apply hpreviousNot
    apply (Subgroup.map_le_map_iff_of_injective (f:=e.toMonoidHom) e.injective).mp
    rwa [hprevMap,hcoreMap]
  · exact hstartMap ▸ hstabMap ▸ Subgroup.map_mono (hinitial.1.trans hinitial.2)
  · intro hle
    apply cp.critical.2
    change ZAt Γ cp.a≤QAt Γ cp.a'
    apply (Subgroup.map_le_map_iff_of_injective (f:=e.toMonoidHom) e.injective).mp
    rwa [hstartMap,hcoreMap]
  · have hh := congrArg (Subgroup.map e.toMonoidHom) ctx.commutator_eq
    rwa [Subgroup.map_commutator,hstartMap,htermMap,Subgroup.map_bot] at hh

end Stellmacher.SectionTen
