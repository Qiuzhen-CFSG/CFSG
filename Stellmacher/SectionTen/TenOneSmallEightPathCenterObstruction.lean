module
public import Stellmacher.SectionTen.TenOneSmallFourPathCenters
public import Stellmacher.SectionNine.NineSevenGoldschmidtPaths

/-!
# The far-center obstruction on the small eight-edge path

In the actual small Section Ten context, every neighbor center at the
second vertex of a supplied nonbacktracking eight-edge walk fails to
commute with its far endpoint center. The far center is also not contained
in the second vertex center. The walk begins at the original first step;
no global distance-eight or distinctness premise is needed.

Four-edge critical-center transport places the second and far centers
in the stabilizer at the fifth vertex, outside its two-core. They fix
the two different neighboring stems. Noncore actors in this cubic local
action cannot commute while fixing different stems. This settles every
second-vertex neighbor except the forward neighbor. For that remaining
center, the far center fixes the forward order-four plane inside the
order-eight module. Its full module fixed subgroup is proper by the
module-centralizer core bound, hence is precisely that plane. Fixing the
remaining center would therefore identify the two distinct neighbor
planes, contradicting the actual order-eight local geometry.

Source: Stellmacher (10.1)(a3), Journal of Algebra190 (1997), printed p.62
after (11), the center noncommutation and final noncontainment used in
the length-eight path contradiction. All vertices and subgroups remain
in the native graph; the original ambient context is used unchanged.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

private theorem center_le_core_two_edges
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    {left middle right : ctx.Γ.Vertex}
    (hleft : ctx.Γ.adjacent left middle) (hright : ctx.Γ.adjacent middle right) :
    ZAt ctx.Γ left ≤ QAt ctx.Γ right := by
  apply critical_minimality ctx.Γ ctx.criticalPath
  have hd := ctx.Γ.distance_le_of_path 2 ![left,middle,right] (by
    intro i
    fin_cases i
    · exact hleft
    · exact hright)
  change ctx.Γ.distance left right≤2 at hd
  rw [ctx.critical_length]
  omega

private theorem two_noncore_actors_not_commute
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    {vertex left right : ctx.Γ.Vertex}
    (hmodel : QuotientIsModel (GAt ctx.Γ vertex) (QAt ctx.Γ vertex) SL2Two)
    (hleft : ctx.Γ.adjacent vertex left) (hright : ctx.Γ.adjacent vertex right)
    (hne : left≠right) (a b:G)
    (haP : a∈GAt ctx.Γ vertex) (hbP : b∈GAt ctx.Γ vertex)
    (haQ : a∉QAt ctx.Γ vertex) (hbQ : b∉QAt ctx.Γ vertex)
    (haFix : ctx.Γ.act a left=left) (hbFix : ctx.Γ.act b right=right) :
    ¬Commute a b := by
  let Γ := ctx.Γ
  intro hab
  have hmove := goldschmidt_cubic_actor_moves_other
    ctx.toLocalContext.toSectionNineLocalContext vertex left right hmodel hleft hright hne
    ⟨a,haP⟩ haQ haFix
  have hvertex : Γ.act a vertex=vertex :=
    (Set.ext_iff.mp (Γ.stabilizer_def vertex) a).mp haP
  have hother : Γ.adjacent vertex (Γ.act a right) := by
    simpa only [hvertex] using adjacent_act Γ a hright
  have hfix : Γ.act b (Γ.act a right)=Γ.act a right := by
    rw [←Γ.act_mul,hab.eq,Γ.act_mul,hbFix]
  exact goldschmidt_cubic_actor_moves_other
    ctx.toLocalContext.toSectionNineLocalContext vertex right (Γ.act a right)
    hmodel hright hother hmove.symm ⟨b,hbP⟩ hbQ hbFix hfix

public theorem ten_one_small_eight_path_center_obstruction
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep)=8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two)
    (path : Fin 9→ctx.Γ.Vertex)
    (hstart : path 0=ctx.criticalPath.firstStep)
    (hadj : ∀i:Fin 8,ctx.Γ.adjacent (path i.castSucc) (path i.succ))
    (hback : ∀i:Fin 7,path i.castSucc.castSucc≠path i.succ.succ) :
    (∀neighbor,ctx.Γ.adjacent (path 1) neighbor →
      ⁅ZAt ctx.Γ neighbor,ZAt ctx.Γ (path 8)⁆≠⊥) ∧
      ¬ZAt ctx.Γ (path 8)≤ZAt ctx.Γ (path 1) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let localCtx := ctx.toLocalContext.toSectionNineLocalContext
  let ambient := ctx.toAmbientSectionNineContext
  have hshort : 1<cp.length := by change 1<ctx.criticalPath.length; rw [ctx.critical_length]; decide
  have horbit0 : IsConjugateVertex Γ cp.firstStep (path 0) := by
    rw [hstart]
    exact ⟨1,Γ.act_one _⟩
  have horbit2 := goldschmidt_orbit_step localCtx horbit0 (Γ.adjacent_symm (hadj 0)) (hadj 1)
  have horbit4 := goldschmidt_orbit_step localCtx horbit2 (Γ.adjacent_symm (hadj 2)) (hadj 3)
  have horbit6 := goldschmidt_orbit_step localCtx horbit4 (Γ.adjacent_symm (hadj 4)) (hadj 5)
  have horbit8 := goldschmidt_orbit_step localCtx horbit6 (Γ.adjacent_symm (hadj 6)) (hadj 7)
  have horbit1 : IsConjugateVertex Γ cp.a (path 1) := by
    apply goldschmidt_orbit_step localCtx (source:=cp.a) (middle:=path 0) ⟨1,Γ.act_one _⟩
    · rw [hstart]
      exact Γ.adjacent_symm cp.firstStep_adj
    · exact hadj 0
  have horbit3 := goldschmidt_orbit_step localCtx horbit1 (Γ.adjacent_symm (hadj 1)) (hadj 2)
  have horbit5 := goldschmidt_orbit_step localCtx horbit3 (Γ.adjacent_symm (hadj 3)) (hadj 4)
  have horbit7 := goldschmidt_orbit_step localCtx horbit5 (Γ.adjacent_symm (hadj 5)) (hadj 6)
  have hmodel4 := goldschmidt_orbit_model Γ horbit4 hmodel
  have hVcard : Nat.card (VAt Γ (path 4))=8 := (goldschmidt_orbit_module localCtx hshort hsmall (path 4) horbit4).1
  have hZ3card := (lemma_nine_three_ambient ambient hshort (path 3) horbit3).2
  have hZ5card := (lemma_nine_three_ambient ambient hshort (path 5) horbit5).2
  let headPath : Fin 5→Γ.Vertex := ![path 0,path 1,path 2,path 3,path 4]
  have hprefixAdj : ∀i:Fin 4,Γ.adjacent (headPath i.castSucc) (headPath i.succ) := by
    intro i
    fin_cases i
    · exact hadj 0
    · exact hadj 1
    · exact hadj 2
    · exact hadj 3
  have hprefixBack : ∀i:Fin 3,headPath i.castSucc.castSucc≠headPath i.succ.succ := by
    intro i
    fin_cases i
    · exact hback 0
    · exact hback 1
    · exact hback 2
  have hprefix := ten_one_small_four_path_center_geometry ctx hmodel headPath
    horbit0 hprefixAdj hprefixBack
  have hAP : ZAt Γ (path 1)≤GAt Γ (path 4) := hprefix.2.2.1
  have hAQ : ¬ZAt Γ (path 1)≤QAt Γ (path 4) := hprefix.2.2.2.1
  let suffix : Fin 5→Γ.Vertex := ![path 4,path 5,path 6,path 7,path 8]
  have hsuffixAdj : ∀i:Fin 4,Γ.adjacent (suffix i.castSucc) (suffix i.succ) := by
    intro i
    fin_cases i
    · exact hadj 4
    · exact hadj 5
    · exact hadj 6
    · exact hadj 7
  have hsuffixBack : ∀i:Fin 3,suffix i.castSucc.castSucc≠suffix i.succ.succ := by
    intro i
    fin_cases i
    · exact hback 4
    · exact hback 5
    · exact hback 6
  have hsuffix := ten_one_small_four_path_center_geometry ctx hmodel suffix
    horbit4 hsuffixAdj hsuffixBack
  have hZ5B : ⁅ZAt Γ (path 5),ZAt Γ (path 8)⁆=⊥ := hsuffix.2.2.2.2
  let reversed : Fin 5→Γ.Vertex := ![path 8,path 7,path 6,path 5,path 4]
  have hrevAdj : ∀i:Fin 4,Γ.adjacent (reversed i.castSucc) (reversed i.succ) := by
    intro i
    fin_cases i
    · exact Γ.adjacent_symm (hadj 7)
    · exact Γ.adjacent_symm (hadj 6)
    · exact Γ.adjacent_symm (hadj 5)
    · exact Γ.adjacent_symm (hadj 4)
  have hrevBack : ∀i:Fin 3,reversed i.castSucc.castSucc≠reversed i.succ.succ := by
    intro i
    fin_cases i
    · exact (hback 6).symm
    · exact (hback 5).symm
    · exact (hback 4).symm
  have hreverse := ten_one_small_four_path_center_geometry ctx hmodel reversed
    horbit8 hrevAdj hrevBack
  have hBP : ZAt Γ (path 8)≤GAt Γ (path 4) := hreverse.1
  have hBQ : ¬ZAt Γ (path 8)≤QAt Γ (path 4) := hreverse.2.1
  have hQlocal (v:Γ.Vertex) : QAt Γ v≤GAt Γ v := by
    change q Γ v≤stabilizer Γ v
    rw [q,Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hA3 : ZAt Γ (path 1)≤GAt Γ (path 3) :=
    (center_le_core_two_edges ctx (hadj 1) (hadj 2)).trans (hQlocal _)
  have hZ2Q := center_le_core_two_edges ctx (hadj 2) (hadj 3)
  have hsplit7 := nine_three_center_split ambient hshort horbit7
    (Γ.adjacent_symm (hadj 6)) (hadj 7) (hback 6)
  have hBZ7 : ZAt Γ (path 8)≤ZAt Γ (path 7) := hsplit7.1 ▸ le_sup_right
  have hB5 : ZAt Γ (path 8)≤GAt Γ (path 5) := hBZ7.trans
    ((center_le_core_two_edges ctx (Γ.adjacent_symm (hadj 6)) (Γ.adjacent_symm (hadj 5))).trans
      (hQlocal _))
  obtain ⟨b,hbB,hbQ⟩ := SetLike.not_le_iff_exists.mp hBQ
  have hbP := hBP hbB
  have hbFix5 : Γ.act b (path 5)=path 5 :=
    (Set.ext_iff.mp (Γ.stabilizer_def (path 5)) b).mp (hB5 hbB)
  have hnotBA : ¬ZAt Γ (path 8)≤ZAt Γ (path 1) := by
    intro hBA
    have hbFix3 : Γ.act b (path 3)=path 3 :=
      (Set.ext_iff.mp (Γ.stabilizer_def (path 3)) b).mp (hA3 (hBA hbB))
    exact goldschmidt_cubic_actor_moves_other localCtx (path 4) (path 3) (path 5)
      hmodel4 (Γ.adjacent_symm (hadj 3)) (hadj 4) (hback 3) ⟨b,hbP⟩ hbQ hbFix3 hbFix5
  refine ⟨?_,hnotBA⟩
  intro neighbor hneighbor hcomm
  by_cases heq : neighbor=path 2
  · subst neighbor
    let C : Subgroup G := VAt Γ (path 4) ⊓ Subgroup.centralizer (ZAt Γ (path 8):Set G)
    have hZ5C : ZAt Γ (path 5)≤C := le_inf
      (nine_seven_neighbor_center_le_module Γ (hadj 4))
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hZ5B)
    have hCproper : C≠VAt Γ (path 4) := by
      intro heq
      apply hBQ
      apply le_trans ?_ (nine_three_module_centralizer_core_at_vertex ambient (path 4) horbit4)
      apply Subgroup.le_centralizer_iff.mp
      exact heq ▸ (show C≤Subgroup.centralizer (ZAt Γ (path 8):Set G) from inf_le_right)
    have hCcardlt : Nat.card C<8 := by
      rw [←hVcard]
      apply lt_of_le_of_ne (Subgroup.card_le_of_le (show C≤VAt Γ (path 4) from inf_le_left))
      intro heq
      exact hCproper (Subgroup.eq_of_le_of_card_ge inf_le_left heq.ge)
    obtain ⟨factor,hfactor⟩ := Subgroup.card_dvd_of_le (show C≤VAt Γ (path 4) from inf_le_left)
    have hfactorTwo : 2≤factor := by rw [hVcard] at hfactor; nlinarith
    have hCbound : Nat.card C≤4 := by rw [hVcard] at hfactor; nlinarith
    have hCeq : C=ZAt Γ (path 5) :=
      (Subgroup.eq_of_le_of_card_ge hZ5C (hCbound.trans hZ5card.ge)).symm
    have hsplit3 := nine_three_center_split ambient hshort horbit3
      (Γ.adjacent_symm (hadj 2)) (hadj 3) (hback 2)
    have hZ2V : ZAt Γ (path 2)≤VAt Γ (path 4) :=
      (show ZAt Γ (path 2)≤ZAt Γ (path 3) from hsplit3.1 ▸ le_sup_left).trans
        (nine_seven_neighbor_center_le_module Γ (Γ.adjacent_symm (hadj 3)))
    have hZ2Z5 : ZAt Γ (path 2)≤ZAt Γ (path 5) := hCeq ▸
      le_inf hZ2V (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm)
    have hsplit5 := nine_three_center_split ambient hshort horbit5
      (Γ.adjacent_symm (hadj 4)) (hadj 5) (hback 4)
    have hZ4Z5 : ZAt Γ (path 4)≤ZAt Γ (path 5) := hsplit5.1 ▸ le_sup_left
    have hjoin3 : ZAt Γ (path 3)=ZAt Γ (path 2)⊔ZAt Γ (path 4) := hsplit3.1
    have hZ3Z5 : ZAt Γ (path 3)≤ZAt Γ (path 5) := by
      rw [hjoin3]
      exact sup_le hZ2Z5 hZ4Z5
    exact nine_seven_neighbor_centers_distinct ctx.sectionSeven Γ hmodel4 hVcard hZ3card
      (Γ.adjacent_symm (hadj 3)) (hadj 4) (hback 3)
      (Subgroup.eq_of_le_of_card_ge hZ3Z5 (hZ5card.le.trans hZ3card.ge))
  · have hsplit1 := nine_three_center_split ambient hshort horbit1 hneighbor (hadj 1) heq
    have hZrA : ZAt Γ neighbor≤ZAt Γ (path 1) := hsplit1.1 ▸ le_sup_left
    have hZrQ : ¬ZAt Γ neighbor≤QAt Γ (path 4) := by
      intro hle
      apply hAQ
      rw [hsplit1.1]
      exact sup_le hle hZ2Q
    obtain ⟨a,haR,haQ⟩ := SetLike.not_le_iff_exists.mp hZrQ
    have haP := hAP (hZrA haR)
    have haFix3 : Γ.act a (path 3)=path 3 :=
      (Set.ext_iff.mp (Γ.stabilizer_def (path 3)) a).mp (hA3 (hZrA haR))
    apply two_noncore_actors_not_commute ctx hmodel4
      (Γ.adjacent_symm (hadj 3)) (hadj 4) (hback 3) a b haP hbP haQ hbQ haFix3 hbFix5
    exact (Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm haR) b hbB).symm

end Stellmacher.SectionTen
