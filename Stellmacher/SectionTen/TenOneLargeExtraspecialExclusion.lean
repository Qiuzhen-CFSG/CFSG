module
public import Theory.ElementaryAbelian.ExtraspecialEquiv
public import Theory.GroupAction.Extraspecial27CenterAction
public import Theory.GroupAction.SubgroupQuotientSupportPlaneMover
public import Stellmacher.SectionTen.TenOneLargeResidualGeneration
public import Stellmacher.SectionTen.TenOneLargeTerminalFullSupport
public import Stellmacher.SectionTen.TenOneLargeDisplacementPlaneImage
public import Theory.GroupTheory.ElementaryEightPlaneMover
public import Stellmacher.SectionNine.VertexNormalizedTwoSubgroupSolvable

/-!
# Exclude the extraspecial terminal action in Stellmacher (10.1)

For the actual selected nontransvection actor on the terminal quotient V/Z,
retain the supplied action, its exact core kernel, and the source-(13)
first-center containment. The extraspecial-order27 alternative of (1.3)
is impossible. Its center-actor commutation is retained as a genuine field
of that alternative, together with its extraspecial predicate and order.

Source (13) identifies the actual residual image with the odd core and
normalizes the selected displacement enlarged by the middle center. The
terminal full-support theorem lets the extraspecial center-action result
act on the same quotient. That center is faithful on the four-element
actor displacement. A faithful order-three action moves every quotient
line, so an actual terminal-stabilizer element normalizes the lifted
displacement of order eight while moving its middle-center plane.

The actual middle-stabilizer image is the full order-twenty-four plane
stabilizer. The plane mover gives a second, distinct S₄ image; elementary-eight
normalizer recognition makes its normalizer nonsolvable. On the other hand,
this nontrivial two-subgroup is normalized by a vertex stabilizer. Conjugating
to a base vertex places the ambient Baumann subgroup in its normalizer, and
Hypothesis Two makes that same normalizer solvable. This is the contradiction.

Source: Stellmacher (10.1), printed p.63, the extraspecial exclusion between
(13) and (14), `refs/files/stellmacher-n-group.pdf`. All quotient support
lifts, centralizer kernels, and actions remain literal throughout the proof.
-/

private theorem center_map_subtype
    {G : Type*} [Group G] (X : Subgroup G) (F : Subgroup X) :
    ((Subgroup.center F).map F.subtype).map X.subtype =
      (Subgroup.center (F.map X.subtype)).map (F.map X.subtype).subtype := by
  let e := F.equivMapOfInjective X.subtype X.subtype_injective
  have hc : (Subgroup.center F).map e.toMonoidHom = Subgroup.center (F.map X.subtype) := by
    ext b
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact (Subgroup.centerCongr e ⟨a,ha⟩).property
    · intro hb
      exact ⟨e.symm b,(Subgroup.centerCongr e.symm ⟨b,hb⟩).property,e.apply_symm_apply b⟩
  rw [←hc,Subgroup.map_map,Subgroup.map_map]
  rfl

private theorem range_extraspecial_center_action
    {W : Type*} [Group W] [Finite W] [IsElementaryAbelian 2 W]
    (X : Subgroup (MulAut W)) (F : Subgroup X) (t : X)
    (hF : IsExtraspecial 3 F) (hFcard : Nat.card F=27)
    (ht : IsInvolution (t:MulAut W))
    (hfull : commutatorAction F W=⊤)
    (hgen : ⁅F,Subgroup.zpowers t⁆=F)
    (hcenter : ⁅(Subgroup.center F).map F.subtype,Subgroup.zpowers t⁆=⊥)
    (hdisp : Nat.card (commutatorAction (Subgroup.zpowers (t:MulAut W)) W)=4) :
    let F' := F.map X.subtype
    let C := (Subgroup.center F').map F'.subtype
    C ≤ X ∧ Nat.card C=3 ∧
      (∀ c : C, (commutatorAction (Subgroup.zpowers (t:MulAut W)) W).map
        (c:MulAut W).toMonoidHom=commutatorAction (Subgroup.zpowers (t:MulAut W)) W) ∧
      (∀ c : C, (∀ v ∈ commutatorAction (Subgroup.zpowers (t:MulAut W)) W,
        (c:MulAut W) v=v) → c=1) := by
  let F' := F.map X.subtype
  let C := (Subgroup.center F').map F'.subtype
  let _ : IsExtraspecial 3 F' := hF.of_mulEquiv (F.equivMapOfInjective X.subtype X.subtype_injective)
  have hFcard' : Nat.card F'=27 := by
    rw [Subgroup.card_map_of_injective X.subtype_injective]
    exact hFcard
  have hfull' : commutatorAction F' W=⊤ := by
    rw [commutatorAction_map_actor_subtype]
    exact hfull
  have hgen' : ⁅F',Subgroup.zpowers (t:MulAut W)⁆=F' := by
    have hh := congrArg (Subgroup.map X.subtype) hgen
    simpa only [F',Subgroup.map_commutator,MonoidHom.map_zpowers,Subgroup.coe_subtype] using hh
  have hcenter' : ⁅C,Subgroup.zpowers (t:MulAut W)⁆=⊥ := by
    have hh := congrArg (Subgroup.map X.subtype) hcenter
    rw [Subgroup.map_commutator,center_map_subtype,MonoidHom.map_zpowers,Subgroup.map_bot] at hh
    exact hh
  have htnorm : (t:MulAut W)∈Subgroup.normalizer (F' : Set (MulAut W)) :=
    (Subgroup.le_normalizer_iff_commutator_le_left.mpr hgen'.le) (Subgroup.mem_zpowers _)
  have hCnorm : C≤Subgroup.normalizer (Subgroup.zpowers (t:MulAut W) : Set (MulAut W)) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcenter').trans (Subgroup.centralizer_le_normalizer _)
  have hInv := commutatorAction_isInvariant_of_normalizing_actor (V:=W) C (Subgroup.zpowers (t:MulAut W)) hCnorm
  have hfaith := (extraspecial27_center_action F' inferInstance hFcard' t ht htnorm hfull' hgen' hcenter' hdisp).2
  refine ⟨(Subgroup.map_subtype_le _).trans (Subgroup.map_subtype_le F),?_,?_,hfaith⟩
  · rw [Subgroup.card_map_of_injective F'.subtype_injective]
    exact IsExtraspecial.center_order_p 3 F'
  · intro c
    apply le_antisymm
    · rintro v ⟨w,hw,rfl⟩
      exact (hInv.invariant c w).mp hw
    · intro v hv
      refine ⟨(c:MulAut W).symm v,?_,(c:MulAut W).apply_symm_apply v⟩
      exact (hInv.invariant c⁻¹ v).mp hv

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

private theorem ten_one_large_extraspecial_mover
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (actor : GAt ctx.Γ ctx.criticalPath.a')
    (hactor : (actor : G) ∈ VAt ctx.Γ ctx.criticalPath.firstStep)
    [hN : ((ZAt ctx.Γ ctx.criticalPath.a').subgroupOf
      (VAt ctx.Γ ctx.criticalPath.a')).Normal]
    [_hW : IsElementaryAbelian 2 (VAt ctx.Γ ctx.criticalPath.a' ⧸
      (ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a'))]
    (action : GAt ctx.Γ ctx.criticalPath.a' →* MulAut
      (VAt ctx.Γ ctx.criticalPath.a' ⧸
        (ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a')))
    (hformula : ∀ mover : GAt ctx.Γ ctx.criticalPath.a',
      ∀ point : VAt ctx.Γ ctx.criticalPath.a',
      action mover (QuotientGroup.mk'
        ((ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a')) point) =
      QuotientGroup.mk'
        ((ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a'))
        ⟨(mover : G) * (point : G) * (mover : G)⁻¹,
          (Subgroup.mem_normalizer_iff.mp
            (stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.a' mover.property)
              point).mp point.property⟩)
    (hkernel : action.ker = pCore 2 (GAt ctx.Γ ctx.criticalPath.a'))

    (hout : (actor : G) ∉ QAt ctx.Γ ctx.criticalPath.a')
    (hcard : QuotientCardEq
      (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers (actor : G)⁆ ⊔
        ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 4)
    (hselected : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      ⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers (actor : G)⁆)
    (hno : ∀ element : G, element ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      element ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers element⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2)
    (hF : IsExtraspecial 3 (SectionOne.oddCore action.range))
    (hFcard : Nat.card (SectionOne.oddCore action.range)=27)
    (hcenter : ⁅(Subgroup.center (SectionOne.oddCore action.range)).map
      (SectionOne.oddCore action.range).subtype,Subgroup.zpowers (action.rangeRestrict actor)⁆=⊥) :
    ∃ mover : GAt ctx.Γ ctx.criticalPath.a',
      (mover:G) ∈ Subgroup.normalizer
        ((⁅VAt ctx.Γ ctx.criticalPath.a',Subgroup.zpowers (actor:G)⁆ ⊔
          ZAt ctx.Γ middle : Subgroup G) : Set G) ∧
      (mover:G) ∉ Subgroup.normalizer (ZAt ctx.Γ middle : Set G) := by
  let P := GAt ctx.Γ ctx.criticalPath.a'
  let V := VAt ctx.Γ ctx.criticalPath.a'
  let Z := ZAt ctx.Γ ctx.criticalPath.a'
  let M := ZAt ctx.Γ middle
  let C0 := Subgroup.zpowers (actor:G)
  let D := ⁅V,C0⁆
  let L := D ⊔ M
  let W := V ⧸ Z.subgroupOf V
  let B := commutatorAction (Subgroup.zpowers (action actor)) W
  let q := QuotientGroup.mk' (Z.subgroupOf V)
  let line := (M.subgroupOf V).map q
  have hb : 1 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  obtain ⟨_,hfirst,hterminal,_⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hMV : M ≤ V := nine_seven_neighbor_center_le_module ctx.Γ (ctx.Γ.adjacent_symm hterminal)
  have hMsplit : M = ZAt ctx.Γ ctx.criticalPath.firstStep ⊔ Z :=
    (sectionTenOpeningData ctx middle hpath).center_direct_product.1
  have hZM : Z ≤ M := by rw [hMsplit]; exact le_sup_right
  have hZV : Z ≤ V := hZM.trans hMV
  have hPV : P ≤ Subgroup.normalizer (V : Set G) := stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.a'
  have hCP : C0 ≤ P := Subgroup.zpowers_le.mpr actor.property
  have hDV : D ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp (hCP.trans hPV)
  have hLsplit : L = D ⊔ Z := by
    apply le_antisymm
    · refine sup_le le_sup_left ?_
      rw [hMsplit]
      exact sup_le (hselected.trans le_sup_left) le_sup_right
    · exact sup_le le_sup_left (hZM.trans le_sup_right)
  have hCnative : C0.subgroupOf P = Subgroup.zpowers actor := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hCP,MonoidHom.map_zpowers]
    rfl
  have hBimage : B = (D.subgroupOf V).map q := by
    have hh := Subgroup.quotient_conjugation_commutatorAction_eq_image
      P V Z C0 hPV hCP hN action hformula
    rw [hCnative,MonoidHom.map_zpowers] at hh
    exact hh
  have hBL : (B.comap q).map V.subtype = L := by
    rw [hBimage,Subgroup.comap_map_eq,QuotientGroup.ker_mk',Subgroup.map_sup,
      Subgroup.map_subgroupOf_eq_of_le hDV,Subgroup.map_subgroupOf_eq_of_le hZV,hLsplit]
  have hlineLift : (line.comap q).map V.subtype = M := by
    rw [show line=(M.subgroupOf V).map q from rfl,Subgroup.comap_map_eq,
      QuotientGroup.ker_mk',Subgroup.map_sup,Subgroup.map_subgroupOf_eq_of_le hMV,
      Subgroup.map_subgroupOf_eq_of_le hZV,sup_eq_left.mpr hZM]
  have hbasic := Subgroup.lift_support_basic V Z hZV B
  change _ ≤ V ∧ Z ≤ _ ∧ Nat.card _=Nat.card B*Nat.card Z ∧ _=B at hbasic
  rw [hBL] at hbasic
  have hlineB : line ≤ B := by
    change (M.subgroupOf V).map q ≤ B
    rw [← hbasic.2.2.2]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono V le_sup_right)
  obtain ⟨align,_,halign⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq
  have hZcard : Nat.card Z = 2 :=
    (nine_next_center_commutator_and_kernel ctx.toAmbientSectionNineContext hb
      ctx.criticalPath.a' ⟨align,halign⟩).1
  have hLcard : Nat.card L=8 := by
    change Nat.card (D ⊔ Z : Subgroup G)=4*Nat.card Z at hcard
    rw [hZcard] at hcard
    exact hLsplit ▸ hcard
  have hBcard : Nat.card B=4 := by
    have hh := hbasic.2.2.1
    rw [hLcard,hZcard] at hh
    omega
  have hlineCard : Nat.card line=2 := by
    have hh := (Subgroup.lift_support_basic V Z hZV line).2.2.1
    change Nat.card ((line.comap q).map V.subtype)=Nat.card line*Nat.card Z at hh
    rw [hlineLift,hZcard,(sectionTenOpeningData ctx middle hpath).center_card] at hh
    omega
  obtain ⟨hodd,hgen,_⟩ := ten_one_large_residual_generation ctx middle hpath actor hactor
    action hformula hkernel hout hcard hselected hno
  have hgenO : ⁅SectionOne.oddCore action.range,Subgroup.zpowers (action.rangeRestrict actor)⁆ =
      SectionOne.oddCore action.range := by
    rw [hodd] at hgen
    exact hgen.symm
  have hfull := ten_one_large_terminal_oddCore_full_support ctx middle hpath hno
    action hformula hkernel
  let _ : IsElementaryAbelian 2 (VAt ctx.Γ ctx.criticalPath.firstStep) :=
    ((lemma_seven_five ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq).longer_case hb).1
  have hinv : _root_.IsInvolution (action actor) := by
    constructor
    · intro heq
      have hk : actor ∈ pCore 2 P := hkernel ▸ (MonoidHom.mem_ker.mpr heq)
      apply hout
      change (actor:G)∈ctx.Γ.twoCoreAt ctx.criticalPath.a'
      rw [ctx.Γ.twoCoreAt_def]
      exact Subgroup.mem_map_of_mem P.subtype hk
    · rw [←map_pow,show actor^2=1 from
        Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (actor:G) hactor),map_one]
  obtain ⟨hCX,hCcard,hCstable,hCfaith⟩ := range_extraspecial_center_action action.range
    (SectionOne.oddCore action.range) (action.rangeRestrict actor) hF hFcard hinv hfull hgenO hcenter hBcard
  obtain ⟨mover,hmover,hmoved⟩ := Subgroup.exists_normalizer_support_not_line_of_faithful_three
    P V Z hPV action hformula B hBcard _ hCcard hCX hCstable hCfaith line hlineCard hlineB
  rw [hBL] at hmover
  rw [hlineLift] at hmoved
  exact ⟨mover,hmover,hmoved⟩


public theorem ten_one_large_extraspecial_alternative_impossible
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (actor : GAt ctx.Γ ctx.criticalPath.a')
    (hactor : (actor : G) ∈ VAt ctx.Γ ctx.criticalPath.firstStep)
    [hN : ((ZAt ctx.Γ ctx.criticalPath.a').subgroupOf
      (VAt ctx.Γ ctx.criticalPath.a')).Normal]
    [_hW : IsElementaryAbelian 2 (VAt ctx.Γ ctx.criticalPath.a' ⧸
      (ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a'))]
    (action : GAt ctx.Γ ctx.criticalPath.a' →* MulAut
      (VAt ctx.Γ ctx.criticalPath.a' ⧸
        (ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a')))
    (hformula : ∀ mover : GAt ctx.Γ ctx.criticalPath.a',
      ∀ point : VAt ctx.Γ ctx.criticalPath.a',
      action mover (QuotientGroup.mk'
        ((ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a')) point) =
      QuotientGroup.mk'
        ((ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a'))
        ⟨(mover : G) * (point : G) * (mover : G)⁻¹,
          (Subgroup.mem_normalizer_iff.mp
            (stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.a' mover.property)
              point).mp point.property⟩)
    (hkernel : action.ker = pCore 2 (GAt ctx.Γ ctx.criticalPath.a'))

    (hout : (actor : G) ∉ QAt ctx.Γ ctx.criticalPath.a')
    (hcard : QuotientCardEq
      (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers (actor : G)⁆ ⊔
        ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 4)
    (hselected : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      ⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers (actor : G)⁆)
    (hno : ∀ element : G, element ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      element ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers element⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2)
    (hF : IsExtraspecial 3 (SectionOne.oddCore action.range))
    (hFcard : Nat.card (SectionOne.oddCore action.range)=27)
    (hcenter : ⁅(Subgroup.center (SectionOne.oddCore action.range)).map
      (SectionOne.oddCore action.range).subtype,Subgroup.zpowers (action.rangeRestrict actor)⁆=⊥) : False := by
  let L := ⁅VAt ctx.Γ ctx.criticalPath.a',Subgroup.zpowers (actor:G)⁆ ⊔ ZAt ctx.Γ middle
  let plane := (ZAt ctx.Γ middle).subgroupOf L
  have hML : ZAt ctx.Γ middle ≤ L := le_sup_right
  obtain ⟨_,_,hnorm⟩ := ten_one_large_residual_generation ctx middle hpath actor hactor
    action hformula hkernel hout hcard hselected hno
  let f : GAt ctx.Γ middle →* MulAut L :=
    L.normalizerMonoidHom.comp (Subgroup.inclusion hnorm)
  obtain ⟨hL,hLcard,hJcard,hmap⟩ := ten_one_large_displacement_plane_image ctx middle hpath
    actor hactor hselected hcard hnorm
  let _ := hL
  have hplane : Nat.card plane=4 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hML).toEquiv).trans
      (sectionTenOpeningData ctx middle hpath).center_card
  obtain ⟨mover,hmover,hmoved⟩ := ten_one_large_extraspecial_mover ctx middle hpath actor hactor
    action hformula hkernel hout hcard hselected hno hF hFcard hcenter
  let e := L.normalizerMonoidHom ⟨(mover:G),hmover⟩
  have he : e∈L.normalizerMonoidHom.range := ⟨⟨(mover:G),hmover⟩,rfl⟩
  have hJR : f.range ≤ L.normalizerMonoidHom.range := by
    rintro j ⟨g,rfl⟩
    exact ⟨Subgroup.inclusion hnorm g,rfl⟩
  have hstable (j:f.range) (x:L) : (j:MulAut L) x∈plane ↔ x∈plane := by
    have hj : plane.map (j:MulAut L).toMonoidHom=plane := hmap j j.property
    constructor
    · intro hx
      have hm : (j:MulAut L) x∈plane.map (j:MulAut L).toMonoidHom := hj.symm ▸ hx
      simpa only [Subgroup.mem_map_equiv,MulEquiv.symm_apply_apply] using hm
    · intro hx
      have hm := Subgroup.mem_map_of_mem (j:MulAut L).toMonoidHom hx
      exact hj ▸ hm
  have hmovedPlane : plane.map e.toMonoidHom≠plane := by
    intro heq
    apply hmoved
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    have hh := congrArg (Subgroup.map L.subtype) heq
    have hcomp : L.subtype.comp e.toMonoidHom =
        (MulAut.conj (mover:G)).toMonoidHom.comp L.subtype := rfl
    rw [Subgroup.map_map,hcomp,←Subgroup.map_map,
      Subgroup.map_subgroupOf_eq_of_le hML] at hh
    exact hh
  have hbad := elementaryEight_normalizer_not_isSolvable_of_full_plane_mover
    L hLcard plane hplane f.range hJcard hJR hstable e he hmovedPlane
  have hne : L ≠ ⊥ := by
    intro hh
    change Nat.card L=8 at hLcard
    rw [hh,Subgroup.card_bot] at hLcard
    omega
  exact hbad (vertex_normalized_two_subgroup_solvable ctx.toAmbientSectionNineContext
    middle L hne (IsElementaryAbelian.isPGroup 2 L) hnorm)

end Stellmacher.SectionTen

