module
public import Stellmacher.SectionNine.NineEightTerminalTransvection
public import Stellmacher.SectionNine.LemmaNineNine
public import Stellmacher.SectionNine.NineNextTransvectionFactor
public import Stellmacher.SectionNine.NineNineTerminalCoreImageSylow
public import Theory.GroupAction.SubgroupQuotientCommutatorImage
public import Stellmacher.SectionNine.NineNineTerminalIntersectionNormality
public import Stellmacher.SectionNine.NineTenInvariantPlaneSupportMove
public import Stellmacher.SectionOne.OneSevenNormalMovingSupportDisplacement
public import Theory.GroupAction.SubgroupQuotientCommutatorBound

/-!
# A normal core subgroup displaces the terminal module outside its intersection

Retain the actual terminal wreath case and its backward module intersection I
of order eight. Let D lie in the penultimate core and be normalized by it.
If D acts nontrivially on I modulo the terminal center, then [V_terminal,D]
is not contained in I. All actions and subgroups use the original context.

The terminal transvection selects a canonical factor in the faithful quotient
V/Z of order sixteen. The penultimate core image is a Sylow group of order
eight and preserves the four-element image of I. Nontrivial D-action supplies
an element exchanging the canonical supports. Normality and the Sylow
transvection force D-displacement of order at least eight, contradicting its
containment in the four-element intersection image.

This is the displacement obstruction needed in Stellmacher (9.10)(12),
printed p.59. It avoids assuming the stronger edge-generation assertion (10).
-/
namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_ten_terminal_normal_subgroup_displacement_not_le_intersection
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 3 < ctx.criticalPath.length)
    (hUcard : Nat.card (VAt ctx.Γ ctx.criticalPath.a') = 2^5)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a')
      (QAt ctx.Γ ctx.criticalPath.a') SL2TwoWreathC2)

    (hIcard : Nat.card (VAt ctx.Γ ctx.criticalPath.a' ⊓ VAt ctx.Γ
      (ctx.criticalPath.path ⟨ctx.criticalPath.length-2,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) : Subgroup G) = 2^3)
    (D : Subgroup G)
    (hDcore : D ≤ QAt ctx.Γ (ctx.criticalPath.path
      ⟨ctx.criticalPath.length-1,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩))
    (hcoreD : QAt ctx.Γ (ctx.criticalPath.path
      ⟨ctx.criticalPath.length-1,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) ≤
        Subgroup.normalizer (D : Set G))
    (hnontrivial : ¬ ⁅VAt ctx.Γ ctx.criticalPath.a' ⊓ VAt ctx.Γ
      (ctx.criticalPath.path ⟨ctx.criticalPath.length-2,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩),D⁆ ≤ ZAt ctx.Γ ctx.criticalPath.a') :
    ¬ ⁅VAt ctx.Γ ctx.criticalPath.a',D⁆ ≤
      VAt ctx.Γ ctx.criticalPath.a' ⊓ VAt ctx.Γ
        (ctx.criticalPath.path ⟨ctx.criticalPath.length-2,
          Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let penultimate := cp.path ⟨cp.length-1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let P := GAt Γ cp.a'
  let U := VAt Γ cp.a'
  let Z := ZAt Γ cp.a'
  let preterminal := cp.path ⟨cp.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let I := U ⊓ VAt Γ preterminal
  let C := ⁅U,D⁆
  have hshort : 1 < cp.length := by change 3 < cp.length at hb; omega
  have hfirstNot : ¬ ZAt Γ cp.firstStep ≤ U := by
    intro hle
    have hh := lemma_nine_nine_ambient ctx hle
    change 3 < cp.length at hb
    change cp.length ≤ 3 at hh
    omega
  obtain ⟨actor, hactorFirst, _, _, hindex⟩ :=
    nine_eight_terminal_transvection_of_reverse_noncontainment ctx hshort hfirstNot
  obtain ⟨alignment, halign, hterminal⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  have horbit : IsConjugateVertex Γ cp.firstStep cp.a' := ⟨alignment, hterminal⟩
  have hdata := nine_next_center_commutator_and_kernel ctx hshort cp.a' horbit
  have hZcard : Nat.card Z = 2 := hdata.1
  have hUcore : ⁅U, QAt Γ cp.a'⁆ = Z := hdata.2.1
  have hQP : QAt Γ cp.a' ≤ P := by
    rw [QAt, CosetGraphContext.q, Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hPU : P ≤ Subgroup.normalizer (U : Set G) := stabilizer_le_normalizer_v Γ cp.a'
  have hZU : Z ≤ U := hUcore ▸
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hQP.trans hPU)
  have hcoreP : QAt Γ penultimate ≤ P :=
    ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core penultimate cp.a'
      ((mem_neighborhood_iff_adjacent Γ).mpr
        (nine_five_penultimate_adjacent ctx.toLocalContext)) default).2.2
  have hDP : D ≤ P := hDcore.trans hcoreP
  have hZpre : Z ≤ VAt Γ preterminal := by
    have hfour := (lemma_nine_three_ambient ctx hshort cp.a ⟨1,Γ.act_one _⟩).2
    have hline := (nine_five_penultimate_center_layer_of_initial_four ctx.toLocalContext hfour).1
    exact hline.trans (nine_seven_neighbor_center_le_module Γ
      (nine_five_previous_adjacent_penultimate ctx.toLocalContext hshort preterminal
        ⟨⟨cp.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩,rfl,rfl⟩))
  have hZI : Z ≤ I := le_inf hZU hZpre
  have hPI := (nine_nine_terminal_intersection_core_normalized ctx hshort).2.2
  obtain ⟨hN, hW, action, hact, hkernel, _, _, hrank, hyp, hfactor⟩ :=
    nine_next_transvection_factor ctx hshort cp.a' horbit actor hindex
  let _ := hN
  let _ := hW
  let W := U ⧸ Z.subgroupOf U
  let q : U →* W := QuotientGroup.mk' (Z.subgroupOf U)
  let f := action.rangeRestrict
  let induced := f actor
  let factor : Subgroup action.range :=
    ⁅SectionOne.oddCore action.range, Subgroup.zpowers induced⁆ ⊔ Subgroup.zpowers induced
  have hfker : f.ker = pCore 2 P := by rw [MonoidHom.ker_rangeRestrict, hkernel]
  obtain ⟨sylow, hsylow⟩ := nine_nine_terminal_core_image_sylow ctx hshort f
    action.rangeRestrict_surjective hfker
  have hScard : Nat.card sylow = 8 := by
    rw [hsylow]
    exact nine_nine_terminal_core_image_card_eight ctx hshort f
      action.rangeRestrict_surjective hfker hmodel
  have hactorQpen : (actor : G) ∈ QAt Γ penultimate :=
    (nine_three_initial_extraction_inputs ctx.toLocalContext hshort).2.1 hactorFirst
  have haS : induced ∈ (sylow : Subgroup action.range) := by
    rw [hsylow]
    exact Subgroup.mem_map_of_mem f hactorQpen
  have haFactor : induced ∈ factor := Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hrank' : Nat.card (commutatorAction (Subgroup.zpowers induced) W) = 2 := by
    rw [← commutatorAction_map_actor_subtype action.range, MonoidHom.map_zpowers]
    exact hrank
  have hWcard : Nat.card W = 16 := by
    have hh := (Z.subgroupOf U).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZU).toEquiv, hZcard, hUcard] at hh
    change Nat.card W * 2 = 2^5 at hh
    omega
  let Nbar := (D.subgroupOf P).map f
  let Sbar : Subgroup action.range := sylow
  let J := (I.subgroupOf U).map q
  have hJcard : Nat.card J=4 := by
    have hcount := (Z.subgroupOf I).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZI).toEquiv,hZcard,hIcard] at hcount
    change Z.relIndex I*2=2^3 at hcount
    have hrel := Subgroup.relIndex_ker (I.subgroupOf U) q
    rw [QuotientGroup.ker_mk',Subgroup.relIndex_subgroupOf (show I≤U from inf_le_left)] at hrel
    change Z.relIndex I=Nat.card J at hrel
    omega
  have hNS : Nbar ≤ Sbar := by
    change Nbar ≤ (sylow : Subgroup action.range)
    rw [hsylow]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono P hDcore)
  have hnormalNative : (QAt Γ penultimate).subgroupOf P ≤
      Subgroup.normalizer (D.subgroupOf P : Set P) := by
    apply Subgroup.le_normalizer_iff.mpr
    intro x hx d hd
    exact Subgroup.le_normalizer_iff.mp hcoreD x hx d hd
  have hnormal : Sbar ≤ Subgroup.normalizer (Nbar : Set action.range) := by
    change (sylow : Subgroup action.range) ≤ _
    rw [hsylow]
    exact (Subgroup.map_mono hnormalNative).trans (Subgroup.le_normalizer_map f)
  have hJinv : ∀ s∈Sbar,J.map (s:MulAut W).toMonoidHom=J := by
    intro s hs
    change s∈(sylow : Subgroup action.range) at hs
    rw [hsylow] at hs
    obtain ⟨lift,hlift,rfl⟩ := hs
    apply Subgroup.eq_of_le_of_card_ge
    · rintro point ⟨vector,⟨original,horiginal,rfl⟩,rfl⟩
      change action lift (q original) ∈ J
      rw [hact]
      exact Subgroup.mem_map_of_mem q
        ((Subgroup.mem_normalizer_iff.mp (hPI
          (show (lift:G)∈GAt Γ penultimate from
            (by
              change (lift:G) ∈ Γ.stabilizer penultimate
              have hle : QAt Γ penultimate≤GAt Γ penultimate := by
                rw [QAt,CosetGraphContext.q,Γ.twoCoreAt_def]
                exact twoCoreIn_le _
              exact hle hlift))) original).mp horiginal)
    · exact (Subgroup.card_map_of_injective (K:=J) (action lift).injective).symm.le
  have hmover : ∃ c∈Nbar, ∃ point∈J,(c:MulAut W) point≠point := by
    by_contra! hfixed
    apply hnontrivial
    rw [Subgroup.commutator_comm]
    have hbound := Subgroup.quotient_conjugation_commutator_le_sup P U Z I D ⊥
      hPU hDP inf_le_left action hact (by
        intro lift hlift point hpoint
        have hmem : f lift∈Nbar := Subgroup.mem_map_of_mem f hlift
        have hfix := hfixed (f lift) hmem (q point) (Subgroup.mem_map_of_mem q hpoint)
        change (q point)⁻¹ * action lift (q point) ∈ _
        change action lift (q point)=q point at hfix
        rw [hfix,inv_mul_cancel]
        exact Subgroup.one_mem _)
    simpa only [bot_sup_eq] using hbound
  obtain ⟨c,hc,point,hpoint,hmovePoint⟩ := hmover
  have hmove := nine_ten_invariant_plane_actor_moves_support action.range hyp factor Sbar
    hfactor sylow.isPGroup' hWcard (by change 4<Nat.card sylow; rw [hScard]; decide)
      induced haFactor haS hrank J hJcard hJinv c (hNS hc) ⟨point,hpoint,hmovePoint⟩
  have hlarge := SectionOne.oneSevenFactor_normal_subgroup_moving_support_commutator_card_ge_eight
    hyp factor Sbar Nbar hfactor hWcard hnormal induced haFactor haS hrank' c hc hmove.1
  have hcommImage : commutatorAction Nbar W = (C.subgroupOf U).map q := by
    rw [←commutatorAction_map_actor_subtype action.range,Subgroup.map_map]
    change commutatorAction ((D.subgroupOf P).map action) W = _
    exact Subgroup.quotient_conjugation_commutatorAction_eq_image P U Z D
      hPU hDP hN action hact
  intro hle
  have hleJ : commutatorAction Nbar W ≤ J := by
    rw [hcommImage]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono U hle)
  change 8 ≤ Nat.card (commutatorAction Nbar W) at hlarge
  have hbound := Subgroup.card_le_of_le hleJ
  rw [hJcard] at hbound
  omega

end Stellmacher.SectionNine
