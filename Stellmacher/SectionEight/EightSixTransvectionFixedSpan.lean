module
public import Stellmacher.SectionEight.EightSixResidualFixedQuotient
public import Stellmacher.SectionEight.GeneratedEightSixEquationOneSetup
public import Stellmacher.SectionFiveToSeven.NeighborCenterNormalizer
public import Stellmacher.SectionFiveToSeven.Result7_8.GeometricExtraction
public import Stellmacher.SectionThree.CentralCoatomTransvectionBound
public import Theory.GroupAction.SubgroupQuotientCommutatorImage

/-!
# A selected transvection forces the fixed-support span

In the actual geometric selection for (8.6), write U=⟨Za^E⟩ and
C=Vnext intersect C_G(O²(E)). If the selected actor has displacement order
two on the literal quotient Vnext/C, then Vnext=U join C. The raw hypothesis
is the corresponding relative index of [Vnext,⟨actor⟩] joined with C over C.

The quotient packet gives an elementary module and a residual image with
no fixed vectors. The actual E-generators are the predecessor actor subgroup
and its selected conjugate. Its index-two coatom has central image because
its commutator with E lies in the next two-core, which acts trivially on the
quotient. The two-conjugate transvection bound therefore gives quotient order
at most four. The image of U is nontrivial: otherwise the residual and the
initial-core actor would both centralize Za, contradicting the neighboring
center-normalizer theorem and edge generation. An invariant subgroup of
order two is fixed pointwise, so the image has order at least four and is the
whole quotient. Exact map/comap identities give the claimed raw span.

Source: Stellmacher, Journal of Algebra 190 (1997), proof of (8.6)(13), printed
p.43, the conditional fixed/support decomposition. The proof retains the
selected actor and subgroups. It needs only the established first-commutator
identity and geometric selection, without assuming the full action model
claimed at the end of source (12).
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SevenSix
open scoped commutatorElement IsMulCommutative
universe u

private theorem selected_span_of_small_fixed_quotient
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (previous : ctx.Γ.Vertex) (E A0 : Subgroup G) (actor : G)
    (geom : SectionNine.NineThreeGeometricData ctx.Γ
      ctx.criticalPath.firstStep ctx.criticalPath.a
      (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) E A0 actor)
    (hedge : E ⊔ (GAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ ctx.criticalPath.firstStep) =
      GAt ctx.Γ ctx.criticalPath.firstStep) :
    let V := VAt ctx.Γ ctx.criticalPath.firstStep
    let U := conjugateClosure (ZAt ctx.Γ ctx.criticalPath.a) E
    let C := V ⊓ Subgroup.centralizer (twoResidualIn E : Set G)
    ∀ hN : (C.subgroupOf V).Normal, let _ := hN
      ∀ (_hW : IsElementaryAbelian 2 (V ⧸ C.subgroupOf V))
        (action : E →* MulAut (V ⧸ C.subgroupOf V)),
          (∀ actor : E, ∀ point : V,
            action actor (QuotientGroup.mk' (C.subgroupOf V) point) =
              QuotientGroup.mk' (C.subgroupOf V)
                ⟨(actor:G)*(point:G)*(actor:G)⁻¹,
                  (Subgroup.mem_normalizer_iff.mp
                    (stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.firstStep
                      (geom.group_le actor.property)) point).mp point.property⟩) →
          FixedPoints.subgroup ((twoResidualAmbient (⊤ : Subgroup E)).map action)
            (V ⧸ C.subgroupOf V) = ⊥ →
          Nat.card (V ⧸ C.subgroupOf V) ≤ 4 → V = U ⊔ C := by
  classical
  dsimp only
  intro hN
  let _ := hN
  intro hW action haction hfixed hbound
  let _ := hW
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let V := VAt Γ cp.firstStep
  let U := conjugateClosure (ZAt Γ cp.a) E
  let R := twoResidualIn E
  let C := V ⊓ Subgroup.centralizer (R : Set G)
  let W := V ⧸ C.subgroupOf V
  let q := QuotientGroup.mk' (C.subgroupOf V)
  let J := (U.subgroupOf V).map q
  let A := VAt Γ previous ⊓ QAt Γ cp.a
  have hRE : R ≤ E := twoResidualIn_le E
  have hAE : A ≤ E := geom.generated ▸ le_sup_left
  have hfirst : cp.firstStep ∈ Neighborhood Γ cp.a :=
    (mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  have hZaU : ZAt Γ cp.a ≤ U := by
    intro z hz
    exact Subgroup.subset_closure ⟨(1:E),⟨z,hz⟩,by simp⟩
  have hUN : E ≤ Subgroup.normalizer (U : Set G) :=
    eight_six_conjugate_closure_normalizer _ _
  have hUV : U ≤ V := eight_six_conjugate_closure_le _ _ _
    (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.1
    (geom.group_le.trans (stabilizer_le_normalizer_v Γ cp.firstStep))
  have hnot : ¬ U ≤ C := by
    intro hUC
    have hRA : R ⊔ A = E := by
      refine le_antisymm (sup_le hRE hAE) ?_
      rw [geom.generated]
      apply sup_le le_sup_right
      rintro g ⟨a,ha,rfl⟩
      exact (R ⊔ A).mul_mem
        ((R ⊔ A).mul_mem (Subgroup.mem_sup_left geom.residual_mem)
          (Subgroup.mem_sup_right ha))
        ((R ⊔ A).inv_mem (Subgroup.mem_sup_left geom.residual_mem))
    have hRcentral : R ≤ Subgroup.centralizer (ZAt Γ cp.a : Set G) :=
      (Subgroup.le_centralizer_iff.mp (hUC.trans inf_le_right)).trans
        (Subgroup.centralizer_le hZaU)
    have hAcentral : A ≤ Subgroup.centralizer (ZAt Γ cp.a : Set G) :=
      inf_le_right.trans (Subgroup.le_centralizer_iff.mp
        (((lemma_seven_three ctx.sectionSeven Γ).center_core cp.a cp.firstStep hfirst).trans
          ((omegaOneCenter_le_centerAmbient _).trans (centerAmbient_le_centralizer _))))
    have hEcentral : E ≤ Subgroup.centralizer (ZAt Γ cp.a : Set G) := by
      rw [←hRA]
      exact sup_le hRcentral hAcentral
    apply neighbor_center_not_normalized ctx.sectionSeven Γ cp.firstStep cp.a
      ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj))
    change GAt ctx.Γ ctx.criticalPath.firstStep ≤ Subgroup.normalizer (ZAt Γ cp.a : Set G)
    rw [←hedge]
    exact sup_le (hEcentral.trans (Subgroup.centralizer_le_normalizer _))
      (inf_le_left.trans (stabilizer_le_normalizer_z Γ cp.a))
  have hJne : J ≠ ⊥ := by
    intro hbot
    have hker := (Subgroup.map_eq_bot_iff (f := q) (H := U.subgroupOf V)).mp hbot
    apply hnot
    intro u hu
    exact (QuotientGroup.eq_one_iff (N := C.subgroupOf V) (⟨u,hUV hu⟩ : V)).mp
      (MonoidHom.mem_ker.mp (hker hu))
  have hJinv (e : E) (w : W) (hw : w ∈ J) : action e w ∈ J := by
    obtain ⟨v,hv,rfl⟩ := hw
    rw [haction]
    exact Subgroup.mem_map_of_mem q
      ((Subgroup.mem_normalizer_iff.mp (hUN e.property) v).mp hv)
  have hJnotTwo : Nat.card J ≠ 2 := by
    intro htwo
    obtain ⟨z,hzne,hz⟩ := (Nat.card_eq_two_iff' (1:J)).mp htwo
    have hfix (e : E) (w : W) (hw : w ∈ J) : action e w = w := by
      by_cases hone : w = 1
      · simp [hone]
      have hmove : action e w ≠ 1 := by
        intro hh
        exact hone ((action e).injective (hh.trans (map_one (action e)).symm))
      exact congrArg Subtype.val
        ((hz ⟨action e w,hJinv e w hw⟩ (fun hh => hmove (congrArg Subtype.val hh))).trans
          (hz ⟨w,hw⟩ (fun hh => hone (congrArg Subtype.val hh))).symm)
    have hJF : J ≤ FixedPoints.subgroup
        ((twoResidualAmbient (⊤ : Subgroup E)).map action) W := by
      intro w hw r
      obtain ⟨e,he,heq⟩ := r.property
      change (r : MulAut W) w = w
      rw [←heq]
      exact hfix e w hw
    exact hJne (le_bot_iff.mp (hJF.trans_eq hfixed))
  have hJtwo : IsPGroup 2 J := (IsElementaryAbelian.isPGroup 2 W).to_subgroup J
  have hJpos : 1 < Nat.card J := (Subgroup.one_lt_card_iff_ne_bot J).mpr hJne
  have hJbig : 4 ≤ Nat.card J := by
    by_contra! hsmall
    obtain ⟨n,hn⟩ := hJtwo.exists_card_eq
    have hnsmall : n ≤ 1 := by
      by_contra! hlarge
      have hp : 4 ≤ 2^n := by
        calc 4 = 2^2 := by norm_num
             _ ≤ 2^n := Nat.pow_le_pow_right (by decide) hlarge
      omega
    interval_cases n
    · have hone : Nat.card J = 1 := by simpa only [pow_zero] using hn
      omega
    · exact hJnotTwo (by simpa using hn)
  change Nat.card W ≤ 4 at hbound
  have hJtop : J = ⊤ := Subgroup.eq_top_of_card_eq J
    (by
      have hc := J.card_le_card_group
      change Nat.card J ≤ Nat.card W at hc
      change Nat.card J = Nat.card W
      omega)
  have hpull := congrArg (fun K : Subgroup W => K.comap q) hJtop
  change ((U.subgroupOf V).map q).comap q = (⊤ : Subgroup W).comap q at hpull
  rw [Subgroup.comap_map_eq,QuotientGroup.ker_mk',Subgroup.comap_top] at hpull
  have hmap := congrArg (fun K : Subgroup V => K.map V.subtype) hpull
  rw [Subgroup.map_sup,Subgroup.map_subgroupOf_eq_of_le hUV,
    Subgroup.map_subgroupOf_eq_of_le (show C ≤ V from inf_le_left),
    ← MonoidHom.range_eq_map,Subgroup.range_subtype] at hmap
  exact hmap.symm

public theorem eight_six_transvection_fixed_span
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (hcomm : ⁅VAt ctx.Γ ctx.criticalPath.firstStep,
      QAt ctx.Γ ctx.criticalPath.firstStep⁆ = ZAt ctx.Γ ctx.criticalPath.firstStep)
    (previous : ctx.Γ.Vertex) (E A0 : Subgroup G) (actor : G)
    (geom : SectionNine.NineThreeGeometricData ctx.Γ
      ctx.criticalPath.firstStep ctx.criticalPath.a
      (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) E A0 actor)
    (hedge : E ⊔ (GAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ ctx.criticalPath.firstStep) =
      GAt ctx.Γ ctx.criticalPath.firstStep)
    (ha : actor ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a)
    (htransvection :
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓
        Subgroup.centralizer (twoResidualIn E : Set G)).relIndex
        (⁅VAt ctx.Γ ctx.criticalPath.firstStep,Subgroup.zpowers actor⁆ ⊔
          (VAt ctx.Γ ctx.criticalPath.firstStep ⊓
            Subgroup.centralizer (twoResidualIn E : Set G))) = 2) :
    VAt ctx.Γ ctx.criticalPath.firstStep =
      conjugateClosure (ZAt ctx.Γ ctx.criticalPath.a) E ⊔
        (VAt ctx.Γ ctx.criticalPath.firstStep ⊓
          Subgroup.centralizer (twoResidualIn E : Set G)) := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let V := VAt Γ cp.firstStep
  let C := V ⊓ Subgroup.centralizer (twoResidualIn E : Set G)
  let A := VAt Γ previous ⊓ QAt Γ cp.a
  have hAE : A ≤ E := geom.generated ▸ le_sup_left
  have hA0A : A0 ≤ A := geom.coatom_eq ▸ inf_le_left
  have hA0E : A0 ≤ E := hA0A.trans hAE
  have hxE : geom.x ∈ E := twoResidualIn_le E geom.residual_mem
  let a : E := ⟨actor,hAE ha⟩
  let x : E := ⟨geom.x,hxE⟩
  let Ai := A.subgroupOf E
  let A0i := A0.subgroupOf E
  have ha0 : actor ∉ A0 := by
    intro hh
    apply geom.actor_outside
    exact (geom.coatom_eq ▸ hh).2
  have hindex : A0.relIndex A = 2 := by
    have hh := (A0.subgroupOf A).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA0A).toEquiv] at hh
    change A0.relIndex A * Nat.card A0 = Nat.card A at hh
    have hcount : Nat.card A = 2 * Nat.card A0 := geom.coatom_card
    have hp : 0 < Nat.card A0 := Nat.card_pos
    nlinarith
  have hAsp : A = Subgroup.zpowers actor ⊔ A0 := by
    apply le_antisymm ?_ (sup_le (Subgroup.zpowers_le.mpr ha) hA0A)
    intro g hg
    by_cases hg0 : g ∈ A0
    · exact Subgroup.mem_sup_right hg0
    have hk : actor⁻¹ * g ∈ A0 := by
      have hh := (A0.subgroupOf A).mul_mem_iff_of_index_two hindex
        (a := ⟨actor⁻¹,A.inv_mem ha⟩) (b := ⟨g,hg⟩)
      exact hh.mpr (by simp only [Subgroup.mem_subgroupOf,Subgroup.inv_mem_iff,ha0,hg0])
    have hm := (Subgroup.zpowers actor ⊔ A0).mul_mem
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers actor)) (Subgroup.mem_sup_right hk)
    simpa only [mul_inv_cancel_left] using hm
  have hAi : Ai = Subgroup.zpowers a ⊔ A0i := by
    apply Subgroup.map_injective E.subtype_injective
    rw [Subgroup.map_sup,MonoidHom.map_zpowers,
      Subgroup.map_subgroupOf_eq_of_le hA0E,Subgroup.map_subgroupOf_eq_of_le hAE]
    exact hAsp
  have hconj : (Ai.conjBy x).map E.subtype = A.conjBy geom.x := by
    calc
      (Ai.conjBy x).map E.subtype = (Ai.map E.subtype).conjBy geom.x := by
        simp only [Subgroup.conjBy,Subgroup.map_map]
        rfl
      _ = A.conjBy geom.x := by rw [Subgroup.map_subgroupOf_eq_of_le hAE]
  have hgen : (⊤ : Subgroup E) = Ai ⊔ Ai.conjBy x := by
    apply Subgroup.map_injective E.subtype_injective
    rw [Subgroup.map_sup,hconj,Subgroup.map_subgroupOf_eq_of_le hAE,
      ←MonoidHom.range_eq_map,Subgroup.range_subtype]
    exact geom.generated
  have hA0two : IsPGroup 2 A0i := by
    have hQtwo : IsPGroup 2 (QAt Γ cp.a) := by
      change IsPGroup 2 (Γ.twoCoreAt cp.a)
      rw [Γ.twoCoreAt_def]
      exact (pCore_isPGroup (p := 2)).map _
    exact (hQtwo.to_le (hA0A.trans inf_le_right)).of_equiv
      (Subgroup.subgroupOfEquivOfLe hA0E).symm
  obtain ⟨hN,hW,action,haction,hkernel,hfixed⟩ := eight_six_residual_fixed_quotient_module
    ctx hcenter hlength hcard hcomm E geom.group_le
  let _ := hN
  let _ := hW
  have hEV : E ≤ Subgroup.normalizer (V : Set G) :=
    geom.group_le.trans (stabilizer_le_normalizer_v Γ cp.firstStep)
  have hcentral : A0i.map action ≤ Subgroup.centralizer (action.range : Set _) := by
    rintro mover ⟨b,hb,rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro image ⟨e,rfl⟩
    have hk : ⁅e,b⁆ ∈ action.ker := hkernel
      (geom.coatom_commutator (Subgroup.commutator_mem_commutator e.property hb))
    have hone : ⁅action e,action b⁆ = 1 := by
      rw [←map_commutatorElement]
      exact MonoidHom.mem_ker.mp hk
    exact commutatorElement_eq_one_iff_mul_comm.mp hone
  have hcyclic : (Subgroup.zpowers actor).subgroupOf E = Subgroup.zpowers a := by
    apply Subgroup.map_injective E.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le (Subgroup.zpowers_le.mpr (hAE ha)),
      MonoidHom.map_zpowers]
    rfl
  have hAV : ⁅V,Subgroup.zpowers actor⁆ ≤ V :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((Subgroup.zpowers_le.mpr (hAE ha)).trans hEV)
  have hrel := Subgroup.relIndex_sup_right
    ((⁅V,Subgroup.zpowers actor⁆).subgroupOf V) (C.subgroupOf V)
  rw [←Subgroup.subgroupOf_sup hAV inf_le_left,
    Subgroup.relIndex_subgroupOf (sup_le hAV inf_le_left),
    Subgroup.relIndex_subgroupOf hAV] at hrel
  have hrank : Nat.card (commutatorAction (Subgroup.zpowers (action a))
      (V ⧸ C.subgroupOf V)) = 2 := by
    have hh := Subgroup.quotient_conjugation_commutatorAction_card E V C
      (Subgroup.zpowers actor) hEV (Subgroup.zpowers_le.mpr (hAE ha)) hN action haction
    rw [hcyclic,MonoidHom.map_zpowers] at hh
    exact hh.trans (hrel.symm.trans htransvection)
  have hbound := SectionThree.central_coatom_transvection_module_card_le_four
    action Ai A0i a x hgen hAi hA0two hcentral hfixed hrank
  exact selected_span_of_small_fixed_quotient ctx previous E A0 actor geom hedge
    hN hW action haction hfixed hbound

end Stellmacher.SectionEight
