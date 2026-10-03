module
public import Stellmacher.SectionNine.DistanceOneFixedComplementContainment
public import Stellmacher.SectionNine.NineThreeBaumannFixedGeneration
public import Stellmacher.SectionFiveToSeven.SixFourGeneratingResidual
public import Stellmacher.SectionFiveToSeven.SixFourInvariantSeedTransfer
public import Stellmacher.QuotientModuleFixedNormalizer
public import Stellmacher.ElementaryAbelianMaxJFixedCenter
public import Stellmacher.SectionEight.LocalQuotientOddCoreSupplement

/-!
# The fixed complement vanishes when the native Thompson subgroup centralizes

At distance one in the original ambient context, suppose the native Thompson
subgroup of the edge Sylow centralizes the initial vertex center. Then the
fixed subgroup of F=[O₂′(bar G_a),image V] on that center is trivial.

Its ambient image Y lies in the two-center intersection, hence is centralized
by the extracted generating group. The maximum-elementary centralizer theorem
places the initial center in Ω₁Z(J(T)), so the Baumann subgroup fixes it and
contains Y. The initial residual normalizes Y through the exact witness:
its image lies in the odd core, which normalizes F. A nonzero Y is therefore
an invariant two-subgroup of the join of that residual, the Baumann group,
and a selected residual K in the next stabilizer's centralizer of Y.

The actual extraction generates the next stabilizer with the edge Sylow.
The generating-residual theorem chooses K with K=[K,B] and K S=P₂. The
invariant-seed form of the repeated (6.4) transfer makes K centralize the
entire initial module, contradicting the actual (7.6) centralizer-generation
obstruction. All transfers retain Hypothesis Two on its original ambient
group; no normality of F in the whole initial stabilizer is asserted.

Source: Stellmacher (9.1), the centralizing native-Thompson branch between
(7) and (8), Journal of Algebra 190 (1997), p.47, completed using the repeated
(6.4) argument on p.32; refs/files/stellmacher-n-group.pdf.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix Subgroup
universe u
private theorem fixed_seed_contradiction
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (h : HypothesisTwo H S0 S P1 P2) (hS : S = (S0 : Subgroup H))
    (hcomm : ⁅P2,omegaOneCenter S⁆ = ⊥)
    (W : Subgroup H) (hWne : W ≠ ⊥) (hWB : W ≤ baumannIn S)
    (hBW : baumannIn S ≤ centralizer (W : Set H))
    (hRW : twoResidualAmbient P1 ≤ normalizer (W : Set H))
    (hgen : (P2 ⊓ centralizer (W : Set H)) ⊔ S = P2)
    (hproper : (P2 ⊓ centralizer (sectionSixV S P1 : Set H)) ⊔ S ≠ P2) : False := by
  let C := P2 ⊓ centralizer (W : Set H)
  let T := S ⊓ centralizer (W : Set H)
  have hWS : W ≤ S := hWB.trans inf_le_left
  have hWP : W ≤ P2 := hWS.trans h.fiveOne.P2_mem.1.2.1.1
  have hWC : W ≤ C := le_inf hWP (by
    intro w hw
    exact (hBW (hWB hw)))
  have hCn : C ≤ normalizer (W : Set H) :=
    inf_le_right.trans (Subgroup.centralizer_le_normalizer _)
  have hWcore : W ≤ twoCoreIn C := by
    rw [← map_subgroupOf_eq_of_le hWC]
    apply map_mono
    exact le_sSup ⟨(normal_subgroupOf_iff_le_normalizer hWC).mpr hCn,
      ((hS ▸ S0.isPGroup').to_le hWS).comap_of_injective C.subtype C.subtype_injective⟩
  have hcore : twoCoreIn C ≠ ⊥ := fun he => hWne (bot_unique (hWcore.trans_eq he))
  obtain ⟨K,hKC,hKB,hKS,_⟩ := sixFour_generating_residual h hS C T inf_le_left
    (le_inf inf_le_left hBW) (le_inf (inf_le_left.trans h.fiveOne.P2_mem.1.2.1.1) inf_le_right)
    inf_le_left hgen hcore
  have hKW := hKC.trans inf_le_right
  have hVK := sixFour_invariant_seed_transfer h hcomm K (hKC.trans inf_le_left) hKB
    W hWne hWS (hWB.trans le_sup_right)
    (sup_le (sup_le hRW (hKW.trans (Subgroup.centralizer_le_normalizer _)))
      (hBW.trans (Subgroup.centralizer_le_normalizer _)))
  apply hproper
  apply le_antisymm (sup_le inf_le_left h.fiveOne.P2_mem.1.2.1.1)
  apply hKS.ge.trans
  exact sup_le_sup_right (le_inf (hKC.trans inf_le_left)
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hVK))) S
end Stellmacher.SectionNine

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix Subgroup
universe u
private theorem map_inf_centralizer_injective
    {G H : Type*} [Group G] [Group H] (f : G →* H) (hf : Function.Injective f)
    (A K : Subgroup G) :
    (A ⊓ centralizer (K : Set G)).map f = A.map f ⊓ centralizer (K.map f : Set H) := by
  apply le_antisymm
  · rintro _ ⟨a,ha,rfl⟩
    refine ⟨mem_map_of_mem f ha.1,mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨k,hk,rfl⟩
    simpa only [map_mul] using congrArg f (mem_centralizer_iff.mp ha.2 k hk)
  · rintro _ ⟨⟨a,ha,rfl⟩,hc⟩
    refine ⟨a,⟨ha,mem_centralizer_iff.mpr ?_⟩,rfl⟩
    intro k hk
    apply hf
    simpa only [map_mul] using mem_centralizer_iff.mp hc (f k) (mem_map_of_mem f hk)

public theorem distance_one_fixed_complement_bot_of_thompson_centralizes
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1) (data : DistanceOneActionData ctx)
    (w : QuotientModuleWitness (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓ centralizer
        (ZAt ctx.Γ ctx.criticalPath.a : Set G)) (ZAt ctx.Γ ctx.criticalPath.a))
    (hJ : elementaryAbelianMaxJ T ≤ centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set G)) :
    let next := ctx.Γ.act data.x⁻¹ ctx.criticalPath.a
    let V := (z ctx.Γ ctx.criticalPath.a ⊓ stabilizer ctx.Γ next) ⊔
      (z ctx.Γ next ⊓ stabilizer ctx.Γ ctx.criticalPath.a)
    let _ := w.groupX
    let _ := MulDistribMulAction.compHom (ZAt ctx.Γ ctx.criticalPath.a) w.action
    let X := (V.subgroupOf (GAt ctx.Γ ctx.criticalPath.a)).map w.projection
    FixedPoints.subgroup (⁅SectionOne.oddCore w.X,X⁆ : Subgroup w.X)
      (ZAt ctx.Γ ctx.criticalPath.a) = ⊥ := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.a
  let Za := ZAt Γ cp.a
  let next := Γ.act data.x⁻¹ cp.a
  let V := (z Γ cp.a ⊓ stabilizer Γ next) ⊔ (z Γ next ⊓ stabilizer Γ cp.a)
  let _ := w.groupX
  let _ := w.finiteX
  let _ := MulDistribMulAction.compHom Za w.action
  let X := (V.subgroupOf P).map w.projection
  let F := ⁅SectionOne.oddCore w.X,X⁆
  let Y := (FixedPoints.subgroup F Za).map Za.subtype
  let YH := Y.map embedding
  change FixedPoints.subgroup F Za = ⊥
  by_contra hfix
  have hYne : Y ≠ ⊥ := by
    intro he
    exact hfix ((map_eq_bot_iff_of_injective _ Za.subtype_injective).mp he)
  have hYHne : YH ≠ ⊥ := by
    intro he
    exact hYne ((map_eq_bot_iff_of_injective _ ctx.embedding_injective).mp he)
  have hfirst : cp.firstStep ∈ neighborhood Γ cp.a :=
    (mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  let _ : IsElementaryAbelian 2 Za := z_isElementaryAbelian_of_neighbor ctx.sectionSeven Γ hfirst
  have hZaQ : Za ≤ QAt Γ cp.a := ((lemma_seven_three ctx.sectionSeven Γ).center_core _ _ hfirst).trans
    ((omegaOneCenter_le_centerAmbient _).trans (map_subtype_le _))
  have hZaT : Za ≤ T := hZaQ.trans (local_cores_le_edge_sylow ctx.sectionSeven Γ cp).1
  have hZaJ : Za ≤ omegaOneCenterAmbient (elementaryAbelianMaxJ T) :=
    elementary_centralizer_maxJ_le_omegaCenter T Za hZaT (le_centralizer_iff.mpr hJ)
  have hBZa : baumannIn T ≤ centralizer (Za : Set G) :=
    (inf_le_right : baumannIn T ≤ centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ T) : Set G)).trans (centralizer_le hZaJ)
  have hZaB : Za ≤ baumannIn T := le_inf hZaT (by
    intro a ha
    rw [mem_centralizer_iff]
    intro j hj
    exact (mem_centralizer_iff.mp (hJ (map_subtype_le _ hj)) a ha).symm)
  have hYI : Y ≤ z Γ cp.a ⊓ z Γ next := distance_one_relative_fixed_complement_le_intersection ctx hb data w
  have hYZ : Y ≤ Za := map_subtype_le _
  have hYB : Y ≤ baumannIn T := hYZ.trans hZaB
  have hBY : baumannIn T ≤ centralizer (Y : Set G) := hBZa.trans (centralizer_le hYZ)
  have hEY : data.E ≤ centralizer (Y : Set G) := by
    rw [le_centralizer_iff]
    intro y hy
    obtain ⟨yn,hyn,rfl⟩ := data.intersection_central (hYI hy)
    exact mem_centralizer_iff.mpr fun e he => congrArg Subtype.val
      ((mem_center_iff.mp hyn) ⟨e,he⟩)
  have hstep : cp.a' = cp.firstStep := by
    rw [← cp.path_end,← cp.path_first]
    congr 1
    exact Fin.ext hb
  have hgen : data.E ⊔ T = GAt Γ cp.firstStep :=
    next_stabilizer_sylow_generation_of_edge_generation ctx.toLocalContext data.E (by
      change data.E ⊔ (GAt Γ cp.a ⊓ GAt Γ cp.firstStep) = GAt Γ cp.firstStep
      rw [← hstep]
      exact data.edge_generated)
  have hamb := nine_two_ambient_setup ctx
  have hGa : P.map embedding = P1 := hamb.2.1
  have hGd : (GAt Γ cp.firstStep).map embedding = P2 := hamb.2.2.1
  have hZa : Za.map embedding = sectionSixV S P1 := nine_two_center_eq_sectionSixV ctx hGa
  have hBm : (baumannIn T).map embedding = baumannIn S := by
    change (T ⊓ centralizer (omegaOneCenterAmbient (elementaryAbelianMaxJ T) : Set G)).map embedding = _
    rw [baumann_map_injective embedding ctx.embedding_injective,ctx.map_S]
    rfl
  have hYHB : YH ≤ baumannIn S := hBm ▸ map_mono hYB
  have hBYH : baumannIn S ≤ centralizer (YH : Set H) := by
    rw [← hBm]
    rintro b ⟨b0,hb0,rfl⟩
    rw [mem_centralizer_iff]
    rintro y ⟨y0,hy0,rfl⟩
    simpa only [map_mul] using congrArg embedding (mem_centralizer_iff.mp (hBY hb0) y0 hy0)
  have hgenH : (P2 ⊓ centralizer (YH : Set H)) ⊔ S = P2 := by
    apply le_antisymm (sup_le inf_le_left ctx.hypothesisTwo.fiveOne.P2_mem.1.2.1.1)
    have hm := congrArg (map embedding) hgen
    rw [Subgroup.map_sup,ctx.map_S,hGd] at hm
    apply hm.ge.trans
    apply sup_le_sup_right
    apply le_inf ((map_mono (le_sup_left.trans_eq hgen)).trans_eq hGd)
    rintro e ⟨e0,he0,rfl⟩
    rw [mem_centralizer_iff]
    rintro y ⟨y0,hy0,rfl⟩
    simpa only [map_mul] using congrArg embedding (mem_centralizer_iff.mp (hEY he0) y0 hy0)
  have hRn : (twoResidualAmbient (⊤ : Subgroup P)).map P.subtype = EAt Γ cp.a := by
    rw [map_twoResidualAmbient_of_subgroup_image (⊤ : Subgroup P) P.subtype P
      (by rw [← MonoidHom.range_eq_map,range_subtype])]
    change twoResidualAmbient P = Γ.twoResidualAt cp.a
    rw [Γ.twoResidualAt_def]
    rfl
  have hRnative : (EAt Γ cp.a).subgroupOf P = twoResidualAmbient (⊤ : Subgroup P) := by
    rw [← hRn,subgroupOf_map_subtype_eq]
  have hRle : EAt Γ cp.a ≤ P := hRn ▸ map_subtype_le _
  have hRY : EAt Γ cp.a ≤ normalizer (Y : Set G) :=
    w.le_normalizer_fixedPoints_map _ hRle F (by
      rw [hRnative]
      exact (SectionEight.local_quotient_residual_image_le_oddCore ctx.sectionSeven Γ cp w).trans
        (normalizer_commutator_ge_left _ _))
  have hRm : (EAt Γ cp.a).map embedding = twoResidualAmbient P1 := by
    change (Γ.twoResidualAt cp.a).map embedding = _
    rw [Γ.twoResidualAt_def]
    exact map_twoResidualAmbient_of_subgroup_image P embedding P1 hGa
  have hRYH : twoResidualAmbient P1 ≤ normalizer (YH : Set H) := by
    rw [← hRm]
    exact (map_mono hRY).trans (le_normalizer_map embedding)
  have hnext := (lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).next_center
  have hOm : (ZAt Γ cp.firstStep).map embedding = omegaOneCenter S := by
    rw [show ZAt Γ cp.firstStep = omegaOneCenter T from hnext.1,← ctx.map_S]
    exact (omegaOneCenterAmbient_map_injective embedding ctx.embedding_injective T).symm
  have hcomm : ⁅P2,omegaOneCenter S⁆ = ⊥ := by
    rw [← hGd,← hOm,← map_commutator]
    have hz : ⁅GAt Γ cp.firstStep,ZAt Γ cp.firstStep⁆ = ⊥ := by
      apply commutator_eq_bot_iff_le_centralizer.mpr
      apply le_centralizer_iff.mpr
      rw [show ZAt Γ cp.firstStep = omegaOneCenter (GAt Γ cp.firstStep) from hnext.2]
      exact (omegaOneCenter_le_centerAmbient _).trans (centerAmbient_le_centralizer _)
    rw [hz,Subgroup.map_bot]
  have hproper : (P2 ⊓ centralizer (sectionSixV S P1 : Set H)) ⊔ S ≠ P2 := by
    intro he
    have hlocal : (GAt Γ cp.firstStep ⊓ centralizer (Za : Set G)) ⊔ T = GAt Γ cp.firstStep := by
      apply map_injective ctx.embedding_injective
      rw [Subgroup.map_sup,map_inf_centralizer_injective embedding ctx.embedding_injective,
        hGd,hZa,ctx.map_S]
      exact he
    apply (lemma_seven_six ctx.sectionSeven Γ cp).centralizer_join_proper
    apply le_antisymm (sup_le inf_le_right inf_le_right)
    apply hlocal.ge.trans
    exact sup_le_sup (by rw [inf_comm]) cp.S_le_edge_stabilizers
  exact fixed_seed_contradiction ctx.hypothesisTwo hamb.1 hcomm YH hYHne hYHB hBYH hRYH hgenH hproper
end Stellmacher.SectionNine
