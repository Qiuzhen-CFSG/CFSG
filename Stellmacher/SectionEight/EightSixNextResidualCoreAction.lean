module
public import Stellmacher.SectionEight.EightSixCommonStructure
public import Stellmacher.SectionEight.GeneratedEightSixIntersectionCommutator
public import Stellmacher.SectionEight.GeneratedEightSixSubgroupForcingHelper
public import Stellmacher.SectionThree.PSetResidualKernel
public import Theory.GroupAction.SubgroupQuotientFullAction

/-!
# The next residual acts trivially on its core modulo V in (8.6)

In the actual distance-two graph configuration, equation-one data imply
Qnext = Vnext join D. If the predecessor core part A is not contained in
Qnext, then [Qnext,O²(Gnext)] lies in Vnext. This is the general source
assertion (8); no small-order core bound or concrete central-product model
is required, so the result applies in the large-index branch.

Intersect the equation-one Sylow generation with Qnext. The A-intersection
lies in D, and normalization permits the product intersection calculation.
The transported neighbor commutator bound gives [D,A] ≤ Za ≤ Vnext;
A also normalizes Vnext, so [Qnext,A] ≤ Vnext. The literal conjugation
action on Qnext/Vnext therefore has A in its normal kernel. The PSet
normal-kernel theorem says that a kernel not containing the two-residual
has every two-subgroup inside the two-core. Since A escapes that core,
the residual is in the kernel, yielding the required ambient commutator.

Source: Stellmacher, Journal of Algebra 190 (1997), (8.6), printed p.43,
assertion (8); refs/files/stellmacher-n-group.pdf. The proof makes explicit
the local residual-kernel argument behind the printed implication.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
open scoped Pointwise commutatorElement
universe u

public theorem eight_six_next_core_eq_v_sup_intersection
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hlength : ctx.criticalPath.length = 2)
    (previous : ctx.Γ.Vertex) (D L Q : Subgroup G)
    (hprev : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a)
    (hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hL : L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a))
    (data : EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q) :
    QAt ctx.Γ ctx.criticalPath.firstStep = VAt ctx.Γ ctx.criticalPath.firstStep ⊔ D := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let A := VAt Γ previous ⊓ QAt Γ cp.a
  let V := VAt Γ cp.firstStep
  let R := QAt Γ cp.firstStep
  have hVR : V ≤ R := SevenSix.neighbor_join_le_core_of_length_gt_one Γ cp (by exact hlength ▸ by decide) _
  have hDR : D ≤ R := hD ▸ inf_le_right
  have hAprevious : A ≤ QAt Γ previous :=
    inf_le_left.trans (SevenSix.neighbor_join_le_core_of_length_gt_one Γ cp
      (by exact hlength ▸ by decide) previous)
  have hAR : A ⊓ R ≤ D := by rw [hD]; exact le_inf (inf_le_left.trans hAprevious) inf_le_right
  have hAinitial : A ≤ GAt Γ cp.a := inf_le_right.trans (by
    change Γ.twoCoreAt cp.a ≤ Γ.vertexStabilizer cp.a
    rw [Γ.twoCoreAt_def]; exact Subgroup.map_subtype_le _)
  have hANV : A ≤ Subgroup.normalizer (V : Set G) := by
    have hAnext : A ≤ GAt Γ cp.firstStep := (inf_le_right : A ≤ QAt Γ cp.a).trans
      ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core cp.a cp.firstStep
        ((SevenSix.mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj) default).2.2
    exact hAnext.trans (stabilizer_le_normalizer_v Γ cp.firstStep)
  have hAND : A ≤ Subgroup.normalizer (D : Set G) :=
    hAinitial.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer data.intersection_normal.1).mp
      data.intersection_normal.2)
  have hAN : A ≤ Subgroup.normalizer ((V ⊔ D : Subgroup G) : Set G) :=
    Subgroup.le_normalizer_iff.mpr fun a ha z hz => by
      have hm : (V ⊔ D).map (MulAut.conj a).toMonoidHom = V ⊔ D := by
        rw [Subgroup.map_sup]
        exact congrArg₂ (· ⊔ ·)
          (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hANV ha))
          (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hAND ha))
      exact hm ▸ Subgroup.mem_map_of_mem _ hz
  have hRL : R ≤ L := by
    rw [hL]
    exact eight_six_neighbor_core_le_closure ctx.sectionSeven Γ cp.a previous cp.firstStep hprev
      ((SevenSix.mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj)
  have hRS : R ≤ S := (SevenSix.local_cores_le_edge_sylow ctx.sectionSeven Γ cp).2
  have hRgen : R ≤ A ⊔ (V ⊔ D) := by
    have hRjoin : R ≤ V ⊔ Q := (le_inf hRL hRS).trans_eq data.sylow_intersection
    apply hRjoin.trans
    rw [data.core_generation]
    apply sup_le (le_sup_of_le_right le_sup_left)
    exact sup_le (sup_le le_sup_left (le_sup_of_le_right (inf_le_left.trans le_sup_left)))
      (le_sup_of_le_right le_sup_right)
  have hinter : (A ⊔ (V ⊔ D)) ⊓ R = V ⊔ D :=
    eight_six_sup_inter_eq_of_normalizes A (V ⊔ D) R hAN (sup_le hVR hDR)
      (hAR.trans le_sup_right)
  exact le_antisymm ((le_inf hRgen le_rfl).trans_eq hinter) (sup_le hVR hDR)

public theorem eight_six_next_core_actor_commutator_le_v
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hlength : ctx.criticalPath.length = 2)
    (previous : ctx.Γ.Vertex) (D L Q : Subgroup G)
    (hprev : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a)
    (hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hL : L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a))
    (data : EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q) :
    ⁅QAt ctx.Γ ctx.criticalPath.firstStep,
      VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a⁆ ≤
        VAt ctx.Γ ctx.criticalPath.firstStep := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let A := VAt Γ previous ⊓ QAt Γ cp.a
  let V := VAt Γ cp.firstStep
  let R := QAt Γ cp.firstStep
  have hRD : R = V ⊔ D := eight_six_next_core_eq_v_sup_intersection
    ctx hlength previous D L Q hprev hD hL data
  have hRG : R ≤ GAt Γ cp.firstStep := by
    change Γ.twoCoreAt cp.firstStep ≤ Γ.vertexStabilizer cp.firstStep
    rw [Γ.twoCoreAt_def]; exact Subgroup.map_subtype_le _
  have hDR : D ≤ R := hD ▸ inf_le_right
  have hAnext : A ≤ GAt Γ cp.firstStep := (inf_le_right : A ≤ QAt Γ cp.a).trans
    ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core cp.a cp.firstStep
      ((SevenSix.mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj) default).2.2
  have hVA : ⁅V,A⁆ ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp
    (hAnext.trans (stabilizer_le_normalizer_v Γ cp.firstStep))
  have hDA : ⁅D,A⁆ ≤ V :=
    (eight_six_intersection_neighbor_commutator_le ctx.sectionSeven Γ cp hcenter
      previous D L Q hD data previous hprev |>.trans
        (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.1) |>.trans' (by
          rw [Subgroup.commutator_comm]
          exact Subgroup.commutator_mono inf_le_left le_rfl)
  have hDN : D ≤ Subgroup.normalizer (V : Set G) :=
    (hDR.trans hRG).trans (stabilizer_le_normalizer_v Γ cp.firstStep)
  apply Subgroup.commutator_le.mpr
  intro x hx a ha
  have hx' : x ∈ (D : Set G) * (V : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right D V hDN, sup_comm]
    exact hRD.le hx
  obtain ⟨d,hd,v,hv,rfl⟩ := hx'
  rw [commutatorElement_mul_left_eq_conj_mul]
  exact V.mul_mem (Subgroup.le_normalizer_iff.mp hDN d hd _
    (Subgroup.commutator_le.mp hVA v hv a ha))
    (Subgroup.commutator_le.mp hDA d hd a ha)

public theorem eight_six_next_residual_core_commutator_le_v
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hlength : ctx.criticalPath.length = 2)
    (previous : ctx.Γ.Vertex) (D L Q : Subgroup G)
    (hprev : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a)
    (hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hL : L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a))
    (data : EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q)
    (hnot : ¬ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a ≤
      QAt ctx.Γ ctx.criticalPath.firstStep) :
    ⁅QAt ctx.Γ ctx.criticalPath.firstStep, EAt ctx.Γ ctx.criticalPath.firstStep⁆ ≤
      VAt ctx.Γ ctx.criticalPath.firstStep := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.firstStep
  let A := VAt Γ previous ⊓ QAt Γ cp.a
  let V := VAt Γ cp.firstStep
  let R := QAt Γ cp.firstStep
  have hRG : R ≤ P := by
    change Γ.twoCoreAt cp.firstStep ≤ Γ.vertexStabilizer cp.firstStep
    rw [Γ.twoCoreAt_def]; exact Subgroup.map_subtype_le _
  have hRP : P ≤ Subgroup.normalizer (R : Set G) := SevenSix.stabilizer_le_normalizer_q Γ _
  have hVP : P ≤ Subgroup.normalizer (V : Set G) := stabilizer_le_normalizer_v Γ _
  have hN : (V.subgroupOf R).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hRG.trans hVP)
  let _ := hN
  obtain ⟨ρ,hρ⟩ := Subgroup.exists_quotient_conjugation_action P R V hRP hVP hN
  have hRA : ⁅R,A⁆ ≤ V := eight_six_next_core_actor_commutator_le_v
    ctx hcenter hlength previous D L Q hprev hD hL data
  have hAker : A.subgroupOf P ≤ ρ.ker :=
    Subgroup.quotient_conjugation_action_kills_commutator_layer P R V A hN hRP hRA ρ hρ
  let K := ρ.ker.map P.subtype
  have hKP : K ≤ P := Subgroup.map_subtype_le _
  have hKN : (K.subgroupOf P).Normal := by
    rw [subgroupOf_map_subtype_eq]
    infer_instance
  have hAP : A ≤ P := (inf_le_right : A ≤ QAt Γ cp.a).trans
    ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core cp.a cp.firstStep
      ((SevenSix.mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj) default).2.2
  have hAK : A ≤ K := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hAP]
    exact Subgroup.map_mono hAker
  have hAp : IsPGroup 2 A :=
    ((pCore_isPGroup (p := 2) (G := GAt Γ cp.a)).map (GAt Γ cp.a).subtype).to_le
      ((inf_le_right : A ≤ QAt Γ cp.a).trans_eq (Γ.twoCoreAt_def cp.a))
  have hres : twoResidualAmbient P ≤ K := by
    by_contra hres
    have hP := (SevenSix.edge_local_data ctx.sectionSeven Γ cp).2
    have hthree : SectionThree.Hypotheses G S := by
      refine ⟨?_,?_,?_⟩
      · obtain ⟨_,sylow,hsylow⟩ := hP.1.1.2.1
        have hcoreN := hP.1.1.2.2.1
        have hSne : S ≠ ⊥ := by
          intro heq
          apply hcoreN
          have hcoreS : twoCoreIn P ≤ S := by
            rw [← hsylow]
            exact Subgroup.map_mono ((pCore_isPGroup (p := 2)).le_sylow_of_normal sylow)
          exact le_bot_iff.mp (hcoreS.trans_eq heq)
        have htwo : IsPGroup 2 S := hsylow ▸ sylow.isPGroup'.map P.subtype
        have hdiv : 2 ∣ Nat.card S := htwo.card_eq_or_dvd.resolve_left
          (fun he => hSne (Subgroup.card_eq_one.mp he))
        exact even_iff_two_dvd.mpr (hdiv.trans S.card_subgroup_dvd_card)
      · intro heq
        apply hnot
        have hAS : A ≤ S := (inf_le_right : A ≤ QAt Γ cp.a).trans
          (SevenSix.local_cores_le_edge_sylow ctx.sectionSeven Γ cp).1
        exact (hAS.trans_eq heq).trans bot_le
      · obtain ⟨_,sylow,hsylow⟩ := hP.1.1.2.1
        exact hsylow ▸ sylow.isPGroup'.map P.subtype
    have hbound := SectionThree.pSet_two_subgroup_normal_kernel_le_core S hthree P K A
      ((pFamily_iff_pSet (⊤ : Subgroup G) S P).mp hP.1) hP.2 hKP hKN hres hAK hAp
    exact hnot (hbound.trans_eq (Γ.twoCoreAt_def cp.firstStep).symm)
  have hER : EAt Γ cp.firstStep ≤ P := by
    change Γ.twoResidualAt cp.firstStep ≤ Γ.vertexStabilizer cp.firstStep
    rw [Γ.twoResidualAt_def]
    exact Subgroup.map_subtype_le _
  have hEK : EAt Γ cp.firstStep ≤ K := by
    rw [EAt, CosetGraphContext.e, Γ.twoResidualAt_def]
    exact hres
  rw [Subgroup.commutator_comm]
  apply Subgroup.commutator_le.mpr
  intro actor hactor point hpoint
  let aP : P := ⟨actor,hER hactor⟩
  let rR : R := ⟨point,hpoint⟩
  have haker : aP ∈ ρ.ker := by
    obtain ⟨k,hk,hka⟩ := hEK hactor
    have heq : k = aP := Subtype.ext hka
    exact heq ▸ hk
  have hact := congrArg (fun f : MulAut (R ⧸ V.subgroupOf R) =>
    f (QuotientGroup.mk' (V.subgroupOf R) rR)) (MonoidHom.mem_ker.mp haker)
  rw [hρ] at hact
  have hd := QuotientGroup.eq_iff_div_mem.mp hact
  change (actor * point * actor⁻¹) / point ∈ V at hd
  simpa [commutatorElement_def, div_eq_mul_inv] using hd

end Stellmacher.SectionEight
