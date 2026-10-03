module
public import Stellmacher.SectionEight.EightSixCostFourActorIndices
public import Theory.GroupAction.SixteenSupportFixedIndex

/-!
# The full actor fixed index in the cost-four branch

In the selected cost-four configuration of Stellmacher (8.6), the full
predecessor actor has common fixed subgroup of index eight on the actual
next quotient Vnext/Znext. The theorem retains the caller's quotient
normality proof, elementary structure, next-stabilizer conjugation action,
and the kernel containment supplied by the actual quotient producer.

The residual decomposition Vnext=YC with Y intersect C=Znext gives
complementary images in the quotient. The Y image has order sixteen and
is invariant under the actor, while source (11) and the fixed-core
containment from (14) make the C image fixed pointwise. The selected actor
has displacement order four. Its square and its commutators with the
other actors lie in the actual Frattini subgroup of Q and hence in D,
so its quotient action is a central involution. A quadratic full action
would lift to the ambient double-commutator bound forbidden by source (5)
and the large actor index. The elementary sixteen-support counting theorem
therefore gives fixed index eight.

This is the full fixed-index calculation in the cost-four paragraph of
Stellmacher, Journal of Algebra 190 (1997), proof of (8.6), printed p.44.
It assumes neither a quotient model nor the bounded classification result.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SevenSix
open scoped commutatorElement IsMulCommutative
universe u
public theorem eight_six_cost_four_full_fixed_index
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex) (D L Q : Subgroup G)
    (hprev : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep)
    (data : EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q)
    (E A0 : Subgroup G) (actor : G)
    (geom : SectionNine.NineThreeGeometricData ctx.Γ
      ctx.criticalPath.firstStep ctx.criticalPath.a
      (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) E A0 actor)
    (hcore : conjugateClosure (ZAt ctx.Γ ctx.criticalPath.a) E ≤
      QAt ctx.Γ ctx.criticalPath.a)
    (hedge : E ⊔ (GAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ ctx.criticalPath.firstStep) =
      GAt ctx.Γ ctx.criticalPath.firstStep)
    (hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hL : L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a))
    (ha : actor ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a)
    (hout : actor ∉ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hlarge : 4 * Nat.card
      ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊓ D : Subgroup G) ≤
      Nat.card (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a : Subgroup G))
    (hmin : ∀ other : G, other ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a →
      other ∉ QAt ctx.Γ ctx.criticalPath.firstStep →
        eightSixCommutatorCost ctx.Γ ctx.criticalPath actor ≤
          eightSixCommutatorCost ctx.Γ ctx.criticalPath other)
    (hQ : Q = twoCoreIn L)
    (hcost : eightSixCommutatorCost ctx.Γ ctx.criticalPath actor = 4)
    (hN : ((ZAt ctx.Γ ctx.criticalPath.firstStep).subgroupOf
      (VAt ctx.Γ ctx.criticalPath.firstStep)).Normal) :
    let _ := hN
    let P := GAt ctx.Γ ctx.criticalPath.firstStep
    let V := VAt ctx.Γ ctx.criticalPath.firstStep
    let Z := ZAt ctx.Γ ctx.criticalPath.firstStep
    ∀ (_hW : IsElementaryAbelian 2 (V ⧸ Z.subgroupOf V))
      (action : P →* MulAut (V ⧸ Z.subgroupOf V)),
      (∀ mover : P, ∀ point : V,
        action mover (QuotientGroup.mk' (Z.subgroupOf V) point) =
          QuotientGroup.mk' (Z.subgroupOf V)
            ⟨(mover:G)*(point:G)*(mover:G)⁻¹,
              (Subgroup.mem_normalizer_iff.mp
                (stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.firstStep
                  mover.property) point).mp point.property⟩) →
      pCore 2 P ≤ action.ker →
      (FixedPoints.subgroup
        (((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a).subgroupOf P).map action)
        (V ⧸ Z.subgroupOf V)).index = 8 := by
  classical
  let _ := hN
  dsimp only
  intro hW action haction hkernel
  let _ := hW
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.firstStep
  let V := VAt Γ cp.firstStep
  let Z := ZAt Γ cp.firstStep
  let A := VAt Γ previous ⊓ QAt Γ cp.a
  let R := QAt Γ cp.firstStep
  let Y := ⁅R,twoResidualIn E⁆
  let C := V ⊓ Subgroup.centralizer (twoResidualIn E : Set G)
  let W := V ⧸ Z.subgroupOf V
  let π : V →* W := QuotientGroup.mk' (Z.subgroupOf V)
  let B := (A.subgroupOf P).map action
  let U := (Y.subgroupOf V).map π
  let F := (C.subgroupOf V).map π
  have hAE : A ≤ E := geom.generated ▸ le_sup_left
  have hAP : A ≤ P := hAE.trans geom.group_le
  have hPV : P ≤ Subgroup.normalizer (V : Set G) := stabilizer_le_normalizer_v Γ _
  have hVR : V ≤ R := neighbor_join_le_core_of_length_gt_one Γ cp
    (by exact hlength ▸ by decide) _
  have hZV : Z ≤ V := (eight_six_first_step_fixed_line_local ctx hcenter hcard).2.trans
    (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.1
  have hZcard : Nat.card Z = 2 := (eight_six_first_step_fixed_line_local ctx hcenter hcard).1
  have hpacket := eight_six_selected_residual_decomposition ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL
  have hYC : Y ⊓ C = Z := hpacket.2.1
  have hsplit : V = Y ⊔ C := hpacket.2.2
  have hYV : Y ≤ V := hsplit.ge.trans' le_sup_left
  have hZY : Z ≤ Y := hYC.ge.trans inf_le_left
  have hZC : Z ≤ C := hYC.ge.trans inf_le_right
  have hEY : E ≤ Subgroup.normalizer (Y : Set G) :=
    le_normalizer_commutator_of_le_normalizers'
      (geom.group_le.trans (stabilizer_le_normalizer_q Γ cp.firstStep))
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (twoResidualIn_le E)).mp
        (twoResidualIn_normal E))
  have hfixed := (eight_six_selected_fixed_core_containment ctx hcenter hquot hlength hcard
    previous D L Q hprev hD hL hQ data E A0 actor geom hcore hedge ha hout hlarge hmin).1
  have hCcore : C ≤ QAt Γ cp.a := (inf_le_inf hVR le_rfl).trans hfixed
  have hCA : ⁅C,A⁆ ≤ Z :=
    (Subgroup.commutator_mono (le_inf (inf_le_inf hVR le_rfl) hCcore) le_rfl).trans
      (eight_six_selected_fixed_core_commutator_bounds ctx hcenter hquot hlength hcard
        previous D L Q hprev hD hL data E A0 actor geom hedge).1
  have hFfixed : F ≤ FixedPoints.subgroup B W := by
    rintro w ⟨c,hc,rfl⟩ b
    obtain ⟨a,ha,heq⟩ := b.property
    change (b : MulAut W) (π c) = π c
    rw [← heq]
    rw [haction]
    apply QuotientGroup.eq_iff_div_mem.mpr
    change (a:G)*(c:G)*(a:G)⁻¹/(c:G) ∈ Z
    have hh := (Subgroup.commutator_comm C A ▸ hCA)
      (Subgroup.commutator_mem_commutator ha hc)
    simpa only [commutatorElement_def,div_eq_mul_inv,Subgroup.coe_subtype] using hh
  have hUforward (a : P) (ha : (a:G) ∈ A) (w : W) (hw : w ∈ U) : action a w ∈ U := by
    obtain ⟨y,hy,rfl⟩ := hw
    rw [haction]
    exact Subgroup.mem_map_of_mem π
      ((Subgroup.mem_normalizer_iff.mp (hEY (hAE ha)) y).mp hy)
  let _ : IsInvariant B W U := ⟨by
    intro b w
    obtain ⟨a,ha,heq⟩ := b.property
    have hh : (b : MulAut W) = action a := heq.symm
    constructor
    · intro hw
      change (b : MulAut W) w ∈ U
      rw [hh]
      exact hUforward a ha w hw
    · intro hw
      have hinv := hUforward a⁻¹ (A.inv_mem ha) ((b : MulAut W) w) hw
      change w ∈ U
      rw [hh,map_inv] at hinv
      simpa only [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply] using hinv⟩
  have hUcard : Nat.card U = 16 := by
    change Nat.card ((Y.subgroupOf V).map (QuotientGroup.mk' (Z.subgroupOf V))) = 16
    rw [← Subgroup.relIndex_ker,QuotientGroup.ker_mk',Subgroup.relIndex_subgroupOf hYV]
    have hcount := (Z.subgroupOf Y).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZY).toEquiv,hZcard] at hcount
    have hYcard := (eight_six_cost_four_residual_card ctx hcenter hquot hlength hcard
      previous D L Q hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin hQ hcost).1
    change Z.relIndex Y * 2 = Nat.card Y at hcount
    change Nat.card Y = 32 at hYcard
    omega
  have hcompl : IsCompl U F := by
    apply isCompl_iff.mpr
    constructor
    · apply disjoint_iff.mpr
      apply le_bot_iff.mp
      rintro w ⟨⟨y,hy,hey⟩,⟨c,hc,hec⟩⟩
      have hdiff : y/c ∈ Z.subgroupOf V := QuotientGroup.eq_iff_div_mem.mp (hey.trans hec.symm)
      have hyC : (y:G) ∈ C := by
        have hh := C.mul_mem (hZC hdiff) hc
        change (y:G)/(c:G)*(c:G) ∈ C at hh
        simpa only [div_mul_cancel] using hh
      have hyZ := hYC.le ⟨hy,hyC⟩
      apply Subgroup.mem_bot.mpr
      rw [← hey]
      exact (QuotientGroup.eq_one_iff (N := Z.subgroupOf V) y).mpr hyZ
    · apply codisjoint_iff.mpr
      change (Y.subgroupOf V).map π ⊔ (C.subgroupOf V).map π = ⊤
      rw [← Subgroup.map_sup,← Subgroup.subgroupOf_sup hYV
        (show C ≤ V from inf_le_left),← hsplit]
      rw [Subgroup.subgroupOf_self]
      rw [← MonoidHom.range_eq_map]
      exact MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective (Z.subgroupOf V))
  have hAQ : A ≤ Q := data.core_generation ▸ le_sup_of_le_left le_sup_left
  have hQtwo : IsPGroup 2 Q := by
    rw [hQ,twoCoreIn]
    exact (pCore_isPGroup (p := 2)).map _
  let _ : Fact (IsPGroup 2 Q) := ⟨hQtwo⟩
  have hcore : R.subgroupOf P = pCore 2 P := by
    change (Γ.twoCoreAt _).subgroupOf P = _
    rw [Γ.twoCoreAt_def]
    exact Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
  have hsquare (a : P) (ha : (a:G) ∈ A) : (action a)^2 = 1 := by
    have hpowD : (a:G)^2 ∈ D := data.core_frattini_le
      (Subgroup.mem_map.mpr ⟨(⟨a,hAQ ha⟩:Q)^2,
        pth_power_mem_frattini_of_isPGroup (p := 2) (⟨a,hAQ ha⟩:Q),rfl⟩)
    rw [← map_pow]
    apply MonoidHom.mem_ker.mp
    apply hkernel
    rw [← hcore]
    exact (hD ▸ hpowD).2
  have hBtwo : IsPGroup 2 B :=
    ((hQtwo.to_le hAQ).of_equiv (Subgroup.subgroupOfEquivOfLe hAP).symm).map action
  let a : P := ⟨actor,hAP ha⟩
  have hacard : Nat.card (commutatorAction (Subgroup.zpowers (action a)) W) = 4 := by
    have hcyclic : (Subgroup.zpowers actor).subgroupOf P = Subgroup.zpowers a := by
      apply Subgroup.map_injective P.subtype_injective
      rw [Subgroup.map_subgroupOf_eq_of_le (Subgroup.zpowers_le.mpr (hAP ha)),
        MonoidHom.map_zpowers]
      rfl
    have hh := Subgroup.quotient_conjugation_commutatorAction_card P V Z
      (Subgroup.zpowers actor) hPV (Subgroup.zpowers_le.mpr (hAP ha)) hN action haction
    rw [hcyclic,MonoidHom.map_zpowers] at hh
    have hAV : ⁅V,Subgroup.zpowers actor⁆ ≤ V :=
      Subgroup.le_normalizer_iff_commutator_le_left.mp
        ((Subgroup.zpowers_le.mpr (hAP ha)).trans hPV)
    have hrel := Subgroup.relIndex_sup_right
      ((⁅V,Subgroup.zpowers actor⁆).subgroupOf V) (Z.subgroupOf V)
    rw [← Subgroup.subgroupOf_sup hAV hZV,
      Subgroup.relIndex_subgroupOf (sup_le hAV hZV),
      Subgroup.relIndex_subgroupOf hAV] at hrel
    exact hh.trans (hrel.symm.trans hcost)
  have hcentral : ∀ b ∈ B, Commute b (action a) := by
    rintro b ⟨g,hg,rfl⟩
    have hcommD : ⁅(g:G),actor⁆ ∈ D := data.core_frattini_le
      (Subgroup.mem_map.mpr ⟨⁅(⟨g,hAQ hg⟩:Q),(⟨actor,hAQ ha⟩:Q)⁆,
        commutator_le_frattini_of_isPGroup (p := 2)
          (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)),rfl⟩)
    apply commutatorElement_eq_one_iff_commute.mp
    rw [← map_commutatorElement]
    apply MonoidHom.mem_ker.mp
    apply hkernel
    rw [← hcore]
    exact (hD ▸ hcommD).2
  have hnonquadratic : commutatorAction₂ B W ≠ ⊥ := by
    intro hquad
    have hdouble : ⁅⁅V,A⁆,A⁆ ≤ Z := by
      apply Subgroup.commutator_le.mpr
      intro c hc b hb
      have hcommV : ⁅V,A⁆ ≤ V :=
        Subgroup.le_normalizer_iff_commutator_le_left.mp (hAP.trans hPV)
      let cV : V := ⟨c,hcommV hc⟩
      let bP : P := ⟨b,hAP hb⟩
      let bB : B := ⟨action bP,Subgroup.mem_map_of_mem action hb⟩
      have hcimage : π cV⁻¹ ∈ commutatorAction B W := by
        rw [Subgroup.quotient_conjugation_commutatorAction_eq_image P V Z A hPV hAP hN action haction]
        exact Subgroup.mem_map_of_mem π (⁅V,A⁆.inv_mem hc)
      have hdelta : (π cV⁻¹)⁻¹ * (bB • π cV⁻¹) ∈ commutatorAction₂ B W :=
        Subgroup.subset_closure ⟨bB,π cV⁻¹,hcimage,rfl⟩
      rw [hquad] at hdelta
      have hone : (π cV⁻¹)⁻¹ * action bP (π cV⁻¹) = 1 := hdelta
      rw [haction,← map_inv,← map_mul] at hone
      have hm := (QuotientGroup.eq_one_iff _).mp hone
      change (c⁻¹)⁻¹ * (b*c⁻¹*b⁻¹) ∈ Z at hm
      simpa only [inv_inv,commutatorElement_def,mul_assoc] using hm
    have hbound := eight_six_nonquadratic_actor_local ctx hcenter hquot hlength hcard
      previous D L Q hprev hD data A le_rfl hdouble
    have hpos : 0 < Nat.card (A ⊓ D : Subgroup G) := Nat.card_pos
    change Nat.card A ≤ 2 * Nat.card (A ⊓ D : Subgroup G) at hbound
    change 4 * Nat.card (A ⊓ D : Subgroup G) ≤ Nat.card A at hlarge
    omega
  exact fixedPoints_index_eq_eight_of_sixteen_support B U F hUcard hcompl hFfixed
    hBtwo (action a) (Subgroup.mem_map_of_mem action ha) (hsquare a ha) hcentral
    hacard hnonquadratic
end Stellmacher.SectionEight
