module
public import Stellmacher.SectionEight.EightSixSelectedOrbitResidual
public import Stellmacher.SectionEight.EightSixResidualFixedDecomposition
public import Stellmacher.ResidualCommutatorIdempotence
public import Theory.GroupTheory.NormalizedSupCard
/-!
The actual selected residual commutator Y=[Qnext,O²(E)] equals [Vnext,O²(E)],
meets its fixed subgroup C=Vnext intersect C_G(O²(E)) in precisely Znext,
and joins C to all of Vnext. The full source-(12) geometric telescope is
retained; no cost branch or raw orbit-action model is required.

Source (8) puts Y inside Vnext. Residual commutator idempotence then
identifies it with [Vnext,O²(E)]. On the literal elementary quotient by
Znext, the odd residual image gives complementary fixed and commutator
subgroups. Their intersection lifts to Znext because the actual selected
orbit already contains Znext and lies in Y. The proved fixed decomposition
lifts their join. The companion records the resulting normalized-product
cardinality identity, with the center line of order two. This supplies the support cardinality transfers in both
remaining branches of Stellmacher (8.6), printed pp.43–45.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u
public theorem eight_six_selected_residual_decomposition
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
    (hL : L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a)) :
    let V := VAt ctx.Γ ctx.criticalPath.firstStep
    let Z := ZAt ctx.Γ ctx.criticalPath.firstStep
    let B := twoResidualIn E
    let Y := ⁅QAt ctx.Γ ctx.criticalPath.firstStep,B⁆
    let C := V ⊓ Subgroup.centralizer (B : Set G)
    Y = ⁅V,B⁆ ∧ Y ⊓ C = Z ∧ V = Y ⊔ C := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let A := VAt Γ previous ⊓ QAt Γ cp.a
  let U := conjugateClosure (ZAt Γ cp.a) E
  let Z := ZAt Γ cp.firstStep
  let V := VAt Γ cp.firstStep
  let P := GAt Γ cp.firstStep
  let R := QAt Γ cp.firstStep
  let B := twoResidualIn E
  let Y := ⁅R,B⁆
  have hBE : B ≤ E := SevenSix.twoResidualIn_le E
  have hAE : A ≤ E := geom.generated ▸ le_sup_left
  have hENR : E ≤ Subgroup.normalizer (R : Set G) :=
    geom.group_le.trans (SevenSix.stabilizer_le_normalizer_q Γ _)
  have hVR : V ≤ R := SevenSix.neighbor_join_le_core_of_length_gt_one Γ cp
    (by exact hlength ▸ by decide) _
  have hnot : ¬ A ≤ R := by
    intro hAR
    have hRG : R ≤ GAt Γ (Γ.act geom.x⁻¹ cp.a) :=
      ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core cp.firstStep _
        geom.neighbor default).2.2
    have hA0 : A0 = A := geom.coatom_eq.trans (inf_eq_left.mpr (hAR.trans hRG))
    have hcoatom := geom.coatom_card
    rw [hA0] at hcoatom
    have hpos : 0 < Nat.card A := Nat.card_pos
    change Nat.card A = 2 * Nat.card A at hcoatom
    omega
  have hBP : B ≤ EAt Γ cp.firstStep := by
    have hs := (SevenSix.edge_sylow_data ctx.sectionSeven Γ cp).2
    have hgen : twoResidualIn P ⊔ S = P := SevenSix.twoResidualIn_sup_sylow hs
    have hnorm : ((twoResidualIn P).subgroupOf (twoResidualIn P ⊔ S)).Normal := by
      rw [hgen]
      exact SevenSix.twoResidualIn_normal P
    have hp : IsPGroup 2 S := by
      obtain ⟨_,s,hs⟩ := hs
      exact hs ▸ s.isPGroup'.map P.subtype
    change B ≤ Γ.twoResidualAt cp.firstStep
    rw [Γ.twoResidualAt_def]
    exact SectionThree.twoResidualAmbient_le_left_of_le_sup (twoResidualIn P) S E
      hnorm hp (geom.group_le.trans_eq hgen.symm)
  have hYV : Y ≤ V := (Subgroup.commutator_mono le_rfl hBP).trans
    (eight_six_next_residual_core_commutator_le_v ctx hcenter hlength previous D L Q
      hprev.1 hD hL data hnot)
  let C := V ⊓ Subgroup.centralizer (B : Set G)
  have hRtwo : IsPGroup 2 R := by
    change IsPGroup 2 (Γ.twoCoreAt _)
    rw [Γ.twoCoreAt_def]
    exact (pCore_isPGroup (p := 2)).map _
  have hidem : ⁅Y,B⁆ = Y := commutator_twoResidualAmbient_idempotent R E hRtwo hENR
  have hYcomm : Y = ⁅V,B⁆ := le_antisymm
    ((hidem.symm.le.trans (Subgroup.commutator_mono hYV le_rfl)))
    (Subgroup.commutator_mono hVR le_rfl)
  have hZY : Z ≤ Y := by
    have hseed : ZAt Γ cp.a ≤ U := by
      intro z hz
      exact Subgroup.subset_closure ⟨(1:E),⟨z,hz⟩,by simp⟩
    exact (eight_six_first_step_fixed_line_local ctx hcenter hcard).2.trans
      (hseed.trans (eight_six_selected_orbit_le_residual_commutator ctx hcenter hquot
        hlength hcard previous D L Q hprev data E A0 actor geom hcore hedge hD hL))
  have hZV : Z ≤ V := hZY.trans hYV
  have hBP' : B ≤ P := hBE.trans geom.group_le
  have hZC : Z ≤ C := le_inf hZV
    ((hcenter.trans (SevenSix.centerAmbient_le_centralizer _)).trans
      (Subgroup.centralizer_le hBP'))
  obtain ⟨hN,hW,action,hformula,hkernel,_⟩ := eight_six_next_quotient_module_data_local
    ctx hcenter hlength hcard data.first_commutator
  let _ := hN
  let _ := hW
  let W := V ⧸ Z.subgroupOf V
  let projection := QuotientGroup.mk' (Z.subgroupOf V)
  let Bbar := (B.subgroupOf P).map action.rangeRestrict
  have hpacket := eight_six_residual_fixed_decomposition ctx hcenter hlength hcard
    E geom.group_le hN hW action hformula hkernel
  have hfixedImage : (C.subgroupOf V).map projection = FixedPoints.subgroup Bbar W :=
    hpacket.2.1
  have hactorImage : Bbar.map action.range.subtype = (B.subgroupOf P).map action := by
    rw [Subgroup.map_map]
    rfl
  have hYImage : (Y.subgroupOf V).map projection = commutatorAction Bbar W := by
    rw [hYcomm,←commutatorAction_map_actor_subtype action.range Bbar,hactorImage]
    exact (Subgroup.quotient_conjugation_commutatorAction_eq_image P V Z B
      (stabilizer_le_normalizer_v Γ cp.firstStep) hBP' hN action hformula).symm
  have hinter : Y ⊓ C = Z := by
    apply le_antisymm ?_ (le_inf hZY hZC)
    intro y hy
    let v : V := ⟨y,hYV hy.1⟩
    have hfix : projection v ∈ FixedPoints.subgroup Bbar W := by
      rw [←hfixedImage]
      exact Subgroup.mem_map_of_mem projection hy.2
    have hcomm : projection v ∈ commutatorAction Bbar W := by
      rw [←hYImage]
      exact Subgroup.mem_map_of_mem projection hy.1
    have hone : projection v = 1 := Subgroup.mem_bot.mp
      (hpacket.2.2.1.inf_eq_bot ▸ (show projection v ∈
        FixedPoints.subgroup Bbar W ⊓ commutatorAction Bbar W from ⟨hfix,hcomm⟩))
    exact (QuotientGroup.eq_one_iff (N := Z.subgroupOf V) v).mp hone
  refine ⟨hYcomm,hinter,?_⟩
  change V = Y ⊔ C
  rw [hYcomm]
  exact hpacket.2.2.2

public theorem eight_six_selected_residual_card_mul_fixed
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
    (hL : L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a)) :
    Nat.card (⁅QAt ctx.Γ ctx.criticalPath.firstStep,twoResidualIn E⁆ : Subgroup G) *
      Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep ⊓
        Subgroup.centralizer (twoResidualIn E : Set G) : Subgroup G) =
      2 * Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) := by
  let V := VAt ctx.Γ ctx.criticalPath.firstStep
  let R := QAt ctx.Γ ctx.criticalPath.firstStep
  let B := twoResidualIn E
  let Y := ⁅R,B⁆
  let C := V ⊓ Subgroup.centralizer (B : Set G)
  have hpacket := eight_six_selected_residual_decomposition ctx hcenter hquot hlength
    hcard previous D L Q hprev data E A0 actor geom hcore hedge hD hL
  have hVR : V ≤ R := SevenSix.neighbor_join_le_core_of_length_gt_one
    ctx.Γ ctx.criticalPath (by omega) _
  have hCY : C ≤ Subgroup.normalizer (Y : Set G) :=
    (inf_le_left.trans hVR).trans (Subgroup.normalizer_commutator_ge_left R B)
  have hc := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes Y C hCY
  have hi : Y ⊓ C = ZAt ctx.Γ ctx.criticalPath.firstStep := hpacket.2.1
  have hs : V = Y ⊔ C := hpacket.2.2
  rw [hi,←hs,(eight_six_first_step_fixed_line_local ctx hcenter hcard).1] at hc
  exact hc

end Stellmacher.SectionEight
