module
public import Stellmacher.SectionEight.EightSixSelectedOrbitV2Core
public import Theory.GroupAction.FixedCoatomDisplacement
public import Stellmacher.SectionThree.CentralCoatomInvolutionCard
public import Theory.GroupAction.CardTwoDisplacementInvolution

/-!
# The second selected orbit has residual quotient of order four

For the actual high-cost selection in Stellmacher (8.6), put
Y=[Qnext,O²(E)] and V2=⟨(Y intersect D)^E⟩. Then V2≤Qa and |Y:V2|=4.
The source-(12) telescope and high-cost branch are retained, together with
the already proved source-(7) actor index and source-(14) fact Y≰Qa.
These two prior facts are supplied by EightSixLargeIndexStructure.

The core-control module gives V2≤Qa, while the selected first orbit puts
Znext inside V2. Thus the literal quotient Y/V2 is elementary abelian.
Residual commutator idempotence gives full O²(E)-action on this quotient;
the odd residual image follows from the local (3.3) quotient by Qnext
and kernel-index divisibility. Coprime splitting makes the action fixed-free.
The actor subgroup fixes (Y intersect Qa)/V2, of index at most two, so a
coatom-complement actor has displacement of order at most two. Its image
is an involution (including the identity case). The central-coatom exact
square-cardinality theorem now bounds the quotient by four; Y≰Qa makes
it nontrivial and forces equality. All quotient and action instances are
kept literal, and no raw S3 action model is used.

Source: Stellmacher, Journal of Algebra 190 (1997), proof of (8.6), printed
p.44, paragraph after (16); refs/files/stellmacher-n-group.pdf.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SevenSix
open scoped commutatorElement IsMulCommutative
universe u

private theorem selected_subgroup_residual_action_odd
    {G X : Type u} [Group G] [Finite G] [Group X] [Finite X]
    {S P1 P2 : Subgroup G} (ctx : SectionEightLocalContext G S P1 P2)
    (E : Subgroup G) (hE : E ≤ GAt ctx.Γ ctx.criticalPath.firstStep)
    (f : E →* X)
    (hker : (QAt ctx.Γ ctx.criticalPath.firstStep).subgroupOf E ≤ f.ker) :
    Odd (Nat.card (((twoResidualIn E).subgroupOf E).map f)) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.firstStep
  let Q := QAt Γ cp.firstStep
  let B := twoResidualIn E
  let projection := QuotientGroup.mk' (pCore 2 P)
  let edgeSylow : Sylow 2 (P ⊓ GAt Γ cp.a : Subgroup G) := default
  let edge := sylowTwoAmbient (P ⊓ GAt Γ cp.a) edgeSylow
  have hdata := edge_sectionThree_data ctx.sectionSeven Γ
    ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj)) edgeSylow
  obtain ⟨prime,hprime,hodd,himage⟩ := SectionThree.pSet_residual_image_is_odd_pGroup
    edge hdata.1 P hdata.2.1 hdata.2.2.2.1 projection
      (by rw [QuotientGroup.ker_mk'])
  let _ : Fact prime.Prime := ⟨hprime⟩
  have hmono : B ≤ twoResidualIn P := eight_six_residual_mono E P hE
  have hnative : (twoResidualIn P).subgroupOf P = twoResidualSubgroup P :=
    Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
  have hle : (B.subgroupOf P).map projection ≤ (twoResidualSubgroup P).map projection := by
    rw [←hnative]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono P hmono)
  have hoddBase : Odd (Nat.card ((B.subgroupOf P).map projection)) := by
    obtain ⟨n,hn⟩ := (himage.to_le hle).exists_card_eq
    rw [hn]
    exact hodd.pow
  have hQnative : Q.subgroupOf P = pCore 2 P := by
    change (Γ.twoCoreAt cp.firstStep).subgroupOf P = _
    rw [Γ.twoCoreAt_def]
    change ((pCore 2 P).map P.subtype).subgroupOf P = _
    exact Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
  have hoddIndex : Odd (Q.relIndex B) := by
    rw [←Subgroup.relIndex_ker,QuotientGroup.ker_mk',←hQnative,
      Subgroup.relIndex_subgroupOf ((twoResidualIn_le E).trans hE)] at hoddBase
    exact hoddBase
  apply hoddIndex.of_dvd_nat
  rw [←Subgroup.relIndex_ker]
  have hdvd := Subgroup.relIndex_dvd_of_le_left (B.subgroupOf E) hker
  rw [Subgroup.relIndex_subgroupOf (twoResidualIn_le E)] at hdvd
  exact hdvd

public theorem eight_six_selected_orbit_v2_support
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
    (hhigh : ∀ mover : G, mover ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a →
      mover ∉ QAt ctx.Γ ctx.criticalPath.firstStep →
        8 ≤ eightSixCommutatorCost ctx.Γ ctx.criticalPath mover)
    (hlarge : 4 * Nat.card
      ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊓ D : Subgroup G) ≤
      Nat.card (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a : Subgroup G))
    (hYnot : ¬ ⁅QAt ctx.Γ ctx.criticalPath.firstStep,twoResidualIn E⁆ ≤
      QAt ctx.Γ ctx.criticalPath.a)
    :
    let Y := ⁅QAt ctx.Γ ctx.criticalPath.firstStep,twoResidualIn E⁆
    let V2 := conjugateClosure (Y ⊓ D) E
    V2 ≤ QAt ctx.Γ ctx.criticalPath.a ∧ QuotientCardEq Y V2 4 := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let V := VAt Γ cp.firstStep
  let R := QAt Γ cp.firstStep
  let Z := ZAt Γ cp.firstStep
  let U := conjugateClosure (ZAt Γ cp.a) E
  let B := twoResidualIn E
  let Y := ⁅R,B⁆
  let N := conjugateClosure (Y ⊓ D) E
  let A := VAt Γ previous ⊓ QAt Γ cp.a
  have hlen : cp.length = 2 := hlength
  have hAE : A ≤ E := geom.generated ▸ le_sup_left
  have hA0A : A0 ≤ A := geom.coatom_eq ▸ inf_le_left
  have hEV : E ≤ Subgroup.normalizer (V : Set G) :=
    geom.group_le.trans (stabilizer_le_normalizer_v Γ cp.firstStep)
  have hER : E ≤ Subgroup.normalizer (R : Set G) :=
    geom.group_le.trans (SevenSix.stabilizer_le_normalizer_q Γ cp.firstStep)
  have hBE : B ≤ E := SevenSix.twoResidualIn_le E
  have hEB : E ≤ Subgroup.normalizer (B : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBE).mp (SevenSix.twoResidualIn_normal E)
  have hEY : E ≤ Subgroup.normalizer (Y : Set G) := by
    intro e he
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    change (⁅R,B⁆).map (MulAut.conj e).toMonoidHom = ⁅R,B⁆
    rw [Subgroup.map_commutator]
    exact congrArg₂ (fun K J : Subgroup G => ⁅K,J⁆)
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hER he))
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hEB he))
  have hVR : V ≤ R := SevenSix.neighbor_join_le_core_of_length_gt_one Γ cp (by omega) _
  have hpacket := eight_six_selected_residual_decomposition ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL
  have hYV : Y ≤ V := hpacket.1.le.trans
    (Subgroup.le_normalizer_iff_commutator_le_left.mp (hBE.trans hEV))
  have hNY : N ≤ Y := eight_six_conjugate_closure_le _ _ _ inf_le_left hEY
  have hEN : E ≤ Subgroup.normalizer (N : Set G) := eight_six_conjugate_closure_normalizer _ _
  have hNcore : N ≤ QAt Γ cp.a := (eight_six_selected_orbit_v2_core ctx hcenter hquot
    hlength hcard previous D L Q hprev data E A0 actor geom hcore hedge hD hL hhigh hlarge).2
  refine ⟨hNcore,?_⟩
  have hseed : ZAt Γ cp.a ≤ U := by
    intro z hz
    exact Subgroup.subset_closure ⟨(1:E),⟨z,hz⟩,by simp⟩
  have hUY : U ≤ Y := eight_six_selected_orbit_le_residual_commutator ctx hcenter hquot
    hlength hcard previous D L Q hprev data E A0 actor geom hcore hedge hD hL
  have hUD : U ≤ D := eight_six_selected_orbit_le_intersection ctx hcenter hquot
    hlength hcard previous D L Q hprev data E A0 actor geom hcore hedge hD hL hhigh
  have hseedN : Y ⊓ D ≤ N := by
    intro z hz
    exact Subgroup.subset_closure ⟨(1:E),⟨z,hz⟩,by simp⟩
  have hZN : Z ≤ N := (eight_six_first_step_fixed_line_local ctx hcenter hcard).2.trans
    (hseed.trans ((le_inf hUY hUD).trans hseedN))
  have hYR : ⁅Y,R⁆ ≤ N := ((Subgroup.commutator_mono hYV le_rfl).trans_eq
    data.first_commutator).trans hZN
  have hN : (N.subgroupOf Y).Normal := Subgroup.normal_subgroupOf_of_le_normalizer
    (Subgroup.le_normalizer_iff_commutator_le_left.mpr
      ((Subgroup.commutator_mono hNY (hYV.trans hVR)).trans hYR))
  let _ := hN
  obtain ⟨hNZ,hWZ,_⟩ := eight_six_next_quotient_module_data_local
    ctx hcenter hlength hcard data.first_commutator
  let _ := hNZ
  let _ := hWZ
  have hderived : _root_.commutator Y ≤ N.subgroupOf Y := by
    intro y hy
    apply (Subgroup.commutator_mono le_rfl (hYV.trans hVR)).trans hYR
    have hm : (_root_.commutator Y).map Y.subtype = ⁅Y,Y⁆ := by
      rw [_root_.commutator_def,Subgroup.map_commutator,←MonoidHom.range_eq_map,Subgroup.range_subtype]
    exact hm ▸ Subgroup.mem_map_of_mem Y.subtype hy
  let W := Y ⧸ N.subgroupOf Y
  let q := QuotientGroup.mk' (N.subgroupOf Y)
  have hW : IsElementaryAbelian 2 W := {
    toIsMulCommutative := (Subgroup.Normal.quotient_commutative_iff_commutator_le
      (N := N.subgroupOf Y)).mpr hderived
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
      intro w
      obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf Y) w
      rw [←map_pow]
      apply (QuotientGroup.eq_one_iff _).mpr
      apply hZN
      let v : V := ⟨y,hYV y.property⟩
      have hp : (QuotientGroup.mk' (Z.subgroupOf V) v)^2 = 1 :=
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 (V ⧸ Z.subgroupOf V)) _
      rw [←map_pow] at hp
      exact (QuotientGroup.eq_one_iff (v^2)).mp hp) }
  let _ := hW
  have hRp : IsPGroup 2 R := by
    change IsPGroup 2 (Γ.twoCoreAt _)
    rw [Γ.twoCoreAt_def]
    exact (pCore_isPGroup (p := 2)).map _
  have hfull : ⁅Y,B⁆ = Y := commutator_twoResidualAmbient_idempotent R E hRp hER
  obtain ⟨action,haction,hkernel,hfullAction⟩ :=
    Subgroup.exists_quotient_conjugation_full_action E Y N B R hEY hEN hN hBE hfull hYR
  change commutatorAction ((B.subgroupOf E).map action) W = ⊤ at hfullAction
  let J := (B.subgroupOf E).map action
  have hodd : Odd (Nat.card J) := selected_subgroup_residual_action_odd ctx E geom.group_le action hkernel
  have hcop : Nat.Coprime (Nat.card J) (Nat.card W) := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 W).exists_card_eq
    rw [hn]
    exact hodd.coprime_two_right.pow_right n
  have hcompl : IsCompl (FixedPoints.subgroup J W) (commutatorAction J W) :=
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (inferInstance : Group.IsSolvable W) hcop inferInstance
  have hRmap : (twoResidualAmbient (⊤ : Subgroup E)).map E.subtype = B :=
    map_twoResidualAmbient_of_subgroup_image ⊤ E.subtype E (by
      rw [←MonoidHom.range_eq_map,Subgroup.range_subtype])
  have hRint : B.subgroupOf E = twoResidualAmbient (⊤ : Subgroup E) := by
    apply Subgroup.map_injective E.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hBE,hRmap]
  have hfixed : FixedPoints.subgroup ((twoResidualAmbient (⊤ : Subgroup E)).map action) W = ⊥ := by
    rw [←hRint]
    have hh := hcompl.inf_eq_bot
    change FixedPoints.subgroup ((B.subgroupOf E).map action) W ⊓
      commutatorAction ((B.subgroupOf E).map action) W = ⊥ at hh
    simpa only [hfullAction,inf_top_eq] using hh
  have hcoatom : A0.relIndex A = 2 := by
    have hh := (A0.subgroupOf A).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA0A).toEquiv] at hh
    change A0.relIndex A * Nat.card A0 = Nat.card A at hh
    have hcount : Nat.card A = 2 * Nat.card A0 := geom.coatom_card
    have hp : 0 < Nat.card A0 := Nat.card_pos
    nlinarith
  have hproper : ¬ A ≤ A0 := by
    intro hh
    have heq := le_antisymm hh hA0A
    rw [heq,Subgroup.relIndex_self] at hcoatom
    omega
  obtain ⟨mover,hmover,hmover0⟩ := SetLike.not_le_iff_exists.mp hproper
  let a : E := ⟨mover,hAE hmover⟩
  let x : E := ⟨geom.x,hBE geom.residual_mem⟩
  let Ai := A.subgroupOf E
  let A0i := A0.subgroupOf E
  have hA0E : A0 ≤ E := hA0A.trans hAE
  have hAsp : A = Subgroup.zpowers mover ⊔ A0 := by
    apply le_antisymm ?_ (sup_le (Subgroup.zpowers_le.mpr hmover) hA0A)
    intro g hg
    by_cases hg0 : g ∈ A0
    · exact Subgroup.mem_sup_right hg0
    have hk : mover⁻¹ * g ∈ A0 := by
      have hh := (A0.subgroupOf A).mul_mem_iff_of_index_two hcoatom
        (a := ⟨mover⁻¹,A.inv_mem hmover⟩) (b := ⟨g,hg⟩)
      exact hh.mpr (by simp only [Subgroup.mem_subgroupOf,Subgroup.inv_mem_iff,hmover0,hg0])
    have hm := (Subgroup.zpowers mover ⊔ A0).mul_mem
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers mover)) (Subgroup.mem_sup_right hk)
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
  have hcentral : A0i.map action ≤ Subgroup.centralizer (action.range : Set _) := by
    rintro point ⟨b,hb,rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro image ⟨e,rfl⟩
    have hk : ⁅e,b⁆ ∈ action.ker := hkernel
      (geom.coatom_commutator (Subgroup.commutator_mem_commutator e.property hb))
    have hone : ⁅action e,action b⁆ = 1 := by
      rw [←map_commutatorElement]
      exact MonoidHom.mem_ker.mp hk
    exact commutatorElement_eq_one_iff_mul_comm.mp hone
  let K := Y ⊓ QAt Γ cp.a
  have hKcomm : ⁅K,A⁆ ≤ N := by
    apply le_trans (le_inf ?_ ?_) hseedN
    · exact (Subgroup.commutator_mono inf_le_left le_rfl).trans
        (Subgroup.le_normalizer_iff_commutator_le_left.mp (hAE.trans hEY))
    · rw [hD]
      apply le_inf ?_ ?_
      · exact (Subgroup.commutator_mono le_rfl
          (inf_le_left.trans (SevenSix.neighbor_join_le_core_of_length_gt_one Γ cp (by omega) previous))).trans
          (Subgroup.le_normalizer_iff_commutator_le_right.mp
            (inf_le_right.trans ((((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core
              cp.a previous hprev.1 default).2.2).trans
                (SevenSix.stabilizer_le_normalizer_q Γ previous))))
      · exact ((Subgroup.commutator_mono inf_le_left le_rfl).trans
          (Subgroup.le_normalizer_iff_commutator_le_left.mp (hAE.trans hEY))).trans (hYV.trans hVR)
  have hindex : K.relIndex Y ∣ 2 :=
    eight_six_two_subgroup_core_part_index_dvd_two _ _ Y
      ((hYV.trans hVR).trans (((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core
        cp.firstStep cp.a ((SevenSix.mem_neighborhood_iff_adjacent Γ).mpr
          (Γ.adjacent_symm cp.firstStep_adj)) default).2.2))
      (hRp.to_le (hYV.trans hVR)) hquot
  have hrankBound := Subgroup.quotient_commutator_card_le_two_of_fixed_coatom E Y N K
    hNY hEY hN hW action haction a inf_le_left hindex
    ((Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hmover)).trans hKcomm)
  have hcyclic : (Subgroup.zpowers mover).subgroupOf E = Subgroup.zpowers a := by
    apply Subgroup.map_injective E.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le (Subgroup.zpowers_le.mpr (hAE hmover)),MonoidHom.map_zpowers]
    rfl
  have hHY : ⁅Y,Subgroup.zpowers mover⁆ ≤ Y :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((Subgroup.zpowers_le.mpr (hAE hmover)).trans hEY)
  have hrel := Subgroup.relIndex_sup_right
    ((⁅Y,Subgroup.zpowers mover⁆).subgroupOf Y) (N.subgroupOf Y)
  rw [←Subgroup.subgroupOf_sup hHY hNY,
    Subgroup.relIndex_subgroupOf (sup_le hHY hNY),Subgroup.relIndex_subgroupOf hHY] at hrel
  have hrank : Nat.card (commutatorAction (Subgroup.zpowers (action a)) W) ≤ 2 := by
    have hh := Subgroup.quotient_conjugation_commutatorAction_card E Y N
      (Subgroup.zpowers mover) hEY (Subgroup.zpowers_le.mpr (hAE hmover)) hN action haction
    rw [hcyclic,MonoidHom.map_zpowers] at hh
    rw [hh,←hrel]
    exact hrankBound
  have hsquare : (action a)^2=1 := by
    by_cases htwo : Nat.card (commutatorAction (Subgroup.zpowers (action a)) W)=2
    · exact (isInvolution_of_card_two_displacement (action a) htwo).2
    have hbot : commutatorAction (Subgroup.zpowers (action a)) W = ⊥ :=
      Subgroup.card_eq_one.mp (by have hp : 0 < Nat.card (commutatorAction (Subgroup.zpowers (action a)) W) := Nat.card_pos; omega)
    have heq : action a = 1 := by
      ext w
      have hm : w⁻¹ * action a w ∈ commutatorAction (Subgroup.zpowers (action a)) W :=
        Subgroup.subset_closure ⟨⟨action a,Subgroup.mem_zpowers (action a)⟩,w,Subgroup.mem_top w,rfl⟩
      rw [hbot] at hm
      exact (inv_mul_eq_one.mp hm).symm
    rw [heq,one_pow]
  have hcardW := SectionThree.central_coatom_involution_module_card_eq_square
    action Ai A0i a x hgen hAi hA0two hcentral hfixed hsquare
  change Nat.card W = Nat.card (commutatorAction (Subgroup.zpowers (action a)) W)^2 at hcardW
  have hWbig : 1 < Nat.card W := by
    have hneq : N ≠ Y := by
      intro h
      apply hYnot
      exact h.ge.trans hNcore
    have hproperN : N.subgroupOf Y ≠ ⊤ := by
      intro ht
      have hh := congrArg (fun K : Subgroup Y => K.map Y.subtype) ht
      rw [Subgroup.map_subgroupOf_eq_of_le hNY,←MonoidHom.range_eq_map,Subgroup.range_subtype] at hh
      exact hneq hh
    have hp : 0 < Nat.card W := Nat.card_pos
    have hn : Nat.card W ≠ 1 := fun hh => hproperN (Subgroup.index_eq_one.mp hh)
    omega
  have hfour : Nat.card W = 4 := by
    have hp : 0 < Nat.card (commutatorAction (Subgroup.zpowers (action a)) W) := Nat.card_pos
    have hr : Nat.card (commutatorAction (Subgroup.zpowers (action a)) W) = 2 := by
      by_contra hn
      have hh : Nat.card (commutatorAction (Subgroup.zpowers (action a)) W) = 1 := by omega
      rw [hh] at hcardW
      norm_num at hcardW
      omega
    simpa only [hr, show (2:ℕ)^2=4 from rfl] using hcardW
  have hcount := (N.subgroupOf Y).index_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNY).toEquiv] at hcount
  change Nat.card W * Nat.card N = Nat.card Y at hcount
  change Nat.card Y = 4 * Nat.card N
  rw [←hcount,hfour]

end Stellmacher.SectionEight
