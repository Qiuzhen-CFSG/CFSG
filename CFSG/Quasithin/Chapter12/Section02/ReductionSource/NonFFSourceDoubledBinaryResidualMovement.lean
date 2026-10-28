module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryNaturalFour
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryResidualMovement
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.CoverRecovery
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.KernelEquality
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.ActorComparison

/-!
# Residual containment and component normality on the chosen doubled orbit

Retain the same escaping H, lifted C-component C, paired plane and original
Sylow R. The rank-one exclusions imply that Q is not Sylow in CQ.
A.4.2 identifies C_R(L₀/O₂(L₀)) with Q, so the component Sylow moves
that section. The literal quotient q : H → H/C_H(Y) retains this movement:
the paired-plane S₃ action identifies O₂((L₀R)^q) with Q^q, using W ≤ Y
and C_T(W)=Q to bound the Sylow part of the full kernel.

The binary SL₃ covering theorem identifies C_L(V)=O₂(L). Restricting to
the original plane centralizer gives |L₀/O₂(L₀)|=3. The residual normalizes
C, so its intersection with C is normal and, by movement, not in O₂(L₀).
Two-perfectness gives L₀ ≤ C. Minimality now gives H=CR. The noncentral
residual image prevents R from exchanging component images; normality of
the image lifts to the original C without a solvability assumption on
the full action kernel.

This proves 7.7.9(2) and all clauses of 7.7.10 with the actual original
maps. W and the selected seed remain distinct, as do the reduced-action
quotient and the C.2.7 star quotient. Remaining constrained-component rows,
ambient paired-plane containment and the original non-FF endgame remain
with qt-d-1222-nonff-doubled.
Source: Aschbacher–Smith, printed p.708, refs/quasithin.pdf.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Stellmacher Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource ChapterE BinaryLinearThree
open DoubledBinaryPlanes DoubledBinaryLocalCore DoubledBinaryOmega
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- Original 7.7.9(2) and 7.7.10: the original residual lies in the
escaping component, which is normal and supplements the original Sylow.
The reduced-action quotient and C.2.7 markings are retained. -/
theorem sourceOrbit_binary_pairedPlane_residual_contained
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3))) :
    ∃ t : G, t ∈ (T : Subgroup G) ∧ t ∉ normalizer (V : Set G) ∧
      ∃ E : Additive D.sourceOrbit ≃ₗ[ZMod 2] NaturalDual.Space,
        (∀ w, (E w).2 = 0 ↔ (w.toMul : G) ∈ V) ∧
        (∀ w, (E w).1 = 0 ↔ (w.toMul : G) ∈ V.map (MulAut.conj t).toMonoidHom) ∧
        ∃ v : Vector, ∃ f : Module.Dual (ZMod 2) Vector, f v = 1 ∧
          HasMarking D.sourceOrbit L E ∧
          let U := ambientPlane D.sourceOrbit E v f
          let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
          localBase L (T : Subgroup G) U =
            (L ⊔ (T : Subgroup G)) ⊓ centralizer (U : Set G) ∧
          (localBase L (T : Subgroup G) U).pCoreIn 2 = Q ∧
          (¬ centralizer (U : Set G) ≤ normalizer (L : Set G) →
            ∃ H : Subgroup G,
              H ∈ Chapter3.HStar (localBase L (T : Subgroup G) U) (normalizer (L : Set G)) ∧
              H ≤ centralizer (U : Set G) ∧
              let Y := conjugateSpanBy
                (omegaOneCenterAmbient ((T : Subgroup G) ⊓ centralizer (U : Set G))) H
              D.sourceOrbit ≤ Y ∧ ∃ hred : IsPReduced 2 (Y.subgroupOf H),
              let := hred.normal
              let q := ChapterB.InternalThompsonAction.actionMk (Y.subgroupOf H)
              ∃ C : Subgroup H, C.IsCComponent ∧
                IsComponent (ChapterB.InternalThompsonAction.ActionQuotient (Y.subgroupOf H))
                  (C.map (ChapterB.InternalThompsonAction.actionMk (Y.subgroupOf H))) ∧
                ¬ C.map H.subtype ≤ normalizer (L : Set G) ∧
                (localResidual L U).subgroupOf H ≤ normalizer (C : Set H) ∧
                (∃ P : Sylow 2 H, (P : Subgroup H).map H.subtype =
                  (T : Subgroup G) ⊓ centralizer (U : Set G)) ∧
                let C₀ := C.map H.subtype
                let M₀ := H ⊓ normalizer (L : Set G)
                Input KnownSimple.IsKnownSimple H Q M₀ C₀ ∧
                ¬ ChapterC.IsAlternatingBlock C₀ 5 ∧
                ¬ Chapter1.IsSylowIn 2 Q (C₀ ⊔ Q) ∧
                (localResidual L U).subgroupOf H ≤ C ∧ C.Normal ∧
                H = C₀ ⊔ ((T : Subgroup G) ⊓ centralizer (U : Set G)) ∧
                (((localBase L (T : Subgroup G) U).subgroupOf H).map q).pCoreIn 2 =
                  (Q.subgroupOf H).map q ∧
                ¬ ⁅((localResidual L U).subgroupOf H).map q,
                  (((T : Subgroup G) ⊓ centralizer (U : Set G)).subgroupOf H).map q ⊓ C.map q⁆ ≤
                    (((localResidual L U).subgroupOf H).map q).pCoreIn 2 ∧
                ¬ Nonempty (starImage C₀ Q C₀ ≃* alternatingGroup (Fin 5)) ∧
                KernelConclusion C₀ Q ∧ OffenderConclusion C₀ Q ∧
                (starImage C₀ Q C₀ ⊓ normalizer
                  (starImage C₀ Q (elementaryAbelianMaxJ Q) : Set (StarQuotient C₀ Q)) ≤
                    starM C₀ Q M₀) ∧
                starM C₀ Q M₀ < starImage C₀ Q C₀ ∧
                let ρ := starRepresentation C₀ Q
                let J := offenderSubgroup ρ
                starImage C₀ Q C₀ ≤ J ∧
                Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
                  (ρ.comp J.subtype) ((starImage C₀ Q C₀).subgroupOf J))) := by
  obtain ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hmark,hbase,hcore,hescape⟩ :=
    D.sourceOrbit_binary_pairedPlane_original_component h hd hnon F hF hmodel
  refine ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hmark,hbase,hcore,?_⟩
  dsimp only
  intro hout
  obtain ⟨H,hH,hHC,hWY,hred,C,hC,hCimage,hCM,hLC,⟨P,hP⟩,
    hi,hno,hnotSylow,hfive,hk,ho,hm,hs,hrest⟩ := hescape hout
  let := hred.normal
  let U := ambientPlane D.sourceOrbit E v f
  let B := localBase L (T : Subgroup G) U
  let R := (T : Subgroup G) ⊓ centralizer (U : Set G)
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let Y := conjugateSpanBy (omegaOneCenterAmbient R) H
  let A := (localResidual L U).subgroupOf H
  let QH := Q.subgroupOf H
  let q := ChapterB.InternalThompsonAction.actionMk (Y.subgroupOf H)
  change B = (L ⊔ (T : Subgroup G)) ⊓ centralizer (U : Set G) at hbase
  have hBH : B ≤ H := hH.1.1.2
  have hRH : R ≤ H := le_sup_right.trans hBH
  have hAH : localResidual L U ≤ H := le_sup_left.trans hBH
  have hQH : Q ≤ H := hi.setup.radical_le
  have hYH : Y ≤ H := conjugateSpanBy_le_self (by
    intro z hz
    exact hRH ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1)
  have hWH : D.sourceOrbit ≤ H := hWY.trans hYH
  have hB0 : A ⊔ (P : Subgroup H) = B.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hAH,hP,map_subgroupOf_eq_of_le hBH]
    rfl
  have hcore0 : (A ⊔ (P : Subgroup H)).pCoreIn 2 = QH := by
    apply map_injective H.subtype_injective
    rw [map_pCoreIn_of_injective 2 _ H.subtype H.subtype_injective,
      Subgroup.map_sup,map_subgroupOf_eq_of_le hAH,hP,map_subgroupOf_eq_of_le hQH]
    exact hcore
  have hPA : (P : Subgroup H) ≤ normalizer (A : Set H) := by
    have hn : (H ⊓ normalizer (L : Set G)).subgroupOf H ≤ normalizer (A : Set H) :=
      (comap_mono (DoubledBinaryPushingUp.localResidual_normalizes L U H hHC)).trans
        (le_normalizer_comap H.subtype)
    apply le_trans ?_ hn
    intro p hp
    exact ⟨p.property,D.sylow_normalizes_component ((hP ▸ mem_map_of_mem H.subtype hp).1)⟩
  have hA : IsPPerfect 2 A := (isPPerfect_embedded_pResidual 2
    (L ⊓ centralizer (U : Set G))).of_surjective
      (subgroupOfEquivOfLe hAH).symm.toMonoidHom (subgroupOfEquivOfLe hAH).symm.surjective
  have hQP : QH ≤ (P : Subgroup H) := by
    rw [←hcore0]
    have hh := pCoreIn_le_sylow _ (P.subtype
      (show (P : Subgroup H) ≤ A ⊔ (P : Subgroup H) from le_sup_right))
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le
      (show (P : Subgroup H) ≤ A ⊔ (P : Subgroup H) from le_sup_right)] using hh
  have hQC : QH ≤ normalizer (C : Set H) := by
    have hh := comap_mono (f := H.subtype) hi.normalizes
    change QH ≤ (normalizer (C.map H.subtype : Set G)).subgroupOf H at hh
    have heC : (C.map H.subtype).subgroupOf H = C :=
      comap_map_eq_self_of_injective H.subtype_injective C
    rwa [subgroupOf_normalizer_eq (map_subtype_le C),heC] at hh
  have hnot : ¬ Chapter1.IsSylowIn 2 QH (C ⊔ QH) := by
    intro hh
    apply hnotSylow
    have hm := (Chapter1.IsSylowIn.map_iff H.subtype H.subtype_injective).mpr hh
    rwa [Subgroup.map_sup,map_subgroupOf_eq_of_le hQH] at hm
  have hmove0 := DoubledBinaryResidualMovement.component_sylow_moves_residual
    P A C QH hA hPA hcore0 hC.subnormal hi.setup.radical.isPGroup hQC hnot
  have hnotPC := DoubledBinaryResidualMovement.component_sylow_not_le_core
    P C QH hC.subnormal hi.setup.radical.isPGroup hQC hnot
  have hQeq : (T : Subgroup G) ⊓ centralizer (D.sourceOrbit : Set G) = Q := by
    simpa only [D.sourceOrbit_eq] using D.doubledOrbit_sylow_centralizer h
  have hPker : (P : Subgroup H) ⊓ q.ker ≤ QH := by
    intro p hp
    have ht := (hP ▸ mem_map_of_mem H.subtype hp.1).1
    have hc : (p : G) ∈ centralizer (D.sourceOrbit : Set G) := by
      have hh : p ∈ centralizer (Y.subgroupOf H : Set H) :=
        (QuotientGroup.eq_one_iff p).mp hp.2
      intro w hw
      exact congrArg Subtype.val (hh ⟨w,hWH hw⟩ (hWY hw))
    change (p : G) ∈ Q
    rw [←hQeq]
    exact ⟨ht,hc⟩
  obtain ⟨hLN,k,hks,a,hE,ha,hcov⟩ := hmark
  obtain ⟨m⟩ := hmodel
  let model := m.groupEquiv.trans (ExtensionConsequences.degreeOneNaturalEquiv F hF 3).groupEquiv
  have hseed : (centralizer (V : Set G)).subgroupOf L = pCore 2 L :=
    D.seedComparison.centralizer_eq_twoCore
      (D.seedComparison.projection_injective_of_linearThree h.quasisimple model)
  have hVW : V ≤ D.sourceOrbit := by
    rw [D.sourceOrbit_eq]
    exact le_componentOrbit V (T : Subgroup G)
  let J0 := L ⊓ centralizer (U : Set G)
  obtain ⟨πL,hπL,hkL⟩ := DoubledBinaryResidualMovement.localBase_quotient
    D.sourceOrbit L J0 hLN k hks E hE a ha hcov v f hfv (inf_le_left.trans hLN) inf_le_right le_rfl
  let j : J0 →* L := inclusion inf_le_left
  have hj : Function.Injective j := inclusion_injective inf_le_left
  have hkernel : IsPGroup 2 πL.ker := by
    apply (pCore_isPGroup.comap_of_injective j hj).to_le
    intro x hx
    rw [hkL] at hx
    change j x ∈ pCore 2 L
    rw [←hseed]
    exact centralizer_le hVW hx
  have hcJ := DoubledBinaryResidualMovement.residual_cubic_quotient πL hπL hkernel
  let eA : pResidual 2 J0 ≃* A :=
    ((pResidual 2 J0).equivMapOfInjective J0.subtype J0.subtype_injective).trans
      (subgroupOfEquivOfLe hAH).symm
  have hcA : Nat.card (A ⧸ pCore 2 A) = 3 :=
    (Nat.card_congr (QuotientGroup.congr _ _ eA (pCore_map_iso 2 eA)).toEquiv).symm.trans hcJ
  have hAC : A ≤ C := DoubledBinaryResidualMovement.residual_le_component_of_cubic_quotient
    A C ((P : Subgroup H) ⊓ C) hA hLC (inf_le_left.trans hPA) inf_le_right hcA hmove0
  have hBN : B ≤ normalizer (D.sourceOrbit : Set G) := by
    rw [hbase]
    exact inf_le_left.trans (sup_le hLN D.sourceOrbit_weakClosure_setup.normalizes)
  have hBC : B ≤ centralizer (U : Set G) := by rw [hbase]; exact inf_le_right
  have hLB : L ⊓ centralizer (U : Set G) ≤ B := by
    rw [hbase]
    exact inf_le_inf_right _ le_sup_left
  obtain ⟨πB,hπB,hkerB⟩ := DoubledBinaryResidualMovement.localBase_quotient
    D.sourceOrbit L B hLN k hks E hE a ha hcov v f hfv hBN hBC hLB
  let eB : (A ⊔ (P : Subgroup H) : Subgroup H) ≃* B :=
    (MulEquiv.subgroupCongr hB0).trans (subgroupOfEquivOfLe hBH)
  let π := πB.comp eB.toMonoidHom
  have hπ : Function.Surjective π := hπB.comp eB.surjective
  have hπP : ∀ p (hp : p ∈ (P : Subgroup H)), π ⟨p,mem_sup_right hp⟩ = 1 → p ∈ QH := by
    intro p hp hz
    have he : eB ⟨p,mem_sup_right hp⟩ ∈ πB.ker := hz
    rw [hkerB] at he
    change (p : G) ∈ Q
    rw [←hQeq]
    exact ⟨(hP ▸ mem_map_of_mem H.subtype hp).1,he⟩
  have hfactor : q.ker.subgroupOf (A ⊔ (P : Subgroup H)) ≤ π.ker := by
    intro x hx
    have hc : (x : H) ∈ centralizer (Y.subgroupOf H : Set H) :=
      (QuotientGroup.eq_one_iff (x : H)).mp hx
    change eB x ∈ πB.ker
    rw [hkerB]
    intro w hw
    exact congrArg Subtype.val (hc ⟨w,hWH hw⟩ (hWY hw))
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hcoreImage := DoubledBinaryResidualMovement.local_core_image P A QH hcore0 π hπ
    (DoubledBinaryPlaneQuotient.twoCore_eq_bot_of_symmetricThree ⟨MulEquiv.refl _⟩)
    hπP q hq hfactor
  have hmove := DoubledBinaryResidualMovement.component_sylow_moves_quotient
    P A C QH hA hPA hQP hnotPC q hq hPker hcoreImage
  have hACamb : localResidual L U ≤ C.map H.subtype := by
    have hh := map_mono (f := H.subtype) hAC
    rwa [map_subgroupOf_eq_of_le hAH] at hh
  let X := C.map H.subtype ⊔ R
  have hXH : X ≤ H := sup_le (map_subtype_le C) hRH
  have hUW : U ≤ D.sourceOrbit := ambientPlane_le_orbit D.sourceOrbit E v f
  have hUR : U ≤ R := le_inf (hUW.trans D.sourceOrbit_weakClosure_setup.le_sylow)
    ((hUW.trans (le_centralizer D.sourceOrbit)).trans (centralizer_le hUW))
  have hUX : U ≤ X := hUR.trans le_sup_right
  have hcoreX : U ≤ X.pCoreIn 2 := le_pCoreIn_of_normalizes
    ((IsElementaryAbelian.isPGroup 2 D.sourceOrbit).to_le hUW) hUX
    ((hXH.trans hHC).trans (Subgroup.centralizer_le_normalizer _))
  have hU : U ≠ ⊥ := by
    intro he
    have hh := DoubledBinaryPlaneQuotient.ambientPlane_card D.sourceOrbit E v f hfv
    change Nat.card U = 4 at hh
    rw [he,card_bot] at hh
    omega
  have hgenH : H = X := le_antisymm (hH.2 ⟨⟨(fun he => hU
    (le_bot_iff.mp (he ▸ hcoreX))),sup_le (hACamb.trans le_sup_left) le_sup_right⟩,
    fun hh => hCM (le_sup_left.trans hh)⟩ hXH) hXH
  have hgen0 : C ⊔ (P : Subgroup H) = ⊤ := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup,hP,←MonoidHom.range_eq_map,range_subtype]
    exact hgenH.symm
  have hnormal : C.Normal := DoubledBinaryResidualMovement.component_normal_of_residual_movement
    P A C hC hAC hPA hgen0 q hq hCimage hmove
  have hP0 : (P : Subgroup H) = R.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le hRH]
  rw [hB0] at hcoreImage
  rw [hP0] at hmove
  exact ⟨H,hH,hHC,hWY,hred,C,hC,hCimage,hCM,hLC,⟨P,hP⟩,
    hi,hno,hnotSylow,hAC,hnormal,hgenH,hcoreImage,hmove,hfive,hk,ho,hm,hs,hrest⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
