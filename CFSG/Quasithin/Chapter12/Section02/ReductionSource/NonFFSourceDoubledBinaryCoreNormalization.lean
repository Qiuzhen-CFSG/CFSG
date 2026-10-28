module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryKernel
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryMovingBlocks
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.OriginalGeometry

/-!
# Original-core normalization and the actual C.2.7 action

The lifted component is normalized by the full original Q. In the moving
natural-block branch, the Borel preserves the whole doubled orbit W by
Thompson normalizer control; the exchanging Q-element fixes W pointwise,
so the Borel displacement vanishes and Borel rigidity forces the block
into M. The deleted A₅ branch is excluded by the original local-residual
supplement and the Sylow-fixed-line calculation. Quasisimplicity rules
out the cubic block.

Transport the surviving lift through its actual inclusion into G, and
apply C.2.7 on C join Q. This gives the full star-kernel bounds, reduced
module, offender conclusions, marked Thompson-normalizer containment,
and B.5.1 moved-section action. The earlier Thompson quotient, its full
preimage, the lifted C-component, and this new star quotient are distinct.
No solvability assertion about the original action kernel is used.

This proves 7.7.8 on the chosen orbit. The constrained-component case
exclusions, ambient paired-plane containment, binary endgame, and remaining
doubled rows remain with qt-d-1222-nonff-doubled.
Source: Aschbacher–Smith, 7.7.8–10, printed pp.707–709, C.2.7(1–2),
printed pp.145–147, and B.5.1, refs/quasithin.pdf.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Stellmacher Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource ChapterE BinaryLinearThree
open DoubledBinaryPlanes DoubledBinaryLocalCore DoubledBinaryOmega
universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The full original core normalizes the escaping lifted C-component.
All original plane, quotient and Sylow witnesses are retained. -/
theorem sourceOrbit_binary_pairedPlane_core_normalizes_lift
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
          let B := localBase L (T : Subgroup G) U
          let R := (T : Subgroup G) ⊓ centralizer (U : Set G)
          (∃ S : Sylow 2 (centralizer (U : Set G)),
            (S : Subgroup _).map (centralizer (U : Set G)).subtype = R) ∧
          B = (L ⊔ (T : Subgroup G)) ⊓ centralizer (U : Set G) ∧
          B.pCoreIn 2 = (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
          (¬ centralizer (U : Set G) ≤ normalizer (L : Set G) →
            ∃ H : Subgroup G,
              H ∈ Chapter3.HStar B (normalizer (L : Set G)) ∧
              H ≤ centralizer (U : Set G) ∧ U ≤ H.pCoreIn 2 ∧
              IsSQTK KnownSimple.IsKnownSimple H ∧
              (∃ S : Sylow 2 H, (S : Subgroup H).map H.subtype = R) ∧
              H.pCoreIn 2 < (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
              H = elementaryAbelianMaxJ H ⊔ B ∧
              H ⊓ normalizer (L : Set G) ∈ Chapter1.He G ∧
              HasCharacteristicTwo H ∧ generalizedFitting H = pCore 2 H ∧
              Chapter1.RadicalExclusions.PushingUpSetup KnownSimple.IsKnownSimple H
                ((L ⊔ (T : Subgroup G)).pCoreIn 2) (H ⊓ normalizer (L : Set G)) ∧
              let Y := conjugateSpanBy (omegaOneCenterAmbient R) H
              D.sourceOrbit ≤ Y ∧ ∃ hred : IsPReduced 2 (Y.subgroupOf H),
              centralizer (Y : Set G) ≤ normalizer (L : Set G) ∧
              ¬ elementaryAbelianMaxJ H ≤ centralizer (Y : Set G) ∧
              inducedAutomizer Y (elementaryAbelianMaxJ H) ≠ ⊥ ∧
              DoubledBinaryThompson.ReducedThompsonAlternative (Y.subgroupOf H) hred ∧
              ¬ DoubledBinaryThompsonPlanes.ReducedSymmetricThree (Y.subgroupOf H) hred ∧
              DoubledBinaryThompsonRelativePlanes.RelativePlaneFactorsContained (Y.subgroupOf H) hred
                ((localResidual L U).subgroupOf H)
                ((normalizer (L : Set G)).subgroupOf H) ∧
              let := hred.normal
              let := hred.elementary
              let J := DoubledBinaryThompson.thompsonImage (Y.subgroupOf H)
              let q := ChapterB.InternalThompsonAction.actionMk (Y.subgroupOf H)
              ¬ Group.IsSolvable J ∧
              ∃ K : Subgroup J, IsComponent J K ∧
                  IsComponent (ChapterB.InternalThompsonAction.ActionQuotient (Y.subgroupOf H))
                    (K.map J.subtype) ∧
                  ¬ ((K.map J.subtype).comap q).map H.subtype ≤ normalizer (L : Set G) ∧
                  ∃ C : Subgroup H, C.IsCComponent ∧ C.map q = K.map J.subtype ∧
                    C ⊔ q.ker = (K.map J.subtype).comap q ∧
                    ¬ C.map H.subtype ≤ normalizer (L : Set G) ∧
                    (localResidual L U).subgroupOf H ≤ normalizer (C : Set H) ∧
                    (C.Normal ∨ (normalizer (C : Set H)).index = 2) ∧
                    ∃ P : Sylow 2 H, (P : Subgroup H).map H.subtype = R ∧
                      (conjugateSpanBy C (P : Subgroup H)).Normal ∧
                      H = (conjugateSpanBy C (P : Subgroup H)).map H.subtype ⊔ B ∧
                      (∃ S : Sylow 2 (centralizer (Y.subgroupOf H : Set H)),
                        (S : Subgroup (centralizer (Y.subgroupOf H : Set H))).Normal) ∧
                      IsQuasisimple (C ⧸ pCore 2 C) ∧
                      generalizedFitting C = pCore 2 C ∧
                      ((L ⊔ (T : Subgroup G)).pCoreIn 2).subgroupOf H ≤
                        normalizer (C : Set H)) := by
  obtain ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hmark,hS,hbase,hcore,hescape⟩ :=
    D.sourceOrbit_binary_pairedPlane_quasisimple_lift h hd hnon F hF hmodel
  let U := ambientPlane D.sourceOrbit E v f
  let B := localBase L (T : Subgroup G) U
  let R := (T : Subgroup G) ⊓ centralizer (U : Set G)
  let M := normalizer (L : Set G)
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  refine ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hmark,hS,hbase,hcore,?_⟩
  intro hout
  obtain ⟨H,hH,hHC,hUH,hSQ,hSyl,hlt,hgen,hMH,hchar,hgf,hpush,
    hWY,hred,hcent,hJ,hJne,hclass,hnot,hplanes,hnsol,hchoice⟩ := hescape hout
  refine ⟨H,hH,hHC,hUH,hSQ,hSyl,hlt,hgen,hMH,hchar,hgf,hpush,
    hWY,hred,hcent,hJ,hJne,hclass,hnot,hplanes,hnsol,?_⟩
  let Y := conjugateSpanBy (omegaOneCenterAmbient R) H
  let := hred.normal
  let := hred.elementary
  obtain ⟨K,hK,hKA,hKM,C,hC,he,hpre,hCM,hLC,horbit,P,hP,hnormal,hgenerate,
    hclosed,hquasi,hfit,halt⟩ := hchoice
  let := hquasi
  refine ⟨K,hK,hKA,hKM,C,hC,he,hpre,hCM,hLC,horbit,P,hP,hnormal,hgenerate,
    hclosed,hquasi,hfit,?_⟩
  rcases halt with hn | ⟨hb,S,hS⟩
  · exact hn
  have hRH : R ≤ H := le_sup_right.trans hH.1.1.2
  have hYH : Y ≤ H := conjugateSpanBy_le_self (by
    intro z hz
    exact hRH ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1)
  have hWH : D.sourceOrbit ≤ H := hWY.trans hYH
  let W := D.sourceOrbit.subgroupOf H
  have hWcore : W ≤ pCore 2 H := (comap_mono hWY).trans hred.le_pCore
  have hWC : W ≤ normalizer (C : Set H) := hWcore.trans (hC.pCore_le_normalizer 2)
  have houtC : ¬ C ≤ M.subgroupOf H := by
    intro hh
    exact hCM (map_le_iff_le_comap.mpr hh)
  have hMWamb : M ≤ normalizer (D.sourceOrbit : Set G) :=
    (D.sourceOrbit_normalizer_eq_of_markedDoubled h hd).symm.le
  have hMW : M.subgroupOf H ≤ normalizer (W : Set H) :=
    (comap_mono hMWamb).trans (le_normalizer_comap H.subtype)
  have hWM : centralizer (W : Set H) ≤ M.subgroupOf H := by
    intro x hx
    apply (Subgroup.centralizer_le_normalizer (D.sourceOrbit : Set G)).trans
      (D.sourceOrbit_normalizer_eq_of_markedDoubled h hd).le
    intro w hw
    exact congrArg Subtype.val (hx ⟨w,hWH hw⟩ hw)
  have hWQ : W ≤ centralizer (Q.subgroupOf H : Set H) := by
    have hQeq : (T : Subgroup G) ⊓ centralizer (D.sourceOrbit : Set G) = Q := by
      simpa only [D.sourceOrbit_eq] using D.doubledOrbit_sylow_centralizer h
    have hQcent : Q ≤ centralizer (D.sourceOrbit : Set G) := by
      rw [←hQeq]
      exact inf_le_right
    intro w hw q hq
    exact Subtype.ext (hQcent hq w hw).symm
  have hctl : (Q.subgroupOf H).characteristicNormalizerClosure ≤ M.subgroupOf H :=
    hpush.characteristic_control.trans (comap_mono inf_le_right)
  have hSC : (S : Subgroup C).map C.subtype ≤ Q.subgroupOf H := hS.trans_le inf_le_left
  rcases hb with ⟨n,hb⟩ | hb | hb
  · exact DoubledBinaryMovingBlocks.natural_block_normalized
      (Q.subgroupOf H) (M.subgroupOf H) W C hpush.radical hchar hctl hC houtC hb S hSC
      (pCore_isPGroup.to_le hWcore) hWC hWQ hMW hWM
  · obtain ⟨e⟩ := hb.2.2.quotient_iso
    have hc : Nat.card (C ⧸ pCore 2 C) = 3 := by
      rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
      norm_num
    let : IsCyclic (C ⧸ pCore 2 C) := isCyclic_of_prime_card hc
    let : IsSimpleGroup ((C ⧸ pCore 2 C) ⧸ center (C ⧸ pCore 2 C)) := IsQuasisimple.simple
    let : Nontrivial (C ⧸ pCore 2 C) := (QuotientGroup.mk'_surjective (center _)).nontrivial
    exact (Group.IsPerfect.not_isMulCommutative (C ⧸ pCore 2 C) inferInstance).elim
  · have hAQ : (localResidual L U).subgroupOf H ≤ normalizer (Q.subgroupOf H : Set H) := by
      have hBQ : B ≤ normalizer (Q : Set G) := by
        change B ≤ normalizer ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G)
        rw [←hcore]
        exact B.le_normalizer.trans (normalizer_le_normalizer_characteristic_image B (pCore 2 B))
      exact (comap_mono ((le_sup_left : localResidual L U ≤ B).trans hBQ)).trans
        (le_normalizer_comap H.subtype)
    have hUC : U.subgroupOf H ≤ centralizer (C : Set H) := by
      intro u hu c hc
      exact Subtype.ext (hHC c.property u hu).symm
    have hUH' : U ≤ H := hUH.trans (pCoreIn_le 2 H)
    have hAH : localResidual L U ≤ H := le_sup_left.trans hH.1.1.2
    have hsupp : U.subgroupOf H ⊔ ⁅W,(localResidual L U).subgroupOf H⁆ = W := by
      apply map_injective H.subtype_injective
      rw [Subgroup.map_sup,map_commutator,map_subgroupOf_eq_of_le hUH',
        map_subgroupOf_eq_of_le hWH,map_subgroupOf_eq_of_le hAH]
      obtain ⟨hLN,q,hq,a,hE,ha,hcov⟩ := hmark
      exact DoubledBinaryOddCore.pairedPlane_residual_supplement D.sourceOrbit L hLN q hq E hE v f hfv
    exact (DoubledBinaryMovingBlocks.alternating_five_no_escape (Q.subgroupOf H)
      (M.subgroupOf H) W C ((localResidual L U).subgroupOf H) (U.subgroupOf H)
      hpush.radical hC houtC hb S hSC hWcore hWQ hAQ hLC hUC hsupp hWM).elim

open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface

/-- The original escaping component now satisfies C.2.7, with its actual
core and star quotients and full moved-section action. -/
theorem sourceOrbit_binary_pairedPlane_star_component
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
          (¬ centralizer (U : Set G) ≤ normalizer (L : Set G) →
            ∃ H : Subgroup G,
              H ∈ Chapter3.HStar (localBase L (T : Subgroup G) U) (normalizer (L : Set G)) ∧
              H ≤ centralizer (U : Set G) ∧
              ∃ C : Subgroup H, C.IsCComponent ∧
                ¬ C.map H.subtype ≤ normalizer (L : Set G) ∧
                let C₀ := C.map H.subtype
                let M₀ := H ⊓ normalizer (L : Set G)
                Input KnownSimple.IsKnownSimple H Q M₀ C₀ ∧
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
  obtain ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hmark,hS,hbase,hcore,hescape⟩ :=
    D.sourceOrbit_binary_pairedPlane_core_normalizes_lift h hd hnon F hF hmodel
  refine ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hmark,?_⟩
  dsimp only
  intro hout
  obtain ⟨H,hH,hHC,hUH,hSQ,hSyl,hlt,hgen,hMH,hchar,hgf,hpush,
    hWY,hred,hcent,hJ,hJne,hclass,hnot,hplanes,hnsol,hchoice⟩ := hescape hout
  let := hred.normal
  let := hred.elementary
  obtain ⟨K,hK,hKA,hKM,C,hC,he,hpre,hCM,hLC,horbit,P,hP,hnormal,hgenerate,
    hclosed,hquasi,hfit,hnorm⟩ := hchoice
  refine ⟨H,hH,hHC,C,hC,hCM,?_⟩
  let C₀ := C.map H.subtype
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let e : C ≃* C₀ := C.equivMapOfInjective H.subtype H.subtype_injective
  have hC₀ : C₀ ∈ Chapter1.cComponentsIn H := ⟨map_subtype_le _,by
    have heC : C₀.subgroupOf H = C := comap_map_eq_self_of_injective H.subtype_injective C
    rw [heC]
    exact hC⟩
  let := hquasi
  have hquasi₀ : IsQuasisimple (C₀ ⧸ pCore 2 C₀) :=
    IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e))
  have hfit₀ : generalizedFitting C₀ = pCore 2 C₀ := by
    have hh := congrArg (map e.toMonoidHom) hfit
    rwa [map_generalizedFitting_equiv,pCore_map_iso] at hh
  have hnorm₀ : Q ≤ normalizer (C₀ : Set G) := by
    have hmap := (map_mono (f := H.subtype) hnorm).trans (C.le_normalizer_map H.subtype)
    rwa [map_subgroupOf_eq_of_le hpush.radical_le] at hmap
  have hi : Input KnownSimple.IsKnownSimple H Q (H ⊓ normalizer (L : Set G)) C₀ :=
    ⟨hpush,hC₀,hquasi₀,hfit₀,fun hh => hCM (hh.trans inf_le_right),hnorm₀⟩
  obtain ⟨hk,ho⟩ := ChapterC.C27Source.kernel_offender_from_source hi
  obtain ⟨hm,hs⟩ := ChapterC.C27Source.star_thompson_intersection_from_source hi
  exact ⟨hi,hk,ho,hm,hs,ChapterC.C27Source.star_moved_section_from_source hi⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
