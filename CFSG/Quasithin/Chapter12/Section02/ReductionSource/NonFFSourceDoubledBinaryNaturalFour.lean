module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryCoreNormalization
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryNaturalFour

/-!
# Excluding the natural rank-one rows on the chosen doubled orbit

Retain the original escaping H, its lifted C-component, and Q. When Q
is Sylow in the component join, the component Sylow fixes the full orbit.
The natural-block Borel normalizes the original Thompson subgroup of Q,
so characteristic-normalizer control places it in the orbit normalizer.
Restrict the literal paired-plane quotient map to H; its full kernel is
still the orbit centralizer. The Borel/residual image comparison excludes
natural blocks at every field size, using the Sylow-fixed bound at four
and the actual Borel {2,3}-residual at larger fields.

Together with the deleted A₅ exclusion, C.2.5 now shows that Q is not
Sylow in the original component join. In particular the A₅ star image is
excluded. The C.2.7 kernel, offenders and moved-section conclusions remain
attached to the same component. All inputs of the new exclusion are
discharged on this chosen module; W remains the full doubled orbit.

Source: Aschbacher–Smith, 7.7.9(1), printed p.708, refs/quasithin.pdf.
The other constrained rows, ambient paired-plane containment, binary
endgame and final non-FF assembly remain with qt-d-1222-nonff-doubled.
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

/-- Neither the deleted A₅ block nor an A₅ star image can occur on the
actual escaping component of the chosen doubled orbit. -/
theorem sourceOrbit_binary_pairedPlane_original_component
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
  obtain ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hmark,hS,hbase,hcore,hescape⟩ :=
    D.sourceOrbit_binary_pairedPlane_core_normalizes_lift h hd hnon F hF hmodel
  refine ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hmark,?_⟩
  dsimp only
  refine ⟨hbase,hcore,?_⟩
  intro hout
  obtain ⟨H,hH,hHC,hUH,hSQ,hSyl,hlt,hgen,hMH,hchar,hgf,hpush,
    hWY,hred,hcent,hJ,hJne,hclass,hnot,hplanes,hnsol,hchoice⟩ := hescape hout
  let := hred.normal
  let := hred.elementary
  obtain ⟨K,hK,hKA,hKM,C,hC,he,hpre,hCM,hLC,horbit,P,hP,hnormal,hgenerate,
    hclosed,hquasi,hfit,hnorm⟩ := hchoice
  refine ⟨H,hH,hHC,hWY,hred,C,hC,he.symm ▸ hKA,hCM,hLC,⟨P,hP⟩,?_⟩
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
  let B := localBase L (T : Subgroup G) (ambientPlane D.sourceOrbit E v f)
  let R := (T : Subgroup G) ⊓ centralizer (ambientPlane D.sourceOrbit E v f : Set G)
  have hBQ : B ≤ normalizer (Q : Set G) := by
    change B ≤ normalizer ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G)
    rw [←hcore]
    exact B.le_normalizer.trans (normalizer_le_normalizer_characteristic_image B (pCore 2 B))
  obtain ⟨S,hS⟩ := P.exists_subgroupOf_eq_of_subnormal C hC.subnormal
  let S₀ := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hS₀Q : (S₀ : Subgroup C₀).map C₀.subtype ≤ normalizer (Q : Set G) := by
    rintro _ ⟨x,⟨c,hc,rfl⟩,rfl⟩
    have hcP : (c : H) ∈ P := by
      change c ∈ (P : Subgroup H).subgroupOf C
      rwa [←hS]
    have hcR : ((c : H) : G) ∈ R := by
      change ((c : H) : G) ∈ (T : Subgroup G) ⊓ centralizer (ambientPlane D.sourceOrbit E v f : Set G)
      rw [←hP]
      exact mem_map_of_mem H.subtype hcP
    exact hBQ (mem_sup_right hcR)
  have hno : ¬ ChapterC.IsAlternatingBlock C₀ 5 := by
    intro hb
    have hs0 := DoubledBinaryFiveStar.deleted_five_core_sylow hi S₀ hS₀Q hb
    have hsH : Chapter1.IsSylowIn 2 (Q.subgroupOf H) (C ⊔ Q.subgroupOf H) := by
      apply (Chapter1.IsSylowIn.map_iff H.subtype H.subtype_injective).mp
      rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (show Q ≤ H from hpush.radical_le)]
      exact hs0
    let : (C.subgroupOf (C ⊔ Q.subgroupOf H)).Normal :=
      normal_subgroupOf_of_le_normalizer (sup_le C.le_normalizer hnorm)
    obtain ⟨SC,hSC⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hsH
      (show C ≤ C ⊔ Q.subgroupOf H from le_sup_left)
      (inferInstance : (C.subgroupOf (C ⊔ Q.subgroupOf H)).Normal).isSubnormal
    let U := ambientPlane D.sourceOrbit E v f
    let Y := conjugateSpanBy (omegaOneCenterAmbient R) H
    have hRH : R ≤ H := le_sup_right.trans hH.1.1.2
    have hYH : Y ≤ H := conjugateSpanBy_le_self (by
      intro z hz
      exact hRH ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1)
    have hWH : D.sourceOrbit ≤ H := hWY.trans hYH
    let W := D.sourceOrbit.subgroupOf H
    have hWcore : W ≤ pCore 2 H := (comap_mono hWY).trans hred.le_pCore
    have hWQ : W ≤ centralizer (Q.subgroupOf H : Set H) := by
      have hQeq : (T : Subgroup G) ⊓ centralizer (D.sourceOrbit : Set G) = Q := by
        simpa only [D.sourceOrbit_eq] using D.doubledOrbit_sylow_centralizer h
      have hQcent : Q ≤ centralizer (D.sourceOrbit : Set G) := by
        rw [←hQeq]
        exact inf_le_right
      intro w hw q hq
      exact Subtype.ext (hQcent hq w hw).symm
    have hAQ : (localResidual L U).subgroupOf H ≤ normalizer (Q.subgroupOf H : Set H) :=
      (comap_mono ((le_sup_left : localResidual L U ≤ B).trans hBQ)).trans
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
    have hWM : centralizer (W : Set H) ≤ (normalizer (L : Set G)).subgroupOf H := by
      intro x hx
      apply (Subgroup.centralizer_le_normalizer (D.sourceOrbit : Set G)).trans
        (D.sourceOrbit_normalizer_eq_of_markedDoubled h hd).le
      intro w hw
      exact congrArg Subtype.val (hx ⟨w,hWH hw⟩ hw)
    have houtC : ¬ C ≤ (normalizer (L : Set G)).subgroupOf H := by
      intro hh
      exact hCM (map_le_iff_le_comap.mpr hh)
    exact DoubledBinaryMovingBlocks.alternating_five_no_escape (Q.subgroupOf H)
      ((normalizer (L : Set G)).subgroupOf H) W C ((localResidual L U).subgroupOf H)
      (U.subgroupOf H) hpush.radical hC houtC (hb.of_mulEquiv e.symm)
      SC (hSC.trans_le inf_le_left) hWcore hWQ hAQ hLC hUC hsupp hWM
  have hnatural : ¬ (Chapter1.IsSylowIn 2 Q (C₀ ⊔ Q) ∧ ∃ n, ChapterC.IsL2EvenBlock C₀ n) := by
    rintro ⟨hs0,n,hb⟩
    have hbC : ChapterC.IsL2EvenBlock C n := hb.of_mulEquiv e.symm
    have hsH : Chapter1.IsSylowIn 2 (Q.subgroupOf H) (C ⊔ Q.subgroupOf H) := by
      apply (Chapter1.IsSylowIn.map_iff H.subtype H.subtype_injective).mp
      rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (show Q ≤ H from hpush.radical_le)]
      exact hs0
    let : (C.subgroupOf (C ⊔ Q.subgroupOf H)).Normal :=
      normal_subgroupOf_of_le_normalizer (sup_le C.le_normalizer hnorm)
    obtain ⟨SC,hSC⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hsH
      (show C ≤ C ⊔ Q.subgroupOf H from le_sup_left)
      (inferInstance : (C.subgroupOf (C ⊔ Q.subgroupOf H)).Normal).isSubnormal
    let U := ambientPlane D.sourceOrbit E v f
    let Y := conjugateSpanBy (omegaOneCenterAmbient R) H
    have hRH : R ≤ H := le_sup_right.trans hH.1.1.2
    have hYH : Y ≤ H := conjugateSpanBy_le_self (by
      intro z hz
      exact hRH ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1)
    have hWH : D.sourceOrbit ≤ H := hWY.trans hYH
    let W := D.sourceOrbit.subgroupOf H
    let : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf hWH
    let N := (normalizer (L : Set G)).subgroupOf H
    let A := (localResidual L U).subgroupOf H
    have hWcore : W ≤ pCore 2 H := (comap_mono hWY).trans hred.le_pCore
    have hNamb : normalizer (L : Set G) ≤ normalizer (D.sourceOrbit : Set G) :=
      (D.sourceOrbit_normalizer_eq_of_markedDoubled h hd).symm.le
    have hNW : N ≤ normalizer (W : Set H) :=
      (comap_mono hNamb).trans (le_normalizer_comap H.subtype)
    have hWM : centralizer (W : Set H) ≤ N := by
      intro x hx
      apply (Subgroup.centralizer_le_normalizer (D.sourceOrbit : Set G)).trans
        (D.sourceOrbit_normalizer_eq_of_markedDoubled h hd).le
      intro w hw
      exact congrArg Subtype.val (hx ⟨w,hWH hw⟩ hw)
    have houtC : ¬ C ≤ N := by
      intro hh
      exact hCM (map_le_iff_le_comap.mpr hh)
    have hWQ : W ≤ centralizer (Q.subgroupOf H : Set H) := by
      have hQeq : (T : Subgroup G) ⊓ centralizer (D.sourceOrbit : Set G) = Q := by
        simpa only [D.sourceOrbit_eq] using D.doubledOrbit_sylow_centralizer h
      have hQcent : Q ≤ centralizer (D.sourceOrbit : Set G) := by
        rw [←hQeq]
        exact inf_le_right
      intro w hw q hq
      exact Subtype.ext (hQcent hq w hw).symm
    have hctl : (Q.subgroupOf H).characteristicNormalizerClosure ≤ N :=
      hpush.characteristic_control.trans (comap_mono inf_le_right)
    have hJN := ChapterC.Section02Source.thompson_le_component_normalizer_of_characteristicTwo
      (Q.subgroupOf H) N C hpush.radical hchar hctl houtC hC
    have hBN : (normalizer (SC : Set C)).map C.subtype ≤ N :=
      (hbC.borel_normalizes_thompson C (Q.subgroupOf H) hpush.radical.isPGroup
        SC (hSC.trans_le inf_le_left) hJN).trans
          ((normalizer_maxJ_le_characteristicNormalizerClosure (Q.subgroupOf H)
            (Q.subgroupOf H) (sSup_le fun _ hA => hA.1) le_rfl
            (elementaryAbelianMaxJ_ne_bot_of_finite_pGroup (Q.subgroupOf H)
              hpush.radical.isPGroup hpush.radical.1)).trans hctl)
    have hAN : A ≤ N := comap_mono ((map_subtype_le _).trans
      (inf_le_left.trans L.le_normalizer))
    have hAH : localResidual L U ≤ H := le_sup_left.trans hH.1.1.2
    have hUH' : U ≤ H := hUH.trans (pCoreIn_le 2 H)
    have hpA : IsPPerfect 2 A := by
      have hp : IsPPerfect 2 (localResidual L U) :=
        (isPPerfect_pResidual 2).of_surjective
          ((L ⊓ centralizer (U : Set G)).subtype.subgroupMap (pResidual 2 _))
          ((L ⊓ centralizer (U : Set G)).subtype.subgroupMap_surjective _)
      exact hp.of_surjective (subgroupOfEquivOfLe hAH).symm.toMonoidHom
        (subgroupOfEquivOfLe hAH).symm.surjective
    have hsupp : U.subgroupOf H ⊔ ⁅W,A⁆ = W := by
      apply map_injective H.subtype_injective
      rw [Subgroup.map_sup,map_commutator,map_subgroupOf_eq_of_le hUH',
        map_subgroupOf_eq_of_le hWH,map_subgroupOf_eq_of_le hAH]
      obtain ⟨hLN,q,hq,a,hE,ha,hcov⟩ := hmark
      exact DoubledBinaryOddCore.pairedPlane_residual_supplement D.sourceOrbit L hLN q hq E hE v f hfv
    obtain ⟨hLN,q,hq,a,hE,ha,hcov⟩ := hmark
    obtain ⟨π₀,hπ₀,hk₀⟩ := DoubledBinaryPlaneQuotient.centralizer_quotient
      D.sourceOrbit U (DoubledBinaryPlaneQuotient.ambientPlane_equiv
        D.sourceOrbit L hLN q hq E hE a ha hcov v f hfv)
    let N₀ := normalizer (D.sourceOrbit : Set G) ⊓ centralizer (U : Set G)
    let j : N →* N₀ := (H.subtype.comp N.subtype).codRestrict N₀
      (fun x => ⟨hNamb x.property,hHC x.val.property⟩)
    let π := π₀.comp j
    have hk : π.ker = (centralizer (W : Set H)).subgroupOf N := by
      ext x
      change π₀ (j x) = 1 ↔ (x : H) ∈ centralizer (W : Set H)
      rw [←MonoidHom.mem_ker,hk₀]
      constructor
      · intro hx w hw
        exact Subtype.ext (hx w hw)
      · intro hx w hw
        exact congrArg Subtype.val (hx ⟨w,hWH hw⟩ hw)
    have hcU : Nat.card (U.subgroupOf H) = 4 :=
      (Nat.card_congr (subgroupOfEquivOfLe hUH').toEquiv).trans
        (DoubledBinaryPlaneQuotient.ambientPlane_card D.sourceOrbit E v f hfv)
    have hcW : Nat.card W = 64 := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hWH).toEquiv]
      change Nat.card (Additive D.sourceOrbit) = 64
      rw [Nat.card_congr E.toEquiv]
      simp [NaturalDual.Space,Module.natCard_eq_pow_finrank (K := ZMod 2),
        Module.finrank_prod,BinaryLinearThree.Vector,Matrix.PSL3Two.Fano.Vector]
    exact DoubledBinaryNaturalFour.natural_block_no_escape W C N A (U.subgroupOf H)
      hC hbC hWcore (fun hh => houtC (hh.trans hWM)) SC
      (hWQ.trans (centralizer_le (hSC.trans_le inf_le_left))) hNW hAN hBN hpA π hk hsupp hcU hcW
  have hnotSylow : ¬ Chapter1.IsSylowIn 2 Q (C₀ ⊔ Q) := by
    intro hs
    rcases ChapterC.C27Source.source_rankOne_blocks_of_sylow hi hs with hn | ha
    · exact hnatural ⟨hs,hn⟩
    · exact hno ha
  have hfive : ¬ Nonempty (starImage C₀ Q C₀ ≃* alternatingGroup (Fin 5)) := by
    rintro ⟨a⟩
    exact hnotSylow (DoubledBinaryFiveStar.five_star_core_sylow hi S₀ hS₀Q a)
  obtain ⟨hk,ho⟩ := ChapterC.C27Source.kernel_offender_from_source hi
  obtain ⟨hm,hs⟩ := ChapterC.C27Source.star_thompson_intersection_from_source hi
  exact ⟨hi,hno,hnotSylow,hfive,hk,ho,hm,hs,ChapterC.C27Source.star_moved_section_from_source hi⟩

/-- Neither the deleted A₅ block nor an A₅ star image can occur on the
actual escaping component of the chosen doubled orbit. -/
theorem sourceOrbit_binary_pairedPlane_no_five_star
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
                ¬ ChapterC.IsAlternatingBlock C₀ 5 ∧
                ¬ Chapter1.IsSylowIn 2 Q (C₀ ⊔ Q) ∧
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
  refine ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hmark,?_⟩
  dsimp only
  intro hout
  obtain ⟨H,hH,hHC,hWY,hred,C,hC,hCimage,hCM,hLC,hP,hrest⟩ := hescape hout
  exact ⟨H,hH,hHC,C,hC,hCM,hrest⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
