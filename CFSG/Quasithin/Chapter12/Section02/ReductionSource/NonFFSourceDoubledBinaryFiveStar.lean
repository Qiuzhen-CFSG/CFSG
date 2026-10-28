module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryCoreNormalization
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryFiveStar

/-!
# The five-letter star branch on the chosen doubled orbit

Restrict the original Sylow of the minimal escaping H to its lifted
C-component. Its ambient image normalizes Q because Q is the two-core of
the original local base. The five-letter star calculation therefore makes
Q Sylow in the component join Q. The full doubled orbit lies in O₂(H),
is fixed by Q, and is the sum of the paired plane and its original
residual commutator. The deleted A₅ Sylow-fixed line then forces the whole
component into the orbit normalizer, a contradiction.

Consequently an A₅ star image forces the distinct natural L₂(4) block.
The actual C.2.7 kernel, offenders and B.5 moved-section conclusion remain
attached to this same component. No condition on the full star kernel or
identification of the whole doubled orbit with the selected seed is added.

This settles the deleted A₅ part of 7.7.9(1). The natural L₂(4) case,
other constrained components, ambient paired-plane containment and final
non-FF contradiction remain with qt-d-1222-nonff-doubled.
Source: Aschbacher–Smith, 7.7.9(1), printed p.708, refs/quasithin.pdf.
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

/-- The original escaping lift is not a deleted A₅ block; a five-letter
star image leaves precisely the natural L₂(4) block with Q Sylow in its join. -/
theorem sourceOrbit_binary_pairedPlane_five_star
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
                (Nonempty (starImage C₀ Q C₀ ≃* alternatingGroup (Fin 5)) →
                  Chapter1.IsSylowIn 2 Q (C₀ ⊔ Q) ∧ ChapterC.IsL2EvenBlock C₀ 2) ∧
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
  have hfive : Nonempty (starImage C₀ Q C₀ ≃* alternatingGroup (Fin 5)) →
      Chapter1.IsSylowIn 2 Q (C₀ ⊔ Q) ∧ ChapterC.IsL2EvenBlock C₀ 2 := by
    rintro ⟨a⟩
    obtain ⟨hs,hn | hd⟩ := DoubledBinaryFiveStar.five_star_natural_or_deleted hi S₀ hS₀Q a
    · exact ⟨hs,hn⟩
    · exact (hno hd).elim
  obtain ⟨hk,ho⟩ := ChapterC.C27Source.kernel_offender_from_source hi
  obtain ⟨hm,hs⟩ := ChapterC.C27Source.star_thompson_intersection_from_source hi
  exact ⟨hi,hno,hfive,hk,ho,hm,hs,ChapterC.C27Source.star_moved_section_from_source hi⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
