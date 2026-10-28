module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryResidualMovement
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinarySmallBlocks

/-!
# Small-block exclusions for the chosen doubled orbit

Retain the original minimal escaping H, its normal lifted C-component,
the full orbit W, residual L0 and original Q. The exact local-base quotient
identifies the index of Q in the original Sylow as two. Coprime splitting
and the paired-plane commutator calculation embed the actual moved
four-space into the intrinsic block module with trivial central kernel.
Thus every short component here has block module order greater than sixteen.

This excludes the exceptional A7 block and the natural A6, L3(2) and L4(2)
blocks on this actual component. It does not identify the ordinary A7
six-space with its exceptional module or the doubled L3 module with a
single natural copy. The remaining constrained rows, ambient containment,
binary endgame, other doubled rows and final contradiction remain with
qt-d-1222-nonff-doubled.
Source: Aschbacher--Smith, proof of Proposition 7.7.3, printed p.709,
refs/quasithin.pdf.
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

/-- The original moved four-space excludes every block module of order
at most sixteen, with all earlier quotient and component data retained. -/
theorem sourceOrbit_binary_pairedPlane_large_block_module
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
                (ChapterC.IsShort C → 16 < Nat.card (ChapterC.BlockModule C)) ∧
                ¬ ChapterC.IsExceptionalA7Block C ∧
                ¬ ChapterC.IsAlternatingBlock C 6 ∧
                ¬ ChapterC.IsSL3EvenBlock C 1 ∧
                ¬ ChapterC.IsLinearTwoBlock C 4 ∧
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
    D.sourceOrbit_binary_pairedPlane_residual_contained h hd hnon F hF hmodel
  refine ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hmark,hbase,hcore,?_⟩
  dsimp only
  intro hout
  obtain ⟨H,hH,hHC,hWY,hred,C,hC,hCimage,hCM,hLC,⟨P,hP⟩,
    hi,hno,hnotSylow,hAC,hnormal,hgen,hcoreImage,hmove,hrest⟩ := hescape hout
  let := hred.normal
  let U := ambientPlane D.sourceOrbit E v f
  let B := localBase L (T : Subgroup G) U
  let R := (T : Subgroup G) ⊓ centralizer (U : Set G)
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let Y := conjugateSpanBy (omegaOneCenterAmbient R) H
  let A := (localResidual L U).subgroupOf H
  let W := D.sourceOrbit.subgroupOf H
  let B₀ := B.subgroupOf H
  change B = (L ⊔ (T : Subgroup G)) ⊓ centralizer (U : Set G) at hbase
  have hBH : B ≤ H := hH.1.1.2
  have hRH : R ≤ H := le_sup_right.trans hBH
  have hAH : localResidual L U ≤ H := le_sup_left.trans hBH
  have hYH : Y ≤ H := conjugateSpanBy_le_self (by
    intro z hz
    exact hRH ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1)
  have hWH : D.sourceOrbit ≤ H := hWY.trans hYH
  have hQH : Q ≤ H := hi.setup.radical_le
  have hWcore : W ≤ pCore 2 H := (comap_mono hWY).trans hred.le_pCore
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf hWH
  have hPB : (P : Subgroup H) ≤ B₀ := by
    intro p hp
    exact mem_sup_right (hP ▸ mem_map_of_mem H.subtype hp)
  have hA : IsPPerfect 2 A := (isPPerfect_embedded_pResidual 2
    (L ⊓ centralizer (U : Set G))).of_surjective
      (subgroupOfEquivOfLe hAH).symm.toMonoidHom (subgroupOfEquivOfLe hAH).symm.surjective
  obtain ⟨hLN,k,hks,a,hE,ha,hcov⟩ := hmark
  have hBN : B ≤ normalizer (D.sourceOrbit : Set G) := by
    rw [hbase]
    exact inf_le_left.trans (sup_le hLN D.sourceOrbit_weakClosure_setup.normalizes)
  have hBC : B ≤ centralizer (U : Set G) := by rw [hbase]; exact inf_le_right
  have hLB : L ⊓ centralizer (U : Set G) ≤ B := by
    rw [hbase]
    exact inf_le_inf_right _ le_sup_left
  obtain ⟨πB,hπB,hkerB⟩ := DoubledBinaryResidualMovement.localBase_quotient
    D.sourceOrbit L B hLN k hks E hE a ha hcov v f hfv hBN hBC hLB
  let eB : B₀ ≃* B := subgroupOfEquivOfLe hBH
  let π := πB.comp eB.toMonoidHom
  have hπ : Function.Surjective π := hπB.comp eB.surjective
  have hk : π.ker = (centralizer (W : Set H)).subgroupOf B₀ := by
    ext x
    change πB (eB x) = 1 ↔ (x : H) ∈ centralizer (W : Set H)
    rw [←MonoidHom.mem_ker,hkerB]
    constructor
    · intro hx w hw
      exact Subtype.ext (hx w hw)
    · intro hx w hw
      exact congrArg Subtype.val (hx ⟨w,hWH hw⟩ hw)
  have hBcore : B₀.pCoreIn 2 = Q.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [map_pCoreIn_of_injective 2 _ H.subtype H.subtype_injective,
      map_subgroupOf_eq_of_le hBH,map_subgroupOf_eq_of_le hQH]
    exact hcore
  have hQeq : (T : Subgroup G) ⊓ centralizer (D.sourceOrbit : Set G) = Q := by
    simpa only [D.sourceOrbit_eq] using D.doubledOrbit_sylow_centralizer h
  have hindex : (Q.subgroupOf H).relIndex (P : Subgroup H) = 2 := by
    apply DoubledBinarySmallBlocks.local_sylow_core_index P B₀ (Q.subgroupOf H)
      hPB hBcore π hπ
    intro p hp hz
    have hc : (p : G) ∈ centralizer (D.sourceOrbit : Set G) := by
      have he : eB ⟨p,hPB hp⟩ ∈ πB.ker := hz
      rw [hkerB] at he
      exact he
    change (p : G) ∈ Q
    rw [←hQeq]
    exact ⟨(hP ▸ mem_map_of_mem H.subtype hp).1,hc⟩
  have hBW : B₀ ≤ normalizer (W : Set H) :=
    (comap_mono hBN).trans (le_normalizer_comap H.subtype)
  have hAB : A ≤ B₀ := comap_mono le_sup_left
  have hsplit := DoubledBinarySmallBlocks.residual_coprime_split W B₀ A hBW hAB π hk hA
  have hcard : Nat.card (⁅W,A⁆ : Subgroup H) = 16 := by
    have he : (⁅W,A⁆ : Subgroup H).map H.subtype =
        ⁅D.sourceOrbit,localResidual L U⁆ := by
      rw [map_commutator,map_subgroupOf_eq_of_le hWH,map_subgroupOf_eq_of_le hAH]
    rw [←card_map_of_injective H.subtype_injective,he]
    exact DoubledBinaryIntersection.pairedPlane_residual_card D.sourceOrbit L hLN k E hE v f hfv
      (DoubledBinaryOddCore.pairedPlane_residual_supplement D.sourceOrbit L hLN k hks E hE v f hfv)
  have hlarge : ChapterC.IsShort C → 16 < Nat.card (ChapterC.BlockModule C) := by
    intro hb
    by_contra! hsmall
    obtain ⟨hDU,hDZ,hDC⟩ := DoubledBinarySmallBlocks.residual_block_embedding W A C hC.subnormal hb
      hWcore hAC (hAB.trans hBW) hsplit
    let eC := C.equivMapOfInjective H.subtype H.subtype_injective
    let eQ := QuotientGroup.congr (pCore 2 C) (pCore 2 (C.map H.subtype)) eC (pCore_map_iso 2 eC)
    let : IsQuasisimple (C.map H.subtype ⧸ pCore 2 (C.map H.subtype)) := hi.quasisimple
    let : IsQuasisimple (C ⧸ pCore 2 C) := IsQuasisimple.of_mulEquiv eQ.symm
    apply DoubledBinarySmallBlocks.small_block_fixed_contradiction C (Q.subgroupOf H) P hC.subnormal
      hb hindex.le ((⁅W,A⁆).subgroupOf C) hDU hDZ
      ((Nat.card_congr (subgroupOfEquivOfLe hDC).toEquiv).trans hcard) hsmall
    intro d hd q hq
    apply Subtype.ext
    apply Subtype.ext
    have hdW : ((d : H) : G) ∈ D.sourceOrbit :=
      (le_normalizer_iff_commutator_le_left.mp (hAB.trans hBW)) hd
    have hqQ : ((q : H) : G) ∈ Q := hq
    have hc : ((q : H) : G) ∈ centralizer (D.sourceOrbit : Set G) :=
      (hQeq.symm ▸ hqQ).2
    exact (hc d hdW).symm
  have hnoA7 : ¬ ChapterC.IsExceptionalA7Block C := by
    intro hb
    have hh := hlarge hb.1
    rw [hb.module_card] at hh
    omega
  have hnoA6 : ¬ ChapterC.IsAlternatingBlock C 6 := by
    intro hb
    have hh := hlarge hb.2.1
    rw [hb.module_card_even (by decide)] at hh
    norm_num at hh
  have hnoL3 : ¬ ChapterC.IsSL3EvenBlock C 1 := by
    intro hb
    have hh := hlarge hb.2.1
    rw [hb.module_card] at hh
    norm_num at hh
  have hnoL4 : ¬ ChapterC.IsLinearTwoBlock C 4 := by
    intro hb
    have hh := hlarge hb.2.1
    rw [hb.module_card] at hh
    norm_num at hh
  exact ⟨H,hH,hHC,hWY,hred,C,hC,hCimage,hCM,hLC,⟨P,hP⟩,
    hi,hno,hnotSylow,hAC,hnormal,hgen,hlarge,hnoA7,hnoA6,hnoL3,hnoL4,hcoreImage,hmove,hrest⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
