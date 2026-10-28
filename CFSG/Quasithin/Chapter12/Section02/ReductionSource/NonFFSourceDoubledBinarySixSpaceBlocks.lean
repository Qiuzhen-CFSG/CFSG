module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinarySmallBlocks
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinarySixSpaceBlocks

/-!
# Six-space block exclusions on the chosen doubled orbit

The original residual commutator has order sixteen and injects into the
intrinsic block module. Its centralizer contains the original Q, of index
two in the original Sylow. An ordinary A₇ block is impossible because such
a subgroup fixes at most eight vectors on the natural six-space.

The residual four-space is invariant under the original Sylow, whose
index-two action has at least four fixed points. A binary G₂ block is
therefore also impossible: the component Sylow fixes at most two vectors
in its actual natural module for G₂(2)′. Both conclusions use the same
selected component, full orbit, residual and quotient kernels. The original
Sylow index and the literal embedded four-space are retained for the
remaining constrained rows.

Source: Aschbacher--Smith, proof of Proposition 7.7.3 after Lemma 7.7.10,
printed p.709, refs/quasithin.pdf. The other constrained rows, ambient
containment and full non-FF doubled contradiction remain to be proved.
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

/-- The actual residual four-space excludes the ordinary A₇ and binary G₂
blocks, retaining its embedding, original Sylow index and quotient data. -/
theorem sourceOrbit_binary_pairedPlane_sixSpace_exclusions
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
                  (T : Subgroup G) ⊓ centralizer (U : Set G) ∧
                  (Q.subgroupOf H).relIndex (P : Subgroup H) = 2) ∧
                let C₀ := C.map H.subtype
                let M₀ := H ⊓ normalizer (L : Set G)
                Input KnownSimple.IsKnownSimple H Q M₀ C₀ ∧
                ¬ ChapterC.IsAlternatingBlock C₀ 5 ∧
                ¬ Chapter1.IsSylowIn 2 Q (C₀ ⊔ Q) ∧
                (localResidual L U).subgroupOf H ≤ C ∧ C.Normal ∧
                H = C₀ ⊔ ((T : Subgroup G) ⊓ centralizer (U : Set G)) ∧
                (ChapterC.IsShort C → 16 < Nat.card (ChapterC.BlockModule C)) ∧
                (ChapterC.IsShort C →
                  let X := (⁅D.sourceOrbit.subgroupOf H,
                    (localResidual L U).subgroupOf H⁆).subgroupOf C
                  ⁅D.sourceOrbit.subgroupOf H,(localResidual L U).subgroupOf H⁆ ≤ C ∧
                  X ≤ ChapterC.blockU C ∧ Disjoint X (center C) ∧
                    Nat.card X = 16 ∧
                    X ≤ centralizer (((Q.subgroupOf H).subgroupOf C) : Set C)) ∧
                ¬ ChapterC.IsAlternatingBlock C 7 ∧
                ¬ ChapterC.IsG2TwoBlock C ∧
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
    D.sourceOrbit_binary_pairedPlane_large_block_module h hd hnon F hF hmodel
  refine ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hmark,hbase,hcore,?_⟩
  dsimp only
  intro hout
  obtain ⟨H,hH,hHC,hWY,hred,C,hC,hCimage,hCM,hLC,⟨P,hP⟩,
    hi,hno,hnotSylow,hAC,hnormal,hgen,hlarge,hnoA7,hnoA6,hnoL3,hnoL4,hcoreImage,hmove,hrest⟩ := hescape hout
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
  have hmodule (hb : ChapterC.IsShort C) :
      ⁅W,A⁆ ≤ C ∧ (⁅W,A⁆).subgroupOf C ≤ ChapterC.blockU C ∧
        Disjoint ((⁅W,A⁆).subgroupOf C) (center C) ∧
        Nat.card ((⁅W,A⁆).subgroupOf C) = 16 ∧
        (⁅W,A⁆).subgroupOf C ≤ centralizer (((Q.subgroupOf H).subgroupOf C) : Set C) := by
    obtain ⟨hDU,hDZ,hDC⟩ := DoubledBinarySmallBlocks.residual_block_embedding W A C hC.subnormal hb
      hWcore hAC (hAB.trans hBW) hsplit
    refine ⟨hDC,hDU,hDZ,(Nat.card_congr (subgroupOfEquivOfLe hDC).toEquiv).trans hcard,?_⟩
    intro d hd q hq
    apply Subtype.ext
    apply Subtype.ext
    have hdW : ((d : H) : G) ∈ D.sourceOrbit :=
      (le_normalizer_iff_commutator_le_left.mp (hAB.trans hBW)) hd
    have hqQ : ((q : H) : G) ∈ Q := hq
    have hc : ((q : H) : G) ∈ centralizer (D.sourceOrbit : Set G) :=
      (hQeq.symm ▸ hqQ).2
    exact (hc d hdW).symm
  have hnoSeven : ¬ ChapterC.IsAlternatingBlock C 7 := by
    intro hb
    obtain ⟨_,hDU,hDZ,hDcard,hDQ⟩ := hmodule hb.2.1
    obtain ⟨S,hS⟩ := P.exists_subgroupOf_eq_of_subnormal C hC.subnormal
    have hiS : ((Q.subgroupOf H).subgroupOf C).relIndex (S : Subgroup C) ≤ 2 := by
      rw [hS,←inf_subgroupOf_right (P : Subgroup H) C,
        relIndex_subgroupOf (show (P : Subgroup H) ⊓ C ≤ C from inf_le_right)]
      exact (relIndex_le_of_le_right inf_le_left index_ne_zero_of_finite).trans hindex.le
    have hbound := DoubledBinarySixSpaceBlocks.seven_block_fixed_card hb S
      ((Q.subgroupOf H).subgroupOf C) ((⁅W,A⁆).subgroupOf C) hiS hDU hDZ hDQ
    rw [hDcard] at hbound
    omega
  have hnoG2 : ¬ ChapterC.IsG2TwoBlock C := by
    intro hb
    obtain ⟨hXC,hDU,hDZ,_,_⟩ := hmodule hb.1
    let X := ⁅W,A⁆
    have hXW : X ≤ W := le_normalizer_iff_commutator_le_left.mp (hAB.trans hBW)
    let : IsElementaryAbelian 2 X := IsElementaryAbelian.of_injective
      (inclusion hXW) (inclusion_injective hXW)
    have hmap : X.map H.subtype = ⁅D.sourceOrbit,localResidual L U⁆ := by
      rw [map_commutator,map_subgroupOf_eq_of_le hWH,map_subgroupOf_eq_of_le hAH]
    have hn : R ≤ normalizer ((⁅D.sourceOrbit,localResidual L U⁆ : Subgroup G) : Set G) :=
      DoubledBinarySylowFixed.localSylow_normalizes_movement
        D.sourceOrbit L (T : Subgroup G) U D.sylow_normalizes_component
        D.sourceOrbit_weakClosure_setup.normalizes
    have hPX : (P : Subgroup H) ≤ normalizer (X : Set H) := by
      have hXpre : X = (⁅D.sourceOrbit,localResidual L U⁆).comap H.subtype := by
        rw [←hmap,comap_map_eq_self_of_injective H.subtype_injective]
      rw [hXpre]
      intro p hp
      apply le_normalizer_comap H.subtype
      have hpR := mem_map_of_mem H.subtype hp
      rw [hP] at hpR
      exact hn hpR
    have hXQ : X ≤ centralizer (Q.subgroupOf H : Set H) := by
      intro x hx q hq
      apply Subtype.ext
      have hc : ((q : H) : G) ∈ centralizer (D.sourceOrbit : Set G) :=
        (hQeq.symm ▸ (show ((q : H) : G) ∈ Q from hq)).2
      exact (hc x (hXW hx)).symm
    have hsquare := card_le_centralizer_card_sq_of_relIndex_two X (Q.subgroupOf H)
      (P : Subgroup H) hPX hXQ hindex
    have hXcard : Nat.card X = 16 := hcard
    rw [hXcard] at hsquare
    change 16 ≤ Nat.card ((centralizer (P : Set H)).subgroupOf X) ^ 2 at hsquare
    let Z := X ⊓ centralizer (P : Set H)
    have hZcard : 4 ≤ Nat.card Z := by
      have he : ((centralizer (P : Set H)).subgroupOf X).map X.subtype = Z := by
        rw [subgroupOf_map_subtype,inf_comm]
      rw [←card_map_of_injective X.subtype_injective,he] at hsquare
      nlinarith
    have hZC : Z ≤ C := inf_le_left.trans hXC
    obtain ⟨S,hS⟩ := P.exists_subgroupOf_eq_of_subnormal C hC.subnormal
    have hZS : Z.subgroupOf C ≤ centralizer (S : Set C) := by
      intro z hz s hs
      apply Subtype.ext
      have hsP : (s : H) ∈ (P : Subgroup H) := by
        change s ∈ (S : Subgroup C) at hs
        rw [hS] at hs
        exact hs
      exact hz.2 s hsP
    have hbound := DoubledBinarySixSpaceBlocks.g2_block_sylow_fixed_card hb S (Z.subgroupOf C)
      ((comap_mono (show Z ≤ X from inf_le_left)).trans hDU)
      (hDZ.mono_left (comap_mono (show Z ≤ X from inf_le_left))) hZS
    rw [Nat.card_congr (subgroupOfEquivOfLe hZC).toEquiv] at hbound
    omega
  exact ⟨H,hH,hHC,hWY,hred,C,hC,hCimage,hCM,hLC,⟨P,hP,hindex⟩,
    hi,hno,hnotSylow,hAC,hnormal,hgen,hlarge,hmodule,hnoSeven,hnoG2,hnoA7,hnoA6,hnoL3,hnoL4,hcoreImage,hmove,hrest⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
