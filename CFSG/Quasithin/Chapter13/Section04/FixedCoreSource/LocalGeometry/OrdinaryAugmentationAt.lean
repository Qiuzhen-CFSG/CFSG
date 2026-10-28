module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NormalizerAt
public import CFSG.Quasithin.Chapter1.Section02.Adequate.Families
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.AugmentationPoint
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricSix.CoreBaumann
public import CFSG.Quasithin.ChapterB.Section03.Offenders.SixCorePointImages
public import CFSG.Quasithin.ChapterC.Section01.AugmentationSixControl.Baumann
public import Theory.GroupTheory.CentralizerInjectiveImage
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import Theory.GroupTheory.CComponent.Basic

/-!
# Ordinary augmentation control from the structural theorem at G,T

The actual LT permutation action has kernel O2(LT). Transporting its point
radical identifies all three possible Baumann images. Small images give
normalizer control or shortness; the full image puts O2(L) in Baum(R) and
identifies the full V-centralizer there. The literal R is O2(L1T), and
L1 is the prime-to-three residual of the original point centralizer.

These proofs adapt the existing augmentation arguments through their
entire structural dependency: normalizer uniqueness and module invariance
are invoked only at the same G,T with Hypothesis1223 T L. No universal
Structural1222 record is constructed. OrdinaryBaumannAt consumes all four
results in the source alternative used by ordinary normalizer fusion.
The original five-dimensional marking, ordinary quotient and both weights
are retained; this does not assert the ordinary quotient in the covered row.

Source: Aschbacher--Smith B.2.19, C.1.37, 13.2.2(6--7),
printed pp.81--82,142--143,877--878.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Nonsolvable Solvable
open Section08.TransvectionRecognition.Component.ModelExtension
open Theory.SpecificGroups.SymmetricSix.BinaryFlags (pointCore)
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The ordinary row gives the actual LT action with precisely its two-core
as kernel, while retaining the original augmentation coordinates. -/
theorem exists_core_product_permutation_at
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) :
    let X := L ⊔ (T : Subgroup G)
    ∃ q : X →* Equiv.Perm (Fin 6),
      (∀ (x : X) (v : V),
        (m.coordinate (V.normalizerMonoidHom
          ⟨x.val,(sup_le D.normalizes ((structural L h).2.2 V D).1) x.property⟩ v)).toAdd =
          BinaryPermutation.coreRepresentation (Fin 6) (q x) (m.coordinate v).toAdd) ∧
      (∀ l : L, q (inclusion le_sup_left l) =
        (m.quotient (QuotientGroup.mk' (centralCore L) l)).val) ∧
      (L.subgroupOf X).map q = alternatingGroup (Fin 6) ∧
      q.ker = pCore 2 X := by
  let X := L ⊔ (T : Subgroup G)
  have hn := normalizer_component_le_module_at h structural D m
  obtain ⟨q,hq,hqL,hker⟩ := exists_core_normalizer_permutation D m hn
  have hXN : X ≤ normalizer (L : Set G) := sup_le L.le_normalizer D.sylow_normalizes_component
  let f := q.comp (inclusion hXN)
  have hfL (l : L) : f (inclusion (show L ≤ X from le_sup_left) l) =
      (m.quotient (QuotientGroup.mk' (centralCore L) l)).val := hqL l
  let N := L.subgroupOf X
  have him : N.map f = alternatingGroup (Fin 6) := by
    apply le_antisymm
    · rintro a ⟨x,hx,rfl⟩
      have hh := hfL ⟨x.val,hx⟩
      change f x = _ at hh
      rw [hh]
      exact (m.quotient (QuotientGroup.mk' (centralCore L) ⟨x.val,hx⟩)).property
    · intro a ha
      obtain ⟨w,hw⟩ := m.quotient.surjective ⟨a,ha⟩
      obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (centralCore L) w
      exact ⟨inclusion le_sup_left l,l.property,(hfL l).trans (congrArg Subtype.val hw)⟩
  let : N.Normal := normal_subgroupOf_of_le_normalizer hXN
  have hquot : IsPGroup 2 (X ⧸ N) := by
    apply isPGroup_quotient_of_sup_eq_top N ((T : Subgroup G).subgroupOf X) T.isPGroup'.comap_subtype
    rw [←subgroupOf_sup (show L ≤ X from le_sup_left) (show (T : Subgroup G) ≤ X from le_sup_right),subgroupOf_self]
  have hfP : IsPGroup 2 f.ker := by
    apply MonoidHom.isPGroup_ker_of_card_image_eq_core_quotient f N hquot
    rw [him]
    let c : N ≃* L := subgroupOfEquivOfLe (show L ≤ X from le_sup_left)
    let cq : N ⧸ pCore 2 N ≃* L ⧸ pCore 2 L :=
      QuotientGroup.congr _ _ c (pCore_map_iso 2 c)
    exact (Nat.card_congr (cq.trans eL).toEquiv).symm
  refine ⟨f,?_,hfL,him,le_antisymm (le_sSup ⟨inferInstance,hfP⟩) ?_⟩
  · intro x v
    exact hq (inclusion hXN x) v
  · intro x hx
    have hxC : x.val ∈ centralizer (V : Set G) :=
      D.core_centralizes (mem_map.mpr ⟨x,hx,rfl⟩)
    change q (inclusion hXN x) = 1
    change inclusion hXN x ∈ q.ker
    rw [hker]
    exact hxC

/-- The two small Baumann images in the original augmentation action give
the source normalizer bound or a short block, with literal point radical. -/
theorem ordinary_augmentation_small_baumann_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (q : (L ⊔ (T : Subgroup G) : Subgroup G) →* Equiv.Perm (Fin 6))
    (hq : ∀ (x : (L ⊔ (T : Subgroup G) : Subgroup G)) (v : V),
      (m.coordinate (V.normalizerMonoidHom
        ⟨x.val,(sup_le D.normalizes ((structural L h).2.2 V D).1) x.property⟩ v)).toAdd =
        BinaryPermutation.coreRepresentation (Fin 6) (q x) (m.coordinate v).toAdd)
    (hsmall : let X := L ⊔ (T : Subgroup G)
      let R := (Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G)).pCoreIn 2
      ((ChapterB.baumann R).subgroupOf X).map q = ⊥ ∨
        ∃ r : Equiv.Perm (Fin 6), r.IsSwap ∧
          ((ChapterB.baumann R).subgroupOf X).map q = zpowers r) :
    let R := (Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G)).pCoreIn 2
    normalizer (ChapterB.baumann R : Set G) ≤ normalizer (L : Set G) ∨ ChapterC.IsShort L := by
  let X := L ⊔ (T : Subgroup G)
  let P := Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G)
  let R := P.pCoreIn 2
  let Li := L.subgroupOf X
  let Ui := V.subgroupOf X
  let Ri := R.subgroupOf X
  let B := ChapterB.baumann Ri
  have hLX : L ≤ X := le_sup_left
  have hVX : V ≤ X := D.le_sylow.trans le_sup_right
  have hPX : P ≤ X := (ordinary_augmentation_point_parabolic D m eL z hzT hzL).le.trans inf_le_left
  have hRX : R ≤ X := (pCoreIn_le 2 P).trans hPX
  have hXV : X ≤ normalizer (V : Set G) :=
    sup_le D.normalizes ((structural L h).2.2 V D).1
  let : Li.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  let : Ui.Normal := normal_subgroupOf_of_le_normalizer hXV
  let := D.elementary
  let : IsElementaryAbelian 2 Ui := IsElementaryAbelian.subgroupOf hVX
  let ek : Li ≃* L := subgroupOfEquivOfLe hLX
  let eu : Ui ≃* V := subgroupOfEquivOfLe hVX
  let e := eu.trans m.coordinate
  have he (x : X) (v : Ui) : (e (MulAut.conjNormal x v)).toAdd =
      BinaryPermutation.coreRepresentation (Fin 6) (q x) (e v).toAdd := hq x (eu v)
  obtain ⟨q0,hq0,_,hLq,hker⟩ := exists_core_product_permutation_at D m h structural eL
  have hqq : q = q0 := by
    apply MonoidHom.ext
    intro x
    apply BinaryPermutation.SixCoreNormalizer.action_injective
    apply LinearMap.ext
    intro w
    obtain ⟨v,rfl⟩ := m.coordinate.surjective (Multiplicative.ofAdd w)
    exact (hq x v).symm.trans (hq0 x v)
  subst q0
  have hC : centralizer (Ui : Set X) = pCore 2 X :=
    (ChapterB.Offenders.SixCorePoint.kernel_centralizer Ui q e he).symm.trans hker
  have hUQ : Ui ≤ pCore 2 X := le_sSup ⟨inferInstance,IsElementaryAbelian.isPGroup 2 Ui⟩
  have hf : generalizedFitting X = pCore 2 X :=
    generalizedFitting_eq_pCore_of_selfCentralizing 2 ((centralizer_le hUQ).trans hC.le)
  have hcmp : Li.IsCComponent := h.maximal_faithful.1.1.1
  let : IsQuasisimple (L ⧸ pCore 2 L) := h.quasisimple
  let : IsQuasisimple (Li ⧸ pCore 2 Li) :=
    IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ ek (pCore_map_iso 2 ek)).symm
  have hfL : generalizedFitting Li = pCore 2 Li := by
    apply map_injective (f := ek.toMonoidHom) ek.injective
    rw [map_generalizedFitting_equiv,pCore_map_iso]
    exact generalizedFitting_eq_pCore_of_selfCentralizing 2
      (Chapter1.Section02.Adequate.mem_L_hasCharacteristicTwo T
        (h.simpleQTKE.evenCharacteristic T) h.maximal_faithful.1.1)
  have hQP : X.pCoreIn 2 ≤ P := by
    change X.pCoreIn 2 ≤ Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G)
    rw [ordinary_augmentation_point_parabolic D m eL z hzT hzL]
    exact le_inf (pCoreIn_le 2 X) (D.core_centralizes.trans
      (centralizer_le (Set.singleton_subset_iff.mpr z.property)))
  have hQR : X.pCoreIn 2 ≤ R := le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 X) hQP
    (hPX.trans (X.le_normalizer.trans (normalizer_le_normalizer_characteristic_image X (pCore 2 X))))
  have hQRi : pCore 2 X ≤ Ri := fun x hx => hQR (mem_map_of_mem X.subtype hx)
  have hTP : (T : Subgroup G) ≤ P := le_sup_right
  have hRT : R ≤ T := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTP] using
      pCoreIn_le_sylow P (T.subtype hTP)
  have hRiT : Ri ≤ (T.subtype (show (T : Subgroup G) ≤ X from le_sup_right) : Subgroup X) := by
    rw [Sylow.coe_subtype]
    exact comap_mono hRT
  have hprod (x : X) : ∃ l ∈ Li, ∃ t ∈
      (T.subtype (show (T : Subgroup G) ≤ X from le_sup_right) : Subgroup X), l*t=x := by
    apply mem_sup_of_normal_left.mp
    rw [Sylow.coe_subtype,←subgroupOf_sup hLX (show (T : Subgroup G) ≤ X from le_sup_right),subgroupOf_self]
    exact mem_top x
  have hm : ⁅Ui,Li⁆ ≠ ⊥ := by
    intro hb
    have hh := congrArg (map X.subtype) hb
    rw [map_commutator,map_subgroupOf_eq_of_le hVX,map_subgroupOf_eq_of_le hLX,Subgroup.map_bot] at hh
    exact D.ne_bot (D.eq_commutator.trans hh)
  have hBm : B.map X.subtype = ChapterB.baumann R := by
    rw [ChapterC.RankOne.SymmetricSix.baumann_map X X.subtype X.subtype_injective Ri,
      map_subgroupOf_eq_of_le hRX]
  have hBi : B = (ChapterB.baumann R).subgroupOf X := by
    rw [←hBm]
    ext x
    exact (mem_map_iff_mem X.subtype_injective).symm
  have hs : B.map q = ⊥ ∨ ∃ r : Equiv.Perm (Fin 6), r.IsSwap ∧ B.map q = zpowers r := by
    rw [hBi]
    exact hsmall
  rcases ChapterC.RankOne.SymmetricSix.normal_characteristic_or_block_of_small_core_baumann
    Li Ui Ri hcmp hf hfL (T.subtype le_sup_right) hQRi hRiT hprod q hLq hker e he hm hs with
    ⟨C,hC,hCn,hCN⟩ | hb
  · left
    let := hC
    let N := (C.map B.subtype).map X.subtype
    have hn : N ≠ ⊥ := by
      intro hh
      exact hCn ((C.map_eq_bot_iff_of_injective B.subtype_injective).mp
        (((C.map B.subtype).map_eq_bot_iff_of_injective X.subtype_injective).mp hh))
    have hp : IsPGroup 2 N := ((((isPGroup_pCoreIn 2 P).comap_subtype).to_le
      (show B ≤ Ri from inf_le_left)).to_subgroup C).map B.subtype |>.map X.subtype
    have hXN : X ≤ normalizer (N : Set G) := by
      apply le_normalizer_iff.mpr
      intro x hx n hn
      obtain ⟨v,hv,rfl⟩ := hn
      exact mem_map_of_mem X.subtype (hCN.conj_mem v hv ⟨x,hx⟩)
    have hNM : normalizer (N : Set G) ≤ normalizer (L : Set G) :=
      normalizer_le_of_unique_maximalTwoLocal
        (h.source_normalizer_maximal_unique_at structural
          (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
          (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)).2 hp hn hXN
    rw [←hBm]
    exact (normalizer_le_normalizer_characteristic_map X.subtype X.subtype_injective B C).trans hNM
  · exact Or.inr (hb.short.of_mulEquiv ek)

/-- The full augmentation image trichotomy on the literal original O₂(L₁T),
with the same marking and either nonconstant weight. -/
theorem ordinary_augmentation_baumann_images_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (q : (L ⊔ (T : Subgroup G) : Subgroup G) →* Equiv.Perm (Fin 6))
    (hq : ∀ (x : (L ⊔ (T : Subgroup G) : Subgroup G)) (v : V),
      (m.coordinate (V.normalizerMonoidHom
        ⟨x.val,(sup_le D.normalizes ((structural L h).2.2 V D).1) x.property⟩ v)).toAdd =
        BinaryPermutation.coreRepresentation (Fin 6) (q x) (m.coordinate v).toAdd) :
    let X := L ⊔ (T : Subgroup G)
    let R := (Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G)).pCoreIn 2
    (((ChapterB.baumann R).subgroupOf X).map q = ⊥ ∨
      ∃ r : Equiv.Perm (Fin 6), r.IsSwap ∧
        ((ChapterB.baumann R).subgroupOf X).map q = zpowers r) ∨
      (Function.Surjective q ∧ ∃ a : alternatingGroup (Fin 6),
        ((elementaryAbelianMaxJ R).subgroupOf X).map q = pointCore.map (MulAut.conj a.val).toMonoidHom ∧
        ((ChapterB.baumann R).subgroupOf X).map q = pointCore.map (MulAut.conj a.val).toMonoidHom ∧
        (R.subgroupOf X).map q = pointCore.map (MulAut.conj a.val).toMonoidHom) := by
  let X := L ⊔ (T : Subgroup G)
  let U := V.subgroupOf X
  let R := (Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G)).pCoreIn 2
  have hVX : V ≤ X := D.le_sylow.trans le_sup_right
  have hXV : X ≤ normalizer (V : Set G) :=
    sup_le D.normalizes (((structural L h).2.2 V D).1)
  let : U.Normal := normal_subgroupOf_of_le_normalizer hXV
  let : IsElementaryAbelian 2 U := by
    let := D.elementary
    exact IsElementaryAbelian.subgroupOf hVX
  let eu : U ≃* V := subgroupOfEquivOfLe hVX
  let e := eu.trans m.coordinate
  let zi : U := eu.symm z
  obtain ⟨q0,hq0,_,him,hker⟩ := exists_core_product_permutation_at D m h structural eL
  have hqq : q = q0 := by
    apply MonoidHom.ext
    intro x
    apply BinaryPermutation.SixCoreNormalizer.action_injective
    apply LinearMap.ext
    intro w
    obtain ⟨v,rfl⟩ := m.coordinate.surjective (Multiplicative.ofAdd w)
    exact (hq x v).symm.trans (hq0 x v)
  subst q0
  have he (x : X) (v : U) : (e (MulAut.conjNormal x v)).toAdd =
      BinaryPermutation.coreRepresentation (Fin 6) (q x) (e v).toAdd := hq x (eu v)
  have hY : alternatingGroup (Fin 6) ≤ q.range := by
    rw [←him]
    exact (L.subgroupOf X).map_le_range q
  have hz : ¬ ∀ a : alternatingGroup (Fin 6),
      BinaryPermutation.alternatingCoreRepresentation (Fin 6) a (e zi).toAdd = (e zi).toAdd := by
    intro hz
    apply hzL
    apply (m.mem_fixed_iff z).mpr
    apply (BinaryPermutation.core_fixed_iff_constant (by simp) _).mp
    change ∀ a : alternatingGroup (Fin 6),
      BinaryPermutation.coreRepresentation (Fin 6) a.val (e zi).toAdd = (e zi).toAdd at hz
    simpa only [e,zi,MulEquiv.trans_apply,eu.apply_symm_apply] using hz
  let C : Subgroup X := centralizer ({zi.val} : Set X)
  have hCm : C.map X.subtype = Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G) := by
    rw [ordinary_augmentation_point_parabolic D m eL z hzT hzL]
    ext x
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ⟨a.property,mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp ha))⟩
    · rintro ⟨hx,hz⟩
      exact ⟨⟨x,hx⟩,mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp hz)),rfl⟩
  have hRm : (C.pCoreIn 2).map X.subtype = R := by
    rw [map_pCoreIn_of_injective 2 _ _ X.subtype_injective,hCm]
  have hRi : C.pCoreIn 2 = R.subgroupOf X := by
    rw [←hRm]
    ext x
    exact (mem_map_iff_mem X.subtype_injective).symm
  have hJ : elementaryAbelianMaxJ (C.pCoreIn 2) = (elementaryAbelianMaxJ R).subgroupOf X := by
    have hm : (elementaryAbelianMaxJ (C.pCoreIn 2)).map X.subtype = elementaryAbelianMaxJ R := by
      rw [←elementaryAbelianMaxJ_map_injective X.subtype X.subtype_injective,hRm]
    rw [←hm]
    ext x
    exact (mem_map_iff_mem X.subtype_injective).symm
  have hB : ChapterB.baumann (C.pCoreIn 2) = (ChapterB.baumann R).subgroupOf X := by
    have hm : (ChapterB.baumann (C.pCoreIn 2)).map X.subtype = ChapterB.baumann R := by
      rw [ChapterC.RankOne.SymmetricSix.baumann_map X X.subtype X.subtype_injective,hRm]
    rw [←hm]
    ext x
    exact (mem_map_iff_mem X.subtype_injective).symm
  have hh := ChapterB.Offenders.SixCorePoint.point_baumann_alternative U q e he hker hY zi hz
  change ((ChapterB.baumann (C.pCoreIn 2)).map q = ⊥ ∨ _) ∨ _ at hh
  rw [hB,hJ,hRi] at hh
  exact hh

/-- Full augmentation point images give kernel saturation on the literal LB,
without any containing-component or doubled-module hypothesis. -/
theorem ordinary_augmentation_full_baumann_kernel_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (q : (L ⊔ (T : Subgroup G) : Subgroup G) →* Equiv.Perm (Fin 6))
    (hq : ∀ (x : (L ⊔ (T : Subgroup G) : Subgroup G)) (v : V),
      (m.coordinate (V.normalizerMonoidHom
        ⟨x.val,(sup_le D.normalizes ((structural L h).2.2 V D).1) x.property⟩ v)).toAdd =
        BinaryPermutation.coreRepresentation (Fin 6) (q x) (m.coordinate v).toAdd)
    (hfull : let X := L ⊔ (T : Subgroup G)
    let R := (Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G)).pCoreIn 2
    Function.Surjective q ∧ ∃ a : alternatingGroup (Fin 6),
      ((elementaryAbelianMaxJ R).subgroupOf X).map q = pointCore.map (MulAut.conj a.val).toMonoidHom ∧
      ((ChapterB.baumann R).subgroupOf X).map q = pointCore.map (MulAut.conj a.val).toMonoidHom ∧
      (R.subgroupOf X).map q = pointCore.map (MulAut.conj a.val).toMonoidHom) :
    let R := (Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G)).pCoreIn 2
    L.pCoreIn 2 ≤ ChapterB.baumann R ∧
      ChapterB.baumann R ⊓ centralizer (V : Set G) =
        (L ⊔ ChapterB.baumann R) ⊓ centralizer (V : Set G) := by
  obtain ⟨hqsur,a,hJfull,hBfull,hRfull⟩ := hfull
  let X := L ⊔ (T : Subgroup G)
  let U := V.subgroupOf X
  let R := (Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G)).pCoreIn 2
  have hVX : V ≤ X := D.le_sylow.trans le_sup_right
  have hXV : X ≤ normalizer (V : Set G) :=
    sup_le D.normalizes (((structural L h).2.2 V D).1)
  let : U.Normal := normal_subgroupOf_of_le_normalizer hXV
  let : IsElementaryAbelian 2 U := by
    let := D.elementary
    exact IsElementaryAbelian.subgroupOf hVX
  let eu : U ≃* V := subgroupOfEquivOfLe hVX
  let ei := eu.trans m.coordinate
  obtain ⟨q0,hq0,_,him,hker⟩ := exists_core_product_permutation_at D m h structural eL
  have hqq : q = q0 := by
    apply MonoidHom.ext
    intro x
    apply BinaryPermutation.SixCoreNormalizer.action_injective
    apply LinearMap.ext
    intro w
    obtain ⟨v,rfl⟩ := m.coordinate.surjective (Multiplicative.ofAdd w)
    exact (hq x v).symm.trans (hq0 x v)
  subst q0
  have hei (x : X) (v : U) : (ei (MulAut.conjNormal x v)).toAdd =
      BinaryPermutation.coreRepresentation (Fin 6) (q x) (ei v).toAdd := hq x (eu v)
  let Li := L.subgroupOf X
  let Ri := R.subgroupOf X
  have hLX : L ≤ X := le_sup_left
  have hPX : Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G) ≤ X :=
    (ordinary_augmentation_point_parabolic D m eL z hzT hzL).le.trans inf_le_left
  have hRX : R ≤ X := (pCoreIn_le 2 _).trans hPX
  have hQR : X.pCoreIn 2 ≤ R := by
    apply le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 X)
    · rw [ordinary_augmentation_point_parabolic D m eL z hzT hzL]
      exact le_inf (pCoreIn_le 2 X) (D.core_centralizes.trans
        (centralizer_le (Set.singleton_subset_iff.mpr z.property)))
    · exact hPX.trans (X.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image X (pCore 2 X)))
  have hQRi : pCore 2 X ≤ Ri := fun x hx => hQR (mem_map_of_mem X.subtype hx)
  have hJmap : (elementaryAbelianMaxJ Ri).map X.subtype = elementaryAbelianMaxJ R := by
    rw [←elementaryAbelianMaxJ_map_injective X.subtype X.subtype_injective,
      map_subgroupOf_eq_of_le hRX]
  have hJi : elementaryAbelianMaxJ Ri = (elementaryAbelianMaxJ R).subgroupOf X := by
    rw [←hJmap]
    ext x
    exact (mem_map_iff_mem X.subtype_injective).symm
  have hRi : Ri.map q = pointCore.map (MulAut.conj a.val).toMonoidHom := hRfull
  have hj : (elementaryAbelianMaxJ Ri).map q = Ri.map q := by
    rw [hJi]
    exact hJfull.trans hRfull.symm
  have hb := ChapterC.AugmentationSixControl.conjugate_point_baumann U Ri q hqsur hker hQRi
    ei hei a hRi hj
  let : Li.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  have hcmp : Li.IsCComponent := h.maximal_faithful.1.1.1
  let : Group.IsPerfect Li := hcmp.perfect
  have hpL : IsPPerfect 2 Li := by
    intro N hn hquot
    let : N.Normal := hn
    by_contra hne
    let : Nontrivial (Li ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
    let : Group.IsPerfect (Li ⧸ N) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
    let : Group.IsNilpotent (Li ⧸ N) := hquot.isNilpotent
    exact Group.IsPerfect.not_isSolvable (Li ⧸ N) inferInstance
  let Ti := T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)
  have hprod (x : X) : ∃ l ∈ Li, ∃ t ∈ (Ti : Subgroup X), l*t=x := by
    apply mem_sup_of_normal_left.mp
    rw [Sylow.coe_subtype,←subgroupOf_sup hLX (show (T : Subgroup G) ≤ X from le_sup_right),subgroupOf_self]
    exact mem_top x
  have hres : pResidual 2 X = Li := pResidual_eq_of_subnormal_product
    Li (Ti : Subgroup X) hcmp.subnormal hpL Ti.isPGroup' hprod
  rw [hres] at hb
  have hLm : Li.map X.subtype = L := map_subgroupOf_eq_of_le hLX
  have hBm : (ChapterB.baumann Ri).map X.subtype = ChapterB.baumann R := by
    rw [ChapterC.RankOne.SymmetricSix.baumann_map X X.subtype X.subtype_injective,
      map_subgroupOf_eq_of_le hRX]
  constructor
  · have hh := map_mono (f := X.subtype) hb.1
    rw [map_pCoreIn_of_injective 2 Li X.subtype X.subtype_injective,hLm,hBm] at hh
    exact hh
  · have hh := congrArg (map X.subtype) hb.2.2
    rw [←map_inf_centralizer_of_injective X.subtype X.subtype_injective,
      ←map_inf_centralizer_of_injective X.subtype X.subtype_injective,
      map_subgroupOf_eq_of_le hVX,Subgroup.map_sup,hLm,hBm] at hh
    exact hh

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
