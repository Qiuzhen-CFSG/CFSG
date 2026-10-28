module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricSix.CoreBaumann
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.AugmentationPoint
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentRadicalBaumann
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import Theory.GroupTheory.CComponent.Basic

/-!
# The small augmentation Baumann branches on the original component

The original five-dimensional marking determines the permutation action of LT
uniquely, with kernel O₂(LT). Transport the literal R=O₂(L₁T) into LT and
apply the augmentation cubic-seed theorem. A characteristic subgroup normal
in LT gives the ambient Baumann-normalizer bound by maximal two-local
uniqueness; the other branch gives shortness of the actual original L.

For the selected doubled-natural component, the previously proved Baumann
normalizer escape excludes the first alternative. The original five-space
chief-factor budget excludes the second. Thus the Baumann image of this
actual point radical is neither trivial nor a transposition subgroup. All
fitting, component, quotient-kernel and residual-containment requirements are
discharged from the original hypotheses; no NaturalSetup is used.

This proves the two small-image branches of the augmentation alternative.
The remaining point-radical images, the full short-block alternative, other
module-row exclusions and comparison/commutator/graph assembly remain with
qt-d-1341-nonsolvable-source. Universal nonsolvability remains necessary at
both escaping weights. Earlier structural inputs retain their existing
producers and final discharge with qt-d-1341-fixed-core-source.

Source: Aschbacher–Smith13.2.2(7), pp.877–878, and13.4.10, pp.907–909.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The two small Baumann images in the original augmentation action give
the source normalizer bound or a short block, with literal point radical. -/
theorem ordinary_augmentation_small_baumann
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (q : (L ⊔ (T : Subgroup G) : Subgroup G) →* Equiv.Perm (Fin 6))
    (hq : ∀ (x : (L ⊔ (T : Subgroup G) : Subgroup G)) (v : V),
      (m.coordinate (V.normalizerMonoidHom
        ⟨x.val,(sup_le D.normalizes ((structural G T L h).2.2 V D).1) x.property⟩ v)).toAdd =
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
    sup_le D.normalizes ((structural G T L h).2.2 V D).1
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
  obtain ⟨q0,hq0,_,hLq,hker⟩ := exists_core_product_permutation D m h structural eL
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
        (h.source_normalizer_maximal_unique structural
          (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
          (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)).2 hp hn hXN
    rw [←hBm]
    exact (normalizer_le_normalizer_characteristic_map X.subtype X.subtype_injective B C).trans hNM
  · exact Or.inr (hb.short.of_mulEquiv ek)

/-- The actual doubled component excludes both small Baumann images of the
original augmentation point radical. The short-block branch is discharged
by the chief-factor comparison; no shortness or residual containment remains
as a hypothesis. -/
theorem ordinary_doubled_baumann_image_not_small
    {K : Subgroup G}
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (e : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ : Subgroup G) ≃*
      Multiplicative (BinaryLinearThree.Vector × BinaryLinearThree.Vector))
    (he : let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
      letI := conjMulDistribMulActionOfLeNormalizer K U (normalizer_commutator_ge_right _ _)
      ∀ (k : K) (v : U), (e (k • v)).toAdd =
        (Representation.prod BinaryLinearThree.W BinaryLinearThree.W)
          (eK (QuotientGroup.mk' (pCore 2 K) k)) (e v).toAdd)
    (q : (L ⊔ (T : Subgroup G) : Subgroup G) →* Equiv.Perm (Fin 6))
    (hq : ∀ (x : (L ⊔ (T : Subgroup G) : Subgroup G)) (v : V),
      (m.coordinate (V.normalizerMonoidHom
        ⟨x.val,(sup_le D.normalizes ((structural G T L h).2.2 V D).1) x.property⟩ v)).toAdd =
        BinaryPermutation.coreRepresentation (Fin 6) (q x) (m.coordinate v).toAdd) :
    let X := L ⊔ (T : Subgroup G)
    let R := (Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G)).pCoreIn 2
    ¬ (((ChapterB.baumann R).subgroupOf X).map q = ⊥ ∨
      ∃ r : Equiv.Perm (Fin 6), r.IsSwap ∧
        ((ChapterB.baumann R).subgroupOf X).map q = zpowers r) := by
  dsimp only
  intro hsmall
  have hescape := (ordinary_doubled_original_baumann h₀ h structural D m eL z hzT hzL
    hKz hHN hTK hKM eK e he).2.2
  rcases ordinary_augmentation_small_baumann h structural D m eL z hzT hzL q hq hsmall with hn | hb
  · exact hescape hn
  · exact core_block_excludes_doubled_without_containment h₀ h structural D m z hzT hzL
      hKz hHN hTK hKM hb eK e he

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
