module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.AugmentationFullImage
public import CFSG.Quasithin.ChapterC.Section01.AugmentationSixControl.Baumann
public import Theory.GroupTheory.CentralizerInjectiveImage

/-!
# Baumann kernel saturation for the actual doubled component

A full augmentation image in the original LT action supplies
B.2.19's literal mixed-plane family. Its conclusion puts O₂(L) in the
original Baumann subgroup and identifies its V-centralizer with that of
L Baum(R). The source L is proved to be O²(LT); all subgroup transports
use the actual embeddings, with no containing-component premise.

This is the kernel-Sylow step of C.1.37. The original doubled-natural
specialization is retained; AugmentationAlternative applies the general
form to obtain shortness from the independent natural large-distance input.
Final discharge remains with qt-d-1341-nonsolvable-source, along with the remaining module
rows, reciprocal comparison, commutators and graph argument. Universal
nonsolvability remains required at both escaping weights.

Source: Aschbacher–Smith B.2.19, pp.81–82; C.1.37, pp.142–143;
13.4.10(4), p.909.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section08.TransvectionRecognition.Component.ModelExtension
open Theory.SpecificGroups.SymmetricSix.BinaryFlags (pointCore)
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Full augmentation point images give kernel saturation on the literal LB,
without any containing-component or doubled-module hypothesis. -/
theorem ordinary_augmentation_full_baumann_kernel
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
    sup_le D.normalizes (((structural G T L h).2.2 V D).1)
  let : U.Normal := normal_subgroupOf_of_le_normalizer hXV
  let : IsElementaryAbelian 2 U := by
    let := D.elementary
    exact IsElementaryAbelian.subgroupOf hVX
  let eu : U ≃* V := subgroupOfEquivOfLe hVX
  let ei := eu.trans m.coordinate
  obtain ⟨q0,hq0,_,him,hker⟩ := exists_core_product_permutation D m h structural eL
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

/-- The original doubled-component specialization. -/
theorem ordinary_doubled_baumann_kernel
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
    let R := (Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G)).pCoreIn 2
    L.pCoreIn 2 ≤ ChapterB.baumann R ∧
      ChapterB.baumann R ⊓ centralizer (V : Set G) =
        (L ⊔ ChapterB.baumann R) ⊓ centralizer (V : Set G) := by
  exact ordinary_augmentation_full_baumann_kernel h structural D m eL z hzT hzL q hq
    (ordinary_doubled_baumann_full_image h₀ h structural D m eL z hzT hzL
      hKz hHN hTK hKM eK e he q hq)

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
