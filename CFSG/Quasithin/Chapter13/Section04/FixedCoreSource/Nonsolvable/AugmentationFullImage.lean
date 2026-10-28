module
public import CFSG.Quasithin.ChapterB.Section03.Offenders.SixCorePointImages
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.AugmentationBaumann

/-!
# The remaining augmentation image of the actual doubled component

Transport the complete five-space Thompson/Baumann image calculation through
the original LT action and identify its radical with O₂(L₁T). The small-image
exclusions then force all three images—radical, Thompson subgroup and Baumann
subgroup—to be the same conjugate of the full order-eight duad radical.
In particular the original LT permutation action is onto S₆.

This isolates the remaining full-image Baumann argument without assuming
shortness, residual containment, a natural submodule or a split fixed line.
Both original nonconstant weights are retained. The subsequent short-block
alternative, other module rows, comparison, commutator and graph arguments
remain with qt-d-1341-nonsolvable-source. Earlier structural source premises
retain their existing producers and discharge with the final assembly owner.

Source: Aschbacher–Smith C.1.37, pp.142–143; 13.2.2(7), p.878;
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

/-- The full augmentation image trichotomy on the literal original O₂(L₁T),
with the same marking and either nonconstant weight. -/
theorem ordinary_augmentation_baumann_images
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
    sup_le D.normalizes (((structural G T L h).2.2 V D).1)
  let : U.Normal := normal_subgroupOf_of_le_normalizer hXV
  let : IsElementaryAbelian 2 U := by
    let := D.elementary
    exact IsElementaryAbelian.subgroupOf hVX
  let eu : U ≃* V := subgroupOfEquivOfLe hVX
  let e := eu.trans m.coordinate
  let zi : U := eu.symm z
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

/-- The selected doubled component forces the full point-radical image in the
original augmentation action. All small-image premises are discharged. -/
theorem ordinary_doubled_baumann_full_image
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
    Function.Surjective q ∧ ∃ a : alternatingGroup (Fin 6),
      ((elementaryAbelianMaxJ R).subgroupOf X).map q = pointCore.map (MulAut.conj a.val).toMonoidHom ∧
      ((ChapterB.baumann R).subgroupOf X).map q = pointCore.map (MulAut.conj a.val).toMonoidHom ∧
      (R.subgroupOf X).map q = pointCore.map (MulAut.conj a.val).toMonoidHom := by
  have hh := ordinary_augmentation_baumann_images h structural D m eL z hzT hzL q hq
  exact hh.resolve_left (ordinary_doubled_baumann_image_not_small h₀ h structural D m eL z hzT hzL
    hKz hHN hTK hKM eK e he q hq)

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
