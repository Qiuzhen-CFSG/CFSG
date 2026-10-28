module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourcePairResidual
public import Theory.ElementaryAbelian.PrimePlane

/-!
# The original barred four-group in the normal A₆ branch

The intrinsic quotient of L and its image in LT/O₂(LT) have the same
kernel O₂(L). Their induced equivalence compares every original barred
subgroup with the prescribed natural permutation map. The marked A₄
residual and even point-core computations then give the literal equality
Ū_H=O₂(L̄₁), and the order-four elementary group yields its E₄ equivalence.

The final theorem proves exactly13.5.15(2), using the original ordinary
A₆ quotient, F.9 hypothesis and13.5.7(b) seed identity. It assumes no block,
quaternion or completed13.5.15 conclusion.

Source: Aschbacher–Smith,13.5.14(2) and13.5.15(2), printed pp.919–920.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceBarred
open Section08.SourceCompletion
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open PlaneGeometry.TwoBlocks
open ChapterG.Section02.AlternatingFive
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)

theorem local_kernel_eq_core (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6)) :
    (localMap d).ker = pCore 2 D.L := by
  have hz : center (D.L ⧸ pCore 2 D.L) = ⊥ := by
    apply card_eq_one.mp
    rw [Nat.card_congr (centerCongr e).toEquiv,
      alternatingGroup.center_eq_bot (by norm_num : 4 ≤ Nat.card (Fin 6)), card_bot]
  have hc : Section08.TransvectionRecognition.Component.ModelExtension.centralCore D.L = pCore 2 D.L := by
    change (center (D.L ⧸ pCore 2 D.L)).comap (QuotientGroup.mk' (pCore 2 D.L)) = _
    rw [hz]
    exact QuotientGroup.ker_mk' _
  rw [← hc]
  ext l
  change ((d.local_quotient (QuotientGroup.mk' _ l)) : Equiv.Perm (Fin 6)) = 1 ↔ _
  constructor
  · intro hh
    have hh' : d.local_quotient (QuotientGroup.mk' _ l) = 1 := Subtype.ext hh
    exact (QuotientGroup.eq_one_iff l).mp (d.local_quotient.injective (hh'.trans (map_one _).symm))
  · intro hl
    have hh : QuotientGroup.mk' _ l = 1 := (QuotientGroup.eq_one_iff l).mpr hl
    rw [hh,map_one]
    rfl

omit d [Finite G] in
def barProjection (D : ChapterF.Section09.Setup G) : D.L →* D.g2.star D.L := starProjection D.g2

omit d [Finite G] in
theorem barProjection_surjective : Function.Surjective (barProjection D) := starProjection_surjective D.g2

omit d in
theorem starProjection_ker (h : D.Hypothesis) :
    (barProjection D).ker = pCore 2 D.L := by
  have hLT : D.L ≤ D.LT := le_sup_left
  ext l
  have he : l ∈ (barProjection D).ker ↔ (l : G) ∈ D.LT.pCoreIn 2 := by
    change barProjection D l = 1 ↔ _
    rw [Subtype.ext_iff]
    change (QuotientGroup.mk (inclusion hLT l) : D.LT ⧸ pCore 2 D.LT) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    constructor
    · intro ha
      exact ⟨_,ha,rfl⟩
    · rintro ⟨b,hb,he⟩
      exact (show b = inclusion hLT l from Subtype.ext he) ▸ hb
  rw [he]
  constructor
  · intro hl
    obtain ⟨b,hb,he⟩ := inf_pCoreIn_le_of_le 2 hLT ⟨l.property,hl⟩
    exact (show b=l from Subtype.ext he) ▸ hb
  · intro hl
    exact SourcePairResidual.local_core_le_LT_core h ⟨l,hl,rfl⟩

noncomputable def imageEquiv (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6)) :
    D.g2.star D.L ≃* (localMap d).range := by
  letI : (localMap d).ker.Normal := MonoidHom.normal_ker _
  exact (QuotientGroup.quotientKerEquivOfSurjective (barProjection D)
    (barProjection_surjective (D := D))).symm |>.trans
      ((QuotientGroup.quotientMulEquivOfEq ((starProjection_ker h).trans (local_kernel_eq_core d e).symm)).trans
        (QuotientGroup.quotientKerEquivRange (localMap d)))

theorem imageEquiv_apply (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6)) (l : D.L) :
    (imageEquiv d h e (barProjection D l)).val = localMap d l := by
  change (imageEquiv d h e ((QuotientGroup.quotientKerEquivOfSurjective (barProjection D)
    (barProjection_surjective (D := D))) (QuotientGroup.mk' _ l))).val = _
  simp only [imageEquiv,MulEquiv.trans_apply,MulEquiv.symm_apply_apply]
  rfl

noncomputable def action (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6)) :
    D.g2.star D.L →* S := (localMap d).range.subtype.comp (imageEquiv d h e).toMonoidHom

theorem action_injective (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6)) :
    Function.Injective (action d h e) :=
  (localMap d).range.subtype_injective.comp (imageEquiv d h e).injective

theorem action_image (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (A : Subgroup G) (hA : A ≤ D.L) :
    ((D.g2.star A).subgroupOf (D.g2.star D.L)).map (action d h e) =
      (A.subgroupOf D.L).map (localMap d) := by
  have hAL : A ≤ D.LT := hA.trans le_sup_left
  ext x
  constructor
  · rintro ⟨y,⟨a,ha,hay⟩,rfl⟩
    let al : D.L := ⟨a,hA ha⟩
    have he : barProjection D al = y := Subtype.ext hay
    refine ⟨al,ha,?_⟩
    rw [←he]
    exact (imageEquiv_apply d h e al).symm
  · rintro ⟨a,ha,rfl⟩
    let y := barProjection D a
    refine ⟨y,?_,imageEquiv_apply d h e a⟩
    exact ⟨⟨a,hAL ha⟩,ha,rfl⟩

include d
theorem source13_5_15_two (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
    (hU : ¬ IsMulCommutative D.UH) :
    D.g2.star D.UH = (D.g2.star D.L₁).pCoreIn 2 ∧
      Nonempty (D.g2.star D.UH ≃* FourGroup) := by
  obtain ⟨a,ha,_⟩ := QuadraticSource.source_even_flag d
  have hUL := (closure_reduction h hseed hn).2.2
  have hLL : D.L₁ ≤ D.L := (map_subtype_le _).trans inf_le_left
  have hUbar : D.g2.star D.UH ≤ D.g2.star D.L :=
    map_mono (comap_mono hUL)
  have hLbar : D.g2.star D.L₁ ≤ D.g2.star D.L :=
    map_mono (comap_mono hLL)
  let c := (MulAut.conj a.val).toMonoidHom
  have hUi : ((D.g2.star D.UH).subgroupOf (D.g2.star D.L)).map (action d h e) =
      pointCoreEven.map c := (action_image d h e D.UH hUL).trans
    (SourcePointCore.closure_image_eq_point_core d h e hseed hn hU a ha)
  have hLi : ((D.g2.star D.L₁).subgroupOf (D.g2.star D.L)).map (action d h e) =
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.K.map c :=
    (action_image d h e D.L₁ hLL).trans (SourcePointCore.local_residual_marking d h a ha)
  have hcore : ((D.g2.star D.L₁).pCoreIn 2).subgroupOf (D.g2.star D.L) =
      ((D.g2.star D.L₁).subgroupOf (D.g2.star D.L)).pCoreIn 2 := by
    apply map_injective (D.g2.star D.L).subtype_injective
    rw [map_subgroupOf_eq_of_le ((pCoreIn_le 2 _).trans hLbar),
      map_pCoreIn_of_injective 2 _ _ (D.g2.star D.L).subtype_injective,
      map_subgroupOf_eq_of_le hLbar]
  have heq : (D.g2.star D.UH).subgroupOf (D.g2.star D.L) =
      ((D.g2.star D.L₁).pCoreIn 2).subgroupOf (D.g2.star D.L) := by
    apply map_injective (action_injective d h e)
    rw [hcore,map_pCoreIn_of_injective 2 _ _ (action_injective d h e),hUi,hLi,
      ←map_pCoreIn_of_injective 2 _ _ (MulAut.conj a.val).injective,K_core_eq_pointCoreEven]
  have hu : D.g2.star D.UH = (D.g2.star D.L₁).pCoreIn 2 := by
    have hh := congrArg (Subgroup.map (D.g2.star D.L).subtype) heq
    rwa [map_subgroupOf_eq_of_le hUbar,
      map_subgroupOf_eq_of_le ((pCoreIn_le 2 _).trans hLbar)] at hh
  let E : D.g2.star D.UH ≃* pointCoreEven :=
    (subgroupOfEquivOfLe hUbar).symm |>.trans
      ((((D.g2.star D.UH).subgroupOf (D.g2.star D.L)).equivMapOfInjective
        (action d h e) (action_injective d h e)).trans
        ((MulEquiv.subgroupCongr hUi).trans ((MulAut.conj a.val).subgroupMap pointCoreEven).symm))
  let := pointCoreEven_elementary
  let ef : Additive pointCoreEven ≃ₗ[ZMod 2] (Fin 2 → ZMod 2) :=
    LinearEquiv.ofFinrankEq _ _ (by
      have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive pointCoreEven)
      rw [Nat.card_congr (Additive.ofMul : pointCoreEven ≃ Additive pointCoreEven).symm,
        pointCoreEven_card,Nat.card_zmod] at hh
      have hd : Module.finrank (ZMod 2) (Additive pointCoreEven)=2 :=
        (Nat.pow_right_injective (by decide : 2≤2)) hh.symm
      simp [hd])
  exact ⟨hu,⟨E.trans ef.toAddEquiv.toMultiplicativeRight⟩⟩

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceBarred
end
