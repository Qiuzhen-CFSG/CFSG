module
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.MovedFittingProduct
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingThree
public import CFSG.Quasithin.ChapterA.Section04.Intersection
public import Theory.GroupTheory.Fitting.OutsideComponent
public import Theory.GroupTheory.PRadical.NormalizerRestriction
public import Theory.GroupTheory.GeneralizedFitting.SylowOvergroup

/-!
# Characteristic control of the centralizer of all outside cubic blocks

Let N be normal and centerless and contain every moved A₃ block outside H.
Inside D=C_G(N)R, any outside factor supplied by C.2.6 is two-perfect, so
lies in C_G(N), since D/C_G(N) is a two-group. Its subnormality and movement
lift to G, placing it in N as well, a contradiction. Thus the Fitting
preimage of D lies in H. Solvable-residual control handles its components.
A.4.4 recovers O₂(D)=R from R=O₂(H), so C_G(N) normalizes R and lies in H.

Source: the exceptional control step in Aschbacher–Smith 14.1.13, p.979.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.Section02Source
variable {G : Type*} [Group G] [Finite G]

theorem centralizer_le_of_all_outside_cubic_blocks {κ : GroupClass} (hG : IsSQTK κ G)
    (hc : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (R H N : Subgroup G) [N.Normal] (hr : IsPRadical 2 R)
    (hcontrol : R.characteristicNormalizerClosure ≤ H)
    (hcore : H.pCoreIn 2 = R) (hres : solvableResidual G ≤ H)
    (hz : center N = ⊥)
    (hcover : ∀ B : Subgroup G, IsBlock B → IsAlternatingBlock B 3 →
      B = ⁅B,elementaryAbelianMaxJ R⁆ → ¬ B ≤ H → B ≤ N) :
    centralizer (N : Set G) ≤ H := by
  have hRH : R ≤ H := hcore ▸ pCoreIn_le 2 H
  have hHN : H ≤ normalizer (R : Set G) := by
    rw [←hcore]
    exact H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hNH : normalizer (R : Set G) ≤ H :=
    (normalizer_le_characteristicNormalizerClosure_self R hr.1).trans hcontrol
  let K := centralizer (N : Set G)
  let : K.Normal := inferInstance
  let D := K ⊔ R
  have hRD : R ≤ D := le_sup_right
  have hKD : K ≤ D := le_sup_left
  have hHD : H ≤ normalizer (D : Set G) :=
    (le_inf le_normalizer_of_normal hHN).trans (normalizer_inf_normalizer_le_normalizer_sup K R)
  have hrD : IsPRadical 2 (R.subgroupOf D) :=
    hr.subgroupOf_of_normalizer_normalizes D hRD (hNH.trans hHD)
  have hcD : centralizer (pCore 2 D : Set D) ≤ pCore 2 D :=
    centralizer_pCore_le_of_pCore_le D hc
      ((pCore_le_of_pCore_normalizer_le R hr.isPGroup hr.2.le).trans hRD)
  have hctlD : (R.subgroupOf D).characteristicNormalizerClosure ≤ H.subgroupOf D :=
    characteristicNormalizerClosure_subgroupOf_le hRD hcontrol
  have hfit : twoFittingCore D ≤ H.subgroupOf D := by
    obtain ⟨n,hn,B,hB,hprod⟩ := fitting_ordered_moved_product
      (hG.subgroup D) (R.subgroupOf D) (H.subgroupOf D) hrD hctlD hcD
    have hfalse (i : Fin n) : False := by
      let X := (B i).map D.subtype
      let e : B i ≃* X := equivMapOfInjective (B i) D.subtype D.subtype_injective
      have hgen : K.subgroupOf D ⊔ R.subgroupOf D = ⊤ := by
        rw [←subgroupOf_sup hKD hRD,subgroupOf_self]
      have hquot : IsPGroup 2 (D ⧸ K.subgroupOf D) :=
        isPGroup_quotient_of_sup_eq_top (K.subgroupOf D) (R.subgroupOf D)
          hr.isPGroup.comap_subtype hgen
      have hBK : B i ≤ K.subgroupOf D := by
        have ht := (hB i).2.2.1.short.twoPerfect.hom_eq_one_of_isPGroup hquot
          ((QuotientGroup.mk' (K.subgroupOf D)).comp (B i).subtype)
        intro b hb
        exact (QuotientGroup.eq_one_iff b).mp (DFunLike.congr_fun ht ⟨b,hb⟩)
      have hXK : X ≤ K := by
        rintro _ ⟨b,hb,rfl⟩
        exact hBK hb
      have hsub : (X.subgroupOf K).IsSubnormal := by
        have he : (B i).comap (inclusion hKD) = X.subgroupOf K := by
          ext x
          exact (mem_map_iff_mem D.subtype_injective).symm
        rw [←he]
        exact (hB i).2.2.1.subnormal.comap (inclusion hKD)
      have ha : IsAlternatingBlock X 3 :=
        RankOne.Solvable.isAlternatingBlock_of_equiv e (hB i).2.2.2.1
      have hb : IsBlock X := ⟨inferInstance,ha.2.1,
        Subgroup.IsSubnormal.trans hXK hsub (inferInstance : K.Normal).isSubnormal⟩
      have hm : X = ⁅X,elementaryAbelianMaxJ R⁆ := by
        have hh := congrArg (map D.subtype) (hB i).2.2.2.2
        rw [map_commutator,←elementaryAbelianMaxJ_map_injective D.subtype D.subtype_injective,
          map_subgroupOf_eq_of_le hRD] at hh
        exact hh
      have hout : ¬ X ≤ H := fun hXH => (hB i).2.1 (map_le_iff_le_comap.mp hXH)
      have hXN : X ≤ N := hcover X hb ha hm hout
      have hXbot : X = ⊥ := by
        apply le_bot_iff.mp
        intro x hx
        have hxZ : (⟨x,hXN hx⟩ : N) ∈ center N := by
          apply mem_center_iff.mpr
          intro y
          exact Subtype.ext (hXK hx y y.property)
        rw [hz,mem_bot] at hxZ
        exact mem_bot.mpr (congrArg Subtype.val hxZ)
      exact hout (hXbot ▸ bot_le)
    have hnzero : n = 0 := by
      by_contra hnzero
      exact hfalse ⟨0,Nat.pos_of_ne_zero hnzero⟩
    subst n
    intro x hx
    obtain ⟨h,hh,l,_,he⟩ := (hprod x).mp hx
    simp only [List.ofFn_zero,List.prod_nil,mul_one] at he
    exact he ▸ hh.1
  have hresD : solvableResidual D ≤ H.subgroupOf D := by
    intro x hx
    exact hres (map_solvableResidual_le D.subtype (mem_map_of_mem D.subtype hx))
  have hgf : (generalizedFitting (D ⧸ pCore 2 D)).comap
      (QuotientGroup.mk' (pCore 2 D)) ≤ H.subgroupOf D := by
    by_contra hout
    obtain ⟨B,hB,_,houtB⟩ := exists_cComponent_outside_of_fitting_preimage_le
      (H.subgroupOf D) hfit hout
    let := hB.perfect
    exact houtB ((le_solvableResidual_of_isPerfect B).trans hresD)
  have hpre : ChapterA.Section04.twoGeneralizedFittingPreimage D ≤ D ⊓ H := by
    rintro _ ⟨x,hx,rfl⟩
    exact ⟨x.property,hgf hx⟩
  have halt : ChapterA.Section04.IntersectionAlternative
      (ChapterA.Section04.twoCoreQuotientImage D
        (ChapterA.Section04.twoGeneralizedFittingPreimage D)) := by
    rw [ChapterA.Section04.twoCoreQuotientImage_fittingPreimage]
    refine Or.inr ⟨le_rfl,?_,?_⟩
    · exact (inferInstance : ((generalizedFitting (D ⧸ pCore 2 D)).subgroupOf
        (generalizedFitting (D ⧸ pCore 2 D))).Normal).isSubnormal
    · exact (closure_le _).mpr (fun x hx => hx.1.1)
  have hrecover := ChapterA.Section04.lemma_A_4_4_1 D H
    (ChapterA.Section04.twoGeneralizedFittingPreimage D)
    (ChapterA.Section04.twoCore_le_fittingPreimage D) hpre halt
  have hDHnorm : H ≤ normalizer (D ⊓ H : Set G) :=
    (le_inf hHD H.le_normalizer).trans inf_normalizer_le_normalizer_inf
  have hDHcore : (D ⊓ H).pCoreIn 2 ≤ R := by
    rw [←hcore]
    exact pCoreIn_mono_of_normalizes inf_le_right hDHnorm
  have hDR : D.pCoreIn 2 ≤ R := hrecover.le.trans hDHcore
  have hRcore : R ≤ (D ⊓ H).pCoreIn 2 :=
    le_pCoreIn_of_normalizes hr.isPGroup (le_inf hRD hRH) (inf_le_right.trans hHN)
  have he : D.pCoreIn 2 = R := le_antisymm hDR (hrecover.symm ▸ hRcore)
  have hDN : D ≤ normalizer (R : Set G) := by
    rw [←he]
    exact D.le_normalizer.trans (normalizer_le_normalizer_characteristic_image D (pCore 2 D))
  exact hKD.trans (hDN.trans hNH)
end CFSG.Quasithin.ChapterC.Section02Source
