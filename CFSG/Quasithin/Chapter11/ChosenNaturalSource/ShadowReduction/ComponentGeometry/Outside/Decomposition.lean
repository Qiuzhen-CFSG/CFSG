module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.Frattini
public import Theory.GroupTheory.NormalizerQuotientInner
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PResidual.Quotient

/-!
# Outer-action and Frattini steps for the outside subgroup

The kernel of the literal action on Out(K/O₂(K)) is K times the
quotient centralizer. A normal Sylow subgroup of the outer image makes
the inverse image of its Sylow normal. Frattini then gives the source
product with the original Sylow normalizer. The two-closed outer image
is a model calculation still required from the surviving 11.1.2 cases.

Source: Aschbacher--Smith, 11.4.3, printed p.778.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside
variable {G : Type*} [Group G] [Finite G]

/-- The outer action of a subgroup of the actual normalizer of K. -/
def outerAction (K J : Subgroup G) (hn : J ≤ normalizer (K : Set G)) :
    J →* MulAut.Outer (K ⧸ pCore 2 K) :=
  (QuotientGroup.mk' (MulAut.innerSubgroup (K ⧸ pCore 2 K))).comp
    ((Closure.coreQuotientAction K).comp (inclusion hn))


private theorem twoClosed_subgroup {Q : Type*} [Group Q] [Finite Q]
    (hc : ChapterE.IsTwoClosed Q) (A : Subgroup Q) : ChapterE.IsTwoClosed A := by
  obtain ⟨P, hP⟩ := hc
  let := hP
  let := Sylow.unique_of_normal P hP
  let S : Sylow 2 A := Classical.choice inferInstance
  obtain ⟨R, hR⟩ := (S.isPGroup'.map A.subtype).exists_le_sylow
  have hSP : (S : Subgroup A) ≤ (P : Subgroup Q).subgroupOf A := by
    intro x hx
    exact (show R = P from Subsingleton.elim _ _) ▸ hR (mem_map_of_mem A.subtype hx)
  have he := S.is_maximal' P.isPGroup'.comap_subtype hSP
  exact ⟨S, he ▸ inferInstance⟩

/-- The source two-closed full outer group controls every literal local
outer image, without assuming that the local action is surjective. -/
theorem outerAction_range_twoClosed (K J : Subgroup G)
    (hn : J ≤ normalizer (K : Set G))
    (hc : ChapterE.IsTwoClosed (MulAut.Outer (K ⧸ pCore 2 K))) :
    ChapterE.IsTwoClosed (outerAction K J hn).range :=
  twoClosed_subgroup hc _

omit [Finite G] in
/-- Kernel of the actual quotient action, returned to the ambient group. -/
theorem quotientAction_kernel (K J : Subgroup G) (hn : J ≤ normalizer (K : Set G)) :
    (((Closure.coreQuotientAction K).comp (inclusion hn)).ker).map J.subtype =
      J ⊓ Closure.coreQuotientCentralizer K := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.property, ⟨inclusion hn x, hx, rfl⟩⟩
  · rintro ⟨hg, x, hx, he⟩
    refine ⟨⟨g, hg⟩, ?_, rfl⟩
    have hh : inclusion hn ⟨g, hg⟩ = x := Subtype.ext he.symm
    change Closure.coreQuotientAction K (inclusion hn ⟨g, hg⟩) = 1
    rw [hh]
    exact hx

omit [Finite G] in
/-- Inner quotient automorphisms lift to K, with precisely the quotient
centralizer as the remaining kernel. No ambient normality of K is used. -/
theorem outerAction_kernel (K J : Subgroup G)
    (hKJ : K ≤ J) (hn : J ≤ normalizer (K : Set G)) :
    (outerAction K J hn).ker.map J.subtype = K ⊔ (J ⊓ Closure.coreQuotientCentralizer K) := by
  let a := (Closure.coreQuotientAction K).comp (inclusion hn)
  have hi : (K.subgroupOf J).map a = MulAut.innerSubgroup (K ⧸ pCore 2 K) := by
    apply le_antisymm
    · rintro _ ⟨k, hk, rfl⟩
      exact ⟨QuotientGroup.mk' (pCore 2 K) ⟨k, hk⟩,
        (normalizerQuotientAction_inner K (pCore 2 K) ⟨k, hk⟩).symm⟩
    · rintro _ ⟨q, rfl⟩
      obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) q
      exact ⟨⟨k, hKJ k.property⟩, k.property,
        normalizerQuotientAction_inner K (pCore 2 K) k⟩
  change (((QuotientGroup.mk' (MulAut.innerSubgroup (K ⧸ pCore 2 K))).comp a).ker).map
    J.subtype = _
  rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', ← hi, comap_map_eq, Subgroup.map_sup,
    map_subgroupOf_eq_of_le hKJ]
  exact congrArg (K ⊔ ·) (quotientAction_kernel K J hn)

private theorem normal_kernel_sup_sylow {Q : Type*} [Group Q]
    (a : G →* Q) (S : Sylow 2 G) (hc : ChapterE.IsTwoClosed a.range) :
    (a.ker ⊔ (S : Subgroup G)).Normal := by
  let : Finite a.range := Finite.of_surjective a.rangeRestrict a.rangeRestrict_surjective
  obtain ⟨P, hP⟩ := hc
  let := Sylow.unique_of_normal P hP
  let U := S.mapSurjective a.rangeRestrict_surjective
  have hU : (U : Subgroup a.range).Normal := Sylow.normal_of_subsingleton U
  have he : (U : Subgroup a.range).comap a.rangeRestrict = a.ker ⊔ (S : Subgroup G) := by
    rw [Sylow.coe_mapSurjective, comap_map_eq, MonoidHom.ker_rangeRestrict, sup_comm]
  rw [← he]
  exact hU.comap a.rangeRestrict

/-- The two-closed outer image supplies the normal subgroup to which
Frattini's argument applies; the product itself is proved here. -/
theorem decomposition_of_outer_image {T : Sylow 2 G} (K J M : Subgroup G)
    (hKJ : K ≤ J) (hn : J ≤ normalizer (K : Set G))
    (hTJ : (T : Subgroup G) ≤ J) (hNT : normalizer (T : Set G) ≤ M)
    (hc : ChapterE.IsTwoClosed (outerAction K J hn).range) :
    J = K ⊔ (J ⊓ Closure.coreQuotientCentralizer K) ⊔ (M ⊓ J) := by
  let a := outerAction K J hn
  let S := T.subtype hTJ
  let N := (a.ker ⊔ (S : Subgroup J)).map J.subtype
  have hnormal : (a.ker ⊔ (S : Subgroup J)).Normal := normal_kernel_sup_sylow a S hc
  let := hnormal
  have hN : N = K ⊔ (J ⊓ Closure.coreQuotientCentralizer K) ⊔ (T : Subgroup G) := by
    rw [show N = (a.ker ⊔ (S : Subgroup J)).map J.subtype from rfl, Subgroup.map_sup,
      outerAction_kernel K J hKJ hn, Sylow.coe_subtype, map_subgroupOf_eq_of_le hTJ]
  have hNJ : N ≤ J := map_subtype_le _
  have hJN : J ≤ normalizer (N : Set G) := by
    intro j hj
    apply (a.ker ⊔ (S : Subgroup J)).le_normalizer_map J.subtype
    exact ⟨⟨j,hj⟩, by rw [normalizer_eq_top]; trivial, rfl⟩
  have hTN : (T : Subgroup G) ≤ N := hN.symm ▸ le_sup_right
  have hfr := LocalGeometry.Normalizers.relative_frattini hNJ hJN (T.subtype hTN)
    (by rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTN])
  apply le_antisymm
  · calc
      J = N ⊔ (J ⊓ normalizer (T : Set G)) := hfr
      _ = (K ⊔ (J ⊓ Closure.coreQuotientCentralizer K) ⊔ (T : Subgroup G)) ⊔
          (J ⊓ normalizer (T : Set G)) := congrArg (· ⊔ (J ⊓ normalizer (T : Set G))) hN
      _ ≤ K ⊔ (J ⊓ Closure.coreQuotientCentralizer K) ⊔ (M ⊓ J) :=
        sup_le (sup_le le_sup_left (le_sup_right.trans' (le_inf
          (T.le_normalizer.trans hNT) hTJ)))
          (le_sup_right.trans' (le_inf (inf_le_right.trans hNT) inf_le_left))
  · exact sup_le (sup_le hKJ inf_le_left) inf_le_right


private theorem normal_le_intersection_sup_sylow (S : Sylow 2 G)
    (B C : Subgroup G) [B.Normal] [C.Normal]
    (hCS : C ⊔ (S : Subgroup G) = ⊤) : B ≤ (B ⊓ C) ⊔ (S : Subgroup G) := by
  have hq := isPGroup_quotient_of_sup_eq_top C (S : Subgroup G) S.isPGroup' hCS
  let f := (QuotientGroup.mk' C).comp B.subtype
  have hr := pResidual_le_ker_of_isPGroup 2 f hq
  have hR : (pResidual 2 B).map B.subtype ≤ B ⊓ C := by
    rintro _ ⟨b, hb, rfl⟩
    exact ⟨b.property, (QuotientGroup.eq_one_iff _).mp (hr hb)⟩
  obtain ⟨P, hP⟩ := S.exists_subgroupOf_eq_of_normal B
  have he := congrArg (map B.subtype) (pResidual_sup_sylow_eq_top P)
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype, hP, subgroupOf_map_subtype] at he
  calc
    B = (pResidual 2 B).map B.subtype ⊔ ((S : Subgroup G) ⊓ B) := he.symm
    _ ≤ (B ⊓ C) ⊔ (S : Subgroup G) :=
      sup_le (hR.trans le_sup_left) (inf_le_left.trans le_sup_right)

/-- Restricting the kernel to a normal subgroup supplemented by T removes
exactly its two-group quotient. This is the extra step for the line centralizer. -/
theorem decomposition_on_normal_subgroup {T : Sylow 2 G} (K C J M : Subgroup G)
    (hKC : K ≤ C) (hCJ : C ≤ J) (hn : J ≤ normalizer (K : Set G))
    (hCn : J ≤ normalizer (C : Set G))
    (hTJ : (T : Subgroup G) ≤ J) (hCT : C ⊔ (T : Subgroup G) = J)
    (hNT : normalizer (T : Set G) ≤ M)
    (hc : ChapterE.IsTwoClosed (outerAction K J hn).range) :
    J = K ⊔ (C ⊓ Closure.coreQuotientCentralizer K) ⊔ (M ⊓ J) := by
  let a := outerAction K J hn
  let B := a.ker.map J.subtype
  have hB := outerAction_kernel K J (hKC.trans hCJ) hn
  let : (C.subgroupOf J).Normal := (normal_subgroupOf_iff_le_normalizer hCJ).mpr hCn
  have hCT' : C.subgroupOf J ⊔ ((T.subtype hTJ : Sylow 2 J) : Subgroup J) = ⊤ := by
    rw [Sylow.coe_subtype, ← subgroupOf_sup hCJ hTJ, hCT, subgroupOf_self]
  have hbound := normal_le_intersection_sup_sylow (T.subtype hTJ) a.ker (C.subgroupOf J) hCT'
  have hbound' : B ≤ (B ⊓ C) ⊔ (T : Subgroup G) := by
    have hh := map_mono (f := J.subtype) hbound
    rw [Subgroup.map_sup, Sylow.coe_subtype, map_subgroupOf_eq_of_le hTJ] at hh
    apply hh.trans
    apply sup_le_sup_right
    exact le_inf (map_mono inf_le_left) (by
      rintro _ ⟨x, hx, rfl⟩
      exact hx.2)
  have hBC : B ⊓ C ≤ K ⊔ (C ⊓ Closure.coreQuotientCentralizer K) := by
    intro b hb
    have hm : b ∈ K ⊔ (J ⊓ Closure.coreQuotientCentralizer K) := hB ▸ hb.1
    change b ∈ ((K ⊔ (J ⊓ Closure.coreQuotientCentralizer K) : Subgroup G) : Set G) at hm
    rw [coe_mul_of_right_le_normalizer_left _ _ (inf_le_left.trans hn)] at hm
    obtain ⟨k, hk, y, hy, rfl⟩ := hm
    have hyC : y ∈ C := by
      have hh := C.mul_mem (C.inv_mem (hKC hk)) hb.2
      simpa only [inv_mul_cancel_left] using hh
    exact (K ⊔ (C ⊓ Closure.coreQuotientCentralizer K)).mul_mem (mem_sup_left hk)
      (mem_sup_right ⟨hyC, hy.2⟩)
  apply le_antisymm
  · have hj : J = B ⊔ (M ⊓ J) := by
      rw [show B = K ⊔ (J ⊓ Closure.coreQuotientCentralizer K) from hB]
      exact decomposition_of_outer_image K J M (hKC.trans hCJ) hn hTJ hNT hc
    have hb' := hbound'.trans (sup_le_sup_right hBC (T : Subgroup G))
    calc
      J = B ⊔ (M ⊓ J) := hj
      _ ≤ K ⊔ (C ⊓ Closure.coreQuotientCentralizer K) ⊔ (M ⊓ J) :=
        sup_le (hb'.trans (sup_le le_sup_left
          (le_sup_right.trans' (le_inf (T.le_normalizer.trans hNT) hTJ)))) le_sup_right

  · exact sup_le (sup_le (hKC.trans hCJ) (inf_le_left.trans hCJ)) inf_le_right

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside
