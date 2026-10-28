module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryConstituent
public import Theory.GroupTheory.SolvableResidual.TwoSupplement

/-!
# Contained cores in the unitary nonnormal branch

Put K = O²(H), Q = O₂(K) and R = O₂(J). If Q ≤ R, the literal image
of K in J/O₂(J) is its original PSL₂ quotient. It is proper: otherwise
J = KR, and R normalizes K, so perfectness forces J = K. The full Sylow
embedding theorem therefore gives q = 4 and the actual five A.3.14 models
without assuming Q normal in J or R = Q.

In the ordinary unitary row the original S lies in K, hence R ≤ Q.
Thus nonnormal containment is confined to the degree-two extension, with
|R:Q| = 2. The original index bound then proves R = O₂(H) = O₂(KS).
Characteristic two in the enlarged source parabolic, whose core is Q,
places Z(R) in Z(Q). Both orientations and the original S are retained.

The companion applies these deductions to the literal Chapter12 pair.
The field-four extended containment remainder is not yet excluded; in
particular the reverse center containment and the source Thompson argument
are not asserted. The proper-intersection embedding selection and
second-parabolic contradiction, other maximality rows, exhaustive amalgam
comparison and ambient recognition also remain open.
Source: Aschbacher–Smith 5.2.8, printed pp.652–653 (`refs/quasithin.pdf`),
with 1.2.4 and A.3.12–14 for the actual binary embedding selection.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
open ChapterC.Section05.NormalizerControl.EmbeddingSelection
variable {G : Type*} [Group G] [Finite G]

private theorem simple_perfect_quasisimple {X : Type*} [Group X]
    [IsSimpleGroup X] [Group.IsPerfect X] : IsQuasisimple X := by
  have hz : center X = ⊥ :=
    (inferInstance : (center X).Normal).eq_bot_or_eq_top.resolve_right
      (fun ht => Group.IsPerfect.not_isMulCommutative X (center_eq_top_iff.mp ht))
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup⟩

private theorem local_binary_parameter_of_core_containment
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {T : Sylow 2 G} {K J : Subgroup G}
    (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hKJ : K < J) (hc : K ⊓ J.pCoreIn 2 = K.pCoreIn 2)
    (hRK : J.pCoreIn 2 ≤ normalizer (K : Set G))
    {n : ℕ} (hn : 1 < n) (hpK : Group.IsPerfect K)
    (hbinary : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2^n)) :
    n = 2 ∧ AlternatingFive.Shortlist (J ⧸ pCore 2 J) := by
  let X := J ⊔ (T : Subgroup G)
  let JX := J.subgroupOf X
  let eJ : JX ≃* J := subgroupOfEquivOfLe le_sup_left
  let TX := T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)
  obtain ⟨P,hP⟩ := TX.exists_subgroupOf_eq_of_subnormal JX hJ.1.subnormal
  let S := P.mapSurjective (f := eJ.toMonoidHom) eJ.surjective
  have hSJ : (S : Subgroup J) ≤ (T : Subgroup G).subgroupOf J := by
    change (P : Subgroup JX).map eJ.toMonoidHom ≤ _
    rw [hP]
    rintro y ⟨x,hx,rfl⟩
    exact hx
  have hSK : (S : Subgroup J) ≤ normalizer (K.subgroupOf J : Set J) := by
    rw [← subgroupOf_normalizer_eq hKJ.le]
    exact hSJ.trans (comap_mono hTK)
  let q := QuotientGroup.mk' (pCore 2 J)
  let f := q.comp (inclusion hKJ.le)
  let B := f.range
  have hBmap : B = (K.subgroupOf J).map q := by
    change (q.comp (inclusion hKJ.le)).range = _
    rw [MonoidHom.range_comp,inclusion_range]
  have hker : f.ker = pCore 2 K := by
    ext x
    change (QuotientGroup.mk (inclusion hKJ.le x) : J ⧸ pCore 2 J) = 1 ↔ x ∈ pCore 2 K
    rw [QuotientGroup.eq_one_iff,←mem_map_iff_mem J.subtype_injective,
      ←mem_map_iff_mem K.subtype_injective]
    change (x : G) ∈ J.pCoreIn 2 ↔ (x : G) ∈ K.pCoreIn 2
    constructor
    · intro hx
      exact hc ▸ (show (x : G) ∈ K ⊓ J.pCoreIn 2 from ⟨x.property,hx⟩)
    · intro hx
      exact (show (x : G) ∈ K ⊓ J.pCoreIn 2 from hc.symm ▸ hx).2
  let eB : B ≃* (K ⧸ pCore 2 K) :=
    (QuotientGroup.quotientKerEquivRange f).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hker)
  let := hpK
  let : IsSimpleGroup (K ⧸ pCore 2 K) := binary_simple hn hbinary
  let : IsSimpleGroup B := eB.isSimpleGroup
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective (f := eB.symm.toMonoidHom) eB.symm.surjective
  let : IsQuasisimple B := simple_perfect_quasisimple
  let Sb := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 J))
  have hnorm : (Sb : Subgroup (J ⧸ pCore 2 J)) ≤ normalizer (B : Set _) := by
    rw [hBmap]
    exact (map_mono hSK).trans (le_normalizer_map q)
  have hb : B ∈ localCComponents Sb := by
    let e := subgroupOfEquivOfLe (show B ≤ B ⊔ (Sb : Subgroup _) from le_sup_left)
    let : IsSimpleGroup (B.subgroupOf (B ⊔ (Sb : Subgroup _))) := e.isSimpleGroup
    let : Group.IsPerfect (B.subgroupOf (B ⊔ (Sb : Subgroup _))) :=
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    have hn' : (B.subgroupOf (B ⊔ (Sb : Subgroup _))).Normal :=
      normal_subgroupOf_of_le_normalizer (sup_le B.le_normalizer hnorm)
    exact isCComponent_of_isSimpleGroup_of_isPerfect hn'.isSubnormal
  have hne : B ≠ ⊤ := by
    intro ht
    let D := K.subgroupOf J
    have hgen : D ⊔ pCore 2 J = ⊤ := by
      have hh := congrArg (Subgroup.comap q) ht
      rw [hBmap,comap_map_eq,QuotientGroup.ker_mk',comap_top] at hh
      exact hh
    have hnD : D.Normal := (normalizer_eq_top_iff).mp (by
      have hh : D ⊔ pCore 2 J ≤ normalizer (D : Set J) := by
        refine sup_le D.le_normalizer ?_
        rw [←subgroupOf_normalizer_eq hKJ.le]
        intro x hx
        exact hRK (mem_map_of_mem J.subtype hx)
      rw [hgen] at hh
      exact top_unique hh)
    let := hnD
    let : Group.IsPerfect D := Group.IsPerfect.ofSurjective
      (f := (subgroupOfEquivOfLe hKJ.le).symm.toMonoidHom)
      (subgroupOfEquivOfLe hKJ.le).symm.surjective
    let : Group.IsPerfect J := Chapter1.mem_L_isPerfect hJ
    have hDtop : D = ⊤ :=
      (residuals_of_perfect_normal_sup_twoGroup D (pCore 2 J) pCore_isPGroup hgen).2.symm.trans
        solvableResidual_eq_top
    exact hKJ.ne (le_antisymm hKJ.le (subgroupOf_eq_top.mp hDtop))
  let qX := QuotientGroup.mk' (pCore 2 X)
  have hsq := Chapter1.Section02.uniqueness_local_quotient_sqtk hG hJ.2.2
  let eqJ : JX.map qX ≃* (J ⧸ pCore 2 J) :=
    (cComponentTwoCoreQuotientEquiv hJ.1).symm.trans
      (QuotientGroup.congr _ _ eJ (pCore_map_iso 2 eJ))
  have hsqJ : IsSQTK KnownSimple.IsKnownSimple (J ⧸ pCore 2 J) :=
    (IsSQTK.equiv eqJ).mp (hsq.subgroup _)
  have htop : (⊤ : Subgroup (J ⧸ pCore 2 J)).IsCComponent := by
    let := pCore_isNilpotent (p := 2) (G := X)
    have hh : (⊤ : Subgroup (JX.map qX)).IsCComponent := by
      simpa only [subgroupOf_self] using (hJ.1.map_quotient (pCore 2 X)).subgroupOf le_rfl
    simpa only [map_top_of_surjective eqJ.toMonoidHom eqJ.surjective] using hh.map_equiv eqJ
  have hbin : ClassicalGroup.IsPSL B 2 (2^n) := hbinary.of_mulEquiv eB
  rcases binary_larger_selection_knownSimple hsqJ (pCore_quotient_pCore_eq_bot 2)
      Sb hb htop (show B ≤ ⊤ from le_top) hnorm hn hbin with he | ⟨hn2,hm⟩
  · exact (hne he).elim
  · exact ⟨hn2, AlternatingFive.Shortlist.of_equiv hm
      (topEquiv (G := J ⧸ pCore 2 J)).symm⟩

open ChapterF.GreenBook.LieModels.UnitaryFour
private theorem Preparation.unitary_ordinary_sourceS_le_right
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (amalgam m hm)) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (amalgam m hm).reverse)) :
    sourceS L H ≤ residual H := by
  have hm' := (d.unitary_local_structure h hTH hp m hm he).1
  have transfer {X : Type} [Group X]
      (e : ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 ≃* X)
      (hb : ∀ U : Subgroup X, IsPGroup 2 U → U ≤ solvableResidual X) :
      sourceS L H ≤ residual H := by
    let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
    have hSP : sourceS L H ≤ P := le_sup_right.trans le_sup_left
    have hh := hb (((sourceS L H).subgroupOf P).map e.toMonoidHom)
      (((pCore_isPGroup.map _ : IsPGroup 2 (sourceS L H)).comap_subtype).map e.toMonoidHom)
    rw [←map_solvableResidual_eq e.toMonoidHom e.surjective,
      map_le_map_iff_of_injective e.injective] at hh
    have hmap := map_mono (f := P.subtype) hh
    rwa [map_subgroupOf_eq_of_le hSP,d.parabolic_residuals h hTH hp 1] at hmap
  rcases he with he | he <;> obtain ⟨e⟩ := he
  · apply transfer e.right
    intro U hU
    let := L2_isPerfect m hm
    have hh := (two_subgroup_le_L2 m hm _ (hU.map _) (map_subtype_le _)).trans
      (le_map_solvableResidual_of_isPerfect (L2 m hm) (planeParabolic m hm)
        (L2_le_planeParabolic m hm))
    exact (map_le_map_iff_of_injective (planeParabolic m hm).subtype_injective).mp hh
  · apply transfer e.right
    intro U hU
    let := PointLocal.projectiveLocal_isPerfect m hm hm'
    have hh := (PointLocal.twoSubgroup_le_projectiveLocal m hm _ (hU.map _)
      (map_subtype_le _)).trans (le_map_solvableResidual_of_isPerfect
        (PointLocal.ProjectiveLocal m hm) (pointParabolic m hm)
        (by rw [←PointLocal.pointParabolic_solvableResidual m hm hm']; exact map_subtype_le _))
    exact (map_le_map_iff_of_injective (pointParabolic m hm).subtype_injective).mp hh

/-- In the ordinary unitary row every overcomponent core lies in Q.
The extended row is not used in this statement. -/
theorem Preparation.unitary_ordinary_overcomponent_core_le
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (amalgam m hm)) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (amalgam m hm).reverse))
    {J : Subgroup G} (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hKJ : residual H ≤ J) : J.pCoreIn 2 ≤ (residual H).pCoreIn 2 := by
  obtain ⟨hRS,hNQ,_,_,_,_⟩ :=
    d.unitary_overcomponent_core_intersection h hH hp m hm (.inl he) hJ hKJ
  have hRK := hRS.trans (d.unitary_ordinary_sourceS_le_right h hH.1.1.2 hp m hm he)
  rwa [inf_eq_right.mpr hRK] at hNQ

section Unitary
variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B (residual H))
  (h : Input KnownSimple.IsKnownSimple T L W n)
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
  (he : (Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (amalgam m hm)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (amalgam m hm).reverse)) ∨
    (Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm).reverse)))
include d h hH hp m hm he

/-- Containment of the original core already forces the field-four embedding
shortlist; normality of that core in the overcomponent is not assumed. -/
theorem Preparation.unitary_overcomponent_parameter_of_containment
    {J : Subgroup G} (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hKJ : residual H < J)
    (hQR : (residual H).pCoreIn 2 ≤ J.pCoreIn 2) :
    m = 2 ∧ n = 4 ∧ AlternatingFive.Shortlist (J ⧸ pCore 2 J) := by
  obtain ⟨hRS,hNQ,_,_,_,_⟩ :=
    d.unitary_overcomponent_core_intersection h hH hp m hm he hJ hKJ.le
  have hc : residual H ⊓ J.pCoreIn 2 = (residual H).pCoreIn 2 :=
    le_antisymm hNQ (le_inf (pCoreIn_le 2 _) hQR)
  have hRK := (hRS.trans (sourceS_le_sylow h.sylow_normalizes hH.1.1.2)).trans
    (hH.1.1.2.trans (le_normalizer_residual H))
  have hf := he.elim (d.unitary_local_structure h hH.1.1.2 hp m hm)
    (d.unitaryExtension_local_structure h hH.1.1.2 hp m hm)
  obtain ⟨hm2,hs⟩ := local_binary_parameter_of_core_containment h.qtke hJ
    (hH.1.1.2.trans (le_normalizer_residual H)) hKJ hc hRK hf.1 hp hf.2.2.2.2
  exact ⟨hm2,by have := hf.2.1; omega,hs⟩

/-- In the containment branch the overcomponent center lies in the original
core center. The enlarged source parabolic has characteristic two and
exactly Q as its two-core, even for the degree-two unitary extension. -/
theorem Preparation.unitary_contained_overcomponent_center_le
    {J : Subgroup G} (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hKJ : residual H ≤ J)
    (hQR : (residual H).pCoreIn 2 ≤ J.pCoreIn 2) :
    (center (J.pCoreIn 2)).map (J.pCoreIn 2).subtype ≤
      (center ((residual H).pCoreIn 2)).map ((residual H).pCoreIn 2).subtype := by
  let K := residual H
  let Q := K.pCoreIn 2
  let R := J.pCoreIn 2
  let P := ChapterF.Source.parabolic ![L,K] (sourceS L H) 1
  let Y := P ⊔ (T : Subgroup G)
  have hKP : K ≤ P := le_sup_left.trans le_sup_left
  have hYK : Y ≤ normalizer (K : Set G) := sup_le
    ((normal_subgroupOf_iff_le_normalizer hKP).mp
      ((d.hypothesisF11 h hH.1.1.2).local_normal_in_parabolic 1))
    (hH.1.1.2.trans (le_normalizer_residual H))
  have hSY : sourceS L H ≤ Y := le_sup_right.trans (le_sup_left.trans le_sup_left)
  have hchar := Chapter1.mem_He_iff.mpr
    ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp
      (characteristic_two_of_sourceS_right h hH hYK hSY))
  change Y ⊓ centralizer (Y.pCoreIn 2 : Set G) ≤ Y.pCoreIn 2 at hchar
  have hcore : Y.pCoreIn 2 = Q := d.parabolic_sylow_core_eq_of_comparison h hH.1.1.2 hp
    (he.elim (.unitary m hm) (.unitaryExtension m hm)) 1
  rw [hcore] at hchar
  have hRS := (d.unitary_overcomponent_core_intersection h hH hp m hm he hJ hKJ).1
  rintro _ ⟨z,hz,rfl⟩
  have hcR : z.val ∈ centralizer (R : Set G) := by
    intro r hr
    exact congrArg Subtype.val ((mem_center_iff.mp hz) ⟨r,hr⟩)
  have hcQ := centralizer_le hQR hcR
  have hzQ : z.val ∈ Q := hchar ⟨hSY (hRS z.property),hcQ⟩
  refine ⟨⟨z.val,hzQ⟩,mem_center_iff.mpr ?_,rfl⟩
  intro q
  exact Subtype.ext (hcQ q.val q.property)

/-- A nonnormal contained unitary core can only be the field-four degree-two
extension: R has twice the order of Q, and the overcomponent quotient is
one of the five actual A.3.14 models. -/
theorem Preparation.unitary_nonnormal_containment
    {J : Subgroup G} (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hKJ : residual H < J)
    (hQR : (residual H).pCoreIn 2 ≤ J.pCoreIn 2)
    (hnorm : ¬ J ≤ normalizer ((residual H).pCoreIn 2 : Set G)) :
    m = 2 ∧ n = 4 ∧ AlternatingFive.Shortlist (J ⧸ pCore 2 J) ∧
      (Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm)) ∨
       Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm).reverse)) ∧
      ((residual H).pCoreIn 2).relIndex (J.pCoreIn 2) = 2 ∧
      Nat.card (J.pCoreIn 2) = 2*(2^m)^5 := by
  obtain ⟨hm2,hn4,hs⟩ :=
    d.unitary_overcomponent_parameter_of_containment h hH hp m hm he hJ hKJ hQR
  have hne : J.pCoreIn 2 ≠ (residual H).pCoreIn 2 := by
    intro hh
    apply hnorm
    rw [←hh]
    exact J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J))
  have hext : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm).reverse) := by
    rcases he with ho | hext
    · exact (hne (le_antisymm
        (d.unitary_ordinary_overcomponent_core_le h hH hp m hm ho hJ hKJ.le) hQR)).elim
    · exact hext
  obtain ⟨_,hNQ,_,_,_,hi⟩ :=
    d.unitary_overcomponent_core_intersection h hH hp m hm he hJ hKJ.le
  have hN : residual H ⊓ J.pCoreIn 2 = (residual H).pCoreIn 2 :=
    le_antisymm hNQ (le_inf (pCoreIn_le 2 _) hQR)
  rw [hN] at hi
  have hni : ((residual H).pCoreIn 2).relIndex (J.pCoreIn 2) ≠ 1 := by
    intro hh
    exact hne (le_antisymm (relIndex_eq_one.mp hh) hQR)
  have hpos : 0 < ((residual H).pCoreIn 2).relIndex (J.pCoreIn 2) :=
    Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hieq : ((residual H).pCoreIn 2).relIndex (J.pCoreIn 2) = 2 := by omega
  refine ⟨hm2,hn4,hs,hext,hieq,?_⟩
  have hcQ : Nat.card ((residual H).pCoreIn 2) = (2^m)^5 := by
    exact (Nat.card_congr ((pCore 2 (residual H)).equivMapOfInjective
      (residual H).subtype (residual H).subtype_injective).symm.toEquiv).trans
      (d.unitary_core_structure h hH.1.1.2 hp m hm he).2.2.2.2.1
  have hh := (((residual H).pCoreIn 2).subgroupOf (J.pCoreIn 2)).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hQR).toEquiv,hcQ] at hh
  change (2^m)^5 * ((residual H).pCoreIn 2).relIndex (J.pCoreIn 2) = _ at hh
  rw [hieq] at hh
  simpa [mul_comm] using hh.symm

/-- In the remaining contained branch, the overcomponent core is exactly
both O₂(H) and O₂(KS). These equalities retain the extra factor of two;
they do not identify either group with the original Q. -/
theorem Preparation.unitary_nonnormal_containment_core_eq
    {J : Subgroup G} (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hKJ : residual H < J)
    (hQR : (residual H).pCoreIn 2 ≤ J.pCoreIn 2)
    (hnorm : ¬ J ≤ normalizer ((residual H).pCoreIn 2 : Set G)) :
    J.pCoreIn 2 = H.pCoreIn 2 ∧
      J.pCoreIn 2 = (residual H ⊔ sourceS L H).pCoreIn 2 := by
  let K := residual H
  let Q := K.pCoreIn 2
  let R := J.pCoreIn 2
  let U := (K ⊔ sourceS L H).pCoreIn 2
  have hHJ : H ≤ J ⊔ (T : Subgroup G) := by
    rw [←residual_sup_sylow T H hH.1.1.2]
    exact sup_le_sup hKJ.le le_rfl
  have hRH : R ≤ H.pCoreIn 2 :=
    (pCoreAmbient_mono_of_isSubnormalIn J (J ⊔ (T : Subgroup G)) 2
      le_sup_left hJ.1.subnormal).trans
        (Chapter3.twoCore_le_of_sylow_le T hH.1.1.2 hHJ)
  have hHS : H.pCoreIn 2 ≤ sourceS L H :=
    Chapter3.twoCore_le_of_sylow_le T (le_inf h.sylow_normalizes hH.1.1.2) inf_le_right
  have hXH : K ⊔ sourceS L H ≤ H := sup_le (map_subtype_le _)
    ((map_subtype_le _).trans inf_le_right)
  have hHU : H.pCoreIn 2 ≤ U :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 H) (hHS.trans le_sup_right)
      (hXH.trans (H.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image H (pCore 2 H))))
  have hi : Q.relIndex R = 2 :=
    (d.unitary_nonnormal_containment h hH hp m hm he hJ hKJ hQR hnorm).2.2.2.2.1
  have hb : Q.relIndex U ≤ 2 := d.core_index_le_two_of_comparison h hH.1.1.2 hp
    (he.elim (.unitary m hm) (.unitaryExtension m hm))
  have hmul := relIndex_mul_relIndex Q R U hQR (hRH.trans hHU)
  rw [hi] at hmul
  have hpos : 0 < R.relIndex U := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hiRU : R.relIndex U = 1 := by omega
  have hUR : U ≤ R := relIndex_eq_one.mp hiRU
  exact ⟨le_antisymm hRH (hHU.trans hUR),le_antisymm (hRH.trans hHU) hUR⟩

end Unitary
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
