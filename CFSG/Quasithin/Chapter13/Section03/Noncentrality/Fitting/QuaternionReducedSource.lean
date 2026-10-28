module
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Fitting.ReducedOddSource
public import Theory.GroupAction.QuaternionPlaneQuotient
public import Theory.Representation.AffineNine.QuaternionSource
public import Theory.Representation.NormalElementaryQuotient
/-!
# The original reduced-PT quaternion ratio obstruction

For a normal two-perfect P with elementary-nine core quotient and a
quaternion subgroup in the actual T-action, A.4.11 makes P move R₂(PT).
The surviving image is the full nine-group by quaternion irreducibility.
Its conjugation action is transported through the literal quotient map,
and reducedness gives the trivial two-core needed by the affine-nine bound.
Thus the original binary conjugation representation has cubic ratio >2.

The final theorem starts with the selected subgroup D of H/O₂(H) and
the original Q₈ image of T∩L⁺. It constructs PT, all intermediate maps,
normality, nontrivial image, and the marked Q₈ subgroup in the reduced
action. No quotient-model or surviving-action premise remains. The source
Ξ-minus implication producing E₉ and the competing bound of 3.1.8 are
separate earlier obligations.
Source: Aschbacher--Smith, 13.3.14(d), printed p.892.
-/

public section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality
open ChapterA.Section04
variable {G : Type*} [Group G] [Finite G]

theorem reduced_quaternion_ratio
    (P T : Subgroup G) [P.Normal] (hP : IsPPerfect 2 P)
    (hT : IsPGroup 2 T) (hgen : P ⊔ T = ⊤)
    [IsElementaryAbelian 3 (P ⧸ pCore 2 P)]
    (hcard : Nat.card (P ⧸ pCore 2 P) = 9)
    (hne : intrinsicSignalizerModule P ≠ ⊥)
    (Q : Subgroup (MulAut (P ⧸ pCore 2 P))) (eQ : Q ≃* QuaternionGroup 2)
    (hQ : Q ≤ (((quotientAut (pCore 2 P)).comp
      (MulAut.conjNormal : G →* MulAut P)).comp T.subtype).range) :
    let W := reducedTwoSubgroup G
    letI := (isPReduced_reducedPSubgroup (p := 2) (G := G)).elementary
    let C := centralizer (W : Set G)
    2 < BinaryOffender.cubicRatio
      (NormalElementaryQuotient.representation W (QuotientGroup.mk' C)
        (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)) := by
  let W := reducedTwoSubgroup G
  let := (isPReduced_reducedPSubgroup (p := 2) (G := G)).elementary
  let C := centralizer (W : Set G)
  let q := QuotientGroup.mk' C
  let D := P.map q
  let S := T.map q
  let : D.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective C)
  let a := (quotientAut (pCore 2 P)).comp (MulAut.conjNormal : G →* MulAut P)
  let f : QuaternionGroup 2 →* MulAut (P ⧸ pCore 2 P) := Q.subtype.comp eQ.symm.toMonoidHom
  have hf : Function.Injective f := Q.subtype_injective.comp eQ.symm.injective
  have hfa : f.range ≤ a.range := by
    rintro _ ⟨x,rfl⟩
    obtain ⟨t,ht⟩ := hQ (eQ.symm x).property
    exact ⟨t,ht⟩
  obtain ⟨hnot,_,hcore,_⟩ := reduced_quotient_odd_image P hP (by decide : Odd 3)
    (IsElementaryAbelian.isPGroup 3 (P ⧸ pCore 2 P)) hne
  have hk : pCore 2 P ≤ C.comap P.subtype := by
    intro x hx
    exact normal_pCore_le_centralizer_reducedPSubgroup 2 P (mem_map_of_mem P.subtype hx)
  obtain ⟨e,he⟩ := QuaternionGroup.quotient_core_image_injective P C (by decide : Odd 3)
    hcard hk hnot f hf hfa
  let : IsElementaryAbelian 3 D := IsElementaryAbelian.of_surjective e.toMonoidHom e.surjective
  have hD : Nat.card D = 9 := (Nat.card_congr e.toEquiv).symm.trans hcard
  let b : (G ⧸ C) →* MulAut D := MulAut.conjNormal
  have hconj (g : G) : MulAut.congr e (a g) = b (q g) := by
    apply MulEquiv.ext
    intro z
    obtain ⟨z,rfl⟩ := e.surjective z
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 P) z
    change e (a g (e.symm (e (QuotientGroup.mk' (pCore 2 P) x)))) = _
    rw [e.symm_apply_apply]
    change e (quotientAut (pCore 2 P) (MulAut.conjNormal g)
      (QuotientGroup.mk' (pCore 2 P) x)) = _
    rw [quotientAut_apply_mk]
    apply Subtype.ext
    change (e (QuotientGroup.mk' (pCore 2 P) (MulAut.conjNormal g x)) : G ⧸ C) =
      q g * (e (QuotientGroup.mk' (pCore 2 P) x) : G ⧸ C) * (q g)⁻¹
    rw [he,he]
    change q (g * (x : G) * g⁻¹) = _
    simp only [map_mul,map_inv]
    rfl
  let Q' := Q.map (MulAut.congr e).toMonoidHom
  let eQ' : Q' ≃* QuaternionGroup 2 := ((MulAut.congr e).subgroupMap Q).symm.trans eQ
  have hQ' : Q' ≤ (b.comp S.subtype).range := by
    rintro _ ⟨x,hx,rfl⟩
    obtain ⟨t,ht⟩ := hQ hx
    refine ⟨⟨q (t : G),mem_map_of_mem q t.property⟩,?_⟩
    change b (q (t : G)) = MulAut.congr e x
    rw [← ht,← hconj]
    rfl
  have hgen' : D ⊔ S = ⊤ := by
    change P.map q ⊔ T.map q = ⊤
    rw [← Subgroup.map_sup,hgen,map_top_of_surjective q (QuotientGroup.mk'_surjective C)]
  exact AffineNine.cubicRatio_gt_two_of_twoCore_eq_bot D S hD (hT.map q) hgen' hcore
    Q' eQ' hQ' _ (NormalElementaryQuotient.representation_injective W q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C))

theorem reduced_quaternion_ratio_of_marked_quotient
    (P T : Subgroup G) [P.Normal] (hP : IsPPerfect 2 P)
    (hT : IsPGroup 2 T) (hgen : P ⊔ T = ⊤)
    {D : Type*} [Group D] [Finite D] [IsElementaryAbelian 3 D]
    (hD : Nat.card D = 9) (e : (P ⧸ pCore 2 P) ≃* D)
    (hne : intrinsicSignalizerModule P ≠ ⊥)
    (a : G →* MulAut D)
    (ha : ∀ (g : G) (x : P),
      e (QuotientGroup.mk' (pCore 2 P) (MulAut.conjNormal g x)) =
        a g (e (QuotientGroup.mk' (pCore 2 P) x)))
    (Q : Subgroup (MulAut D)) (eQ : Q ≃* QuaternionGroup 2)
    (hQ : Q ≤ (a.comp T.subtype).range) :
    let W := reducedTwoSubgroup G
    letI := (isPReduced_reducedPSubgroup (p := 2) (G := G)).elementary
    let C := centralizer (W : Set G)
    2 < BinaryOffender.cubicRatio
      (NormalElementaryQuotient.representation W (QuotientGroup.mk' C)
        (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)) := by
  let : IsElementaryAbelian 3 (P ⧸ pCore 2 P) :=
    IsElementaryAbelian.of_surjective e.symm.toMonoidHom e.symm.surjective
  let b := (quotientAut (pCore 2 P)).comp (MulAut.conjNormal : G →* MulAut P)
  let E := MulAut.congr e.symm
  have he (g : G) : E (a g) = b g := by
    apply MulEquiv.ext
    intro z
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 P) z
    apply e.injective
    change e (e.symm (a g (e (QuotientGroup.mk' (pCore 2 P) x)))) = _
    rw [e.apply_symm_apply]
    change a g (e (QuotientGroup.mk' (pCore 2 P) x)) =
      e (quotientAut (pCore 2 P) (MulAut.conjNormal g) (QuotientGroup.mk' (pCore 2 P) x))
    rw [quotientAut_apply_mk]
    exact (ha g x).symm
  let Q' := Q.map E.toMonoidHom
  let eQ' : Q' ≃* QuaternionGroup 2 := (E.subgroupMap Q).symm.trans eQ
  have hQ' : Q' ≤ (b.comp T.subtype).range := by
    rintro _ ⟨x,hx,rfl⟩
    obtain ⟨t,ht⟩ := hQ hx
    refine ⟨t,?_⟩
    change b (t : G) = E x
    rw [← ht]
    exact (he (t : G)).symm
  exact reduced_quaternion_ratio P T hP hT hgen
    ((Nat.card_congr e.toEquiv).trans hD) hne Q' eQ' hQ'

theorem star_reduced_join_quaternion_ratio
    (H T Lplus : Subgroup G) (hTH : T ≤ H) (hLH : Lplus ≤ H)
    (hT : IsPGroup 2 T)
    (D : Subgroup (Star H)) [D.Normal] [IsElementaryAbelian 3 D]
    (hD : Nat.card D = 9)
    (hfaith : IsFaithfulSignalizerType ((starResidual H D).map H.subtype))
    (hQ : Nonempty (((T.subgroupOf Lplus).map
      ((MulAut.conjNormal : Star H →* MulAut D).comp (starMap H Lplus hLH))) ≃*
        QuaternionGroup 2)) :
    let P := (starResidual H D).map H.subtype
    let J := P ⊔ T
    let W := reducedTwoSubgroup J
    letI := (isPReduced_reducedPSubgroup (p := 2) (G := J)).elementary
    let C := centralizer (W : Set J)
    2 < BinaryOffender.cubicRatio
      (NormalElementaryQuotient.representation W (QuotientGroup.mk' C)
        (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)) := by
  let R := starResidual H D
  let P := R.map H.subtype
  let J := P ⊔ T
  let A := P.subgroupOf J
  let S := T.subgroupOf J
  let := starResidual_normal H D
  have hPN : (P.subgroupOf H).Normal := by
    change ((R.map H.subtype).comap H.subtype).Normal
    rw [comap_map_eq_self_of_injective H.subtype_injective]
    infer_instance
  have hHN : H ≤ normalizer (P : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (show P ≤ H from map_subtype_le _)).mp hPN
  have hJH : J ≤ H := sup_le (map_subtype_le _) hTH
  let : A.Normal := normal_subgroupOf_of_le_normalizer (hJH.trans hHN)
  let eP : A ≃* P := subgroupOfEquivOfLe (show P ≤ J from le_sup_left)
  let eR : A ≃* R := eP.trans (R.equivMapOfInjective H.subtype H.subtype_injective).symm
  let e : (A ⧸ pCore 2 A) ≃* D :=
    (QuotientGroup.congr _ _ eR (pCore_map_iso 2 eR)).trans
      (oddStarResidualCoreEquiv H D (by decide : Odd 3) (IsElementaryAbelian.isPGroup 3 D))
  have he (x : A) : (e (QuotientGroup.mk' (pCore 2 A) x) : Star H) =
      QuotientGroup.mk' (pCore 2 H) (inclusion hJH (x : J)) := by
    change QuotientGroup.mk' (pCore 2 H) (eR x : H) = _
    apply congrArg (QuotientGroup.mk' (pCore 2 H))
    apply Subtype.ext
    exact congrArg (fun y : P => (y : G))
      ((R.equivMapOfInjective H.subtype H.subtype_injective).apply_symm_apply (eP x))
  let a : J →* MulAut D := (MulAut.conjNormal : Star H →* MulAut D).comp
    ((QuotientGroup.mk' (pCore 2 H)).comp (inclusion hJH))
  have ha (g : J) (x : A) :
      e (QuotientGroup.mk' (pCore 2 A) (MulAut.conjNormal g x)) =
        a g (e (QuotientGroup.mk' (pCore 2 A) x)) := by
    apply Subtype.ext
    rw [he]
    change QuotientGroup.mk' (pCore 2 H) (inclusion hJH
      (g * (x : J) * g⁻¹)) =
      QuotientGroup.mk' (pCore 2 H) (inclusion hJH g) *
        (e (QuotientGroup.mk' (pCore 2 A) x) : Star H) *
        (QuotientGroup.mk' (pCore 2 H) (inclusion hJH g))⁻¹
    rw [he]
    simp only [map_mul,map_inv]
  let Q := (T.subgroupOf Lplus).map
    ((MulAut.conjNormal : Star H →* MulAut D).comp (starMap H Lplus hLH))
  obtain ⟨eQ⟩ := hQ
  have hQS : Q ≤ (a.comp S.subtype).range := by
    rintro x ⟨l,hl,rfl⟩
    refine ⟨⟨⟨l,mem_sup_right hl⟩,hl⟩,?_⟩
    rfl
  have hA : IsPPerfect 2 A := hfaith.1.2.1.of_surjective eP.symm.toMonoidHom eP.symm.surjective
  have hne : intrinsicSignalizerModule A ≠ ⊥ := by
    intro hz
    have heq := intrinsicSignalizerModule_map_of_injective J.subtype J.subtype_injective A
    rw [show A.map J.subtype = P from map_subgroupOf_eq_of_le le_sup_left,
      hz,Subgroup.map_bot] at heq
    exact hfaith.2 heq
  have hgen : A ⊔ S = ⊤ := by
    change P.subgroupOf J ⊔ T.subgroupOf J = ⊤
    rw [← subgroupOf_sup (show P ≤ J from le_sup_left) (show T ≤ J from le_sup_right)]
    exact subgroupOf_self _
  exact reduced_quaternion_ratio_of_marked_quotient A S hA
    (hT.of_equiv (subgroupOfEquivOfLe (show T ≤ J from le_sup_right)).symm)
    hgen hD e hne a ha Q eQ hQS
end CFSG.Quasithin.Chapter13.Section03.Noncentrality
