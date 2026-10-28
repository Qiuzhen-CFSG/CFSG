module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SmallFactors

/-!
# The saturated original star as a full intrinsic MS pair

The original odd-index witness restricts to the normal star overgroup. Its
core is the intersection with the original radical, which marked preservation
identifies with the star radical. Characteristic subgroups of the star lift
through its actual subgroup equivalence to characteristic subgroups of R;
normality under the component and R then proves the intrinsic MS3 condition.
Thus the source star retains every original input, including its literal
component quotient, and has inner ambient action and a saturated radical.
Its Sylow status is exactly that of the original radical.

Intersecting admissible characteristic cuts proves that every minimum
replacement lies inside this same star. This is containment, not equality of
marked images. No critical distance is transferred between their graphs.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.4), printed pp.868--869, and the opening of (3.7), printed p.872.
The minimum-cut comparison uses the definition in Section 7, pp.932--933.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
open DistanceTwoRecognition
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)

private theorem odd_index_restriction (A M : Subgroup H) [M.Normal]
    (ho : Odd A.index) : Odd (A.subgroupOf M).index := by
  let P : Sylow 2 A := Classical.choice inferInstance
  have hp : ¬ 2 ∣ ((P : Subgroup A).map A.subtype).index := by
    rw [index_map_subtype]
    exact Nat.Prime.not_dvd_mul (by decide) P.not_dvd_index ho.not_two_dvd_nat
  let S : Sylow 2 H := (P.isPGroup'.map A.subtype).toSylow hp
  let S₀ := componentSylow M S
  have hS : (S₀ : Subgroup M) ≤ A.subgroupOf M := by
    rw [componentSylow_coe]
    exact fun x hx => map_subtype_le (P : Subgroup A) hx
  rw [←Nat.not_even_iff_odd,even_iff_two_dvd]
  exact fun hd => S₀.not_dvd_index (hd.trans (index_dvd_of_le hS))

private theorem core_restriction (A M : Subgroup H) [M.Normal] :
    (A.subgroupOf M).pCoreIn 2 = (A.pCoreIn 2).subgroupOf M := by
  have hu := map_mono (f := A.subtype)
    (pCoreIn_le_of_subnormal 2 (inferInstance : (M.subgroupOf A).Normal).isSubnormal)
  rw [map_pCoreIn_of_injective 2 _ _ A.subtype_injective,
    subgroupOf_map_subtype,inf_comm M A] at hu
  have hl := inf_pCoreIn_le_of_le 2 (show A ⊓ M ≤ A from inf_le_left)
  have he : (A ⊓ M).pCoreIn 2 = M ⊓ A.pCoreIn 2 := by
    apply le_antisymm (le_inf (((A ⊓ M).pCoreIn_le 2).trans inf_le_right) hu)
    apply le_trans ?_ hl
    exact le_inf (le_inf ((inf_le_right : M ⊓ A.pCoreIn 2 ≤ A.pCoreIn 2).trans
      (A.pCoreIn_le 2)) inf_le_left) inf_le_right
  apply map_injective M.subtype_injective
  rw [map_pCoreIn_of_injective 2 _ _ M.subtype_injective,
    subgroupOf_map_subtype,subgroupOf_map_subtype,he,inf_comm]

private theorem characteristic_comap_equiv
    {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (C : Subgroup B) [C.Characteristic] : (C.comap e.toMonoidHom).Characteristic := by
  apply characteristic_iff_le_comap.mpr
  intro a x hx
  change e (a x) ∈ C
  have hh := characteristic_iff_le_comap.mp (inferInstance : C.Characteristic)
    ((e.symm.trans a).trans e) hx
  change e (a (e.symm (e x))) ∈ C at hh
  simpa only [MulEquiv.symm_apply_apply] using hh

include h

omit [Finite H] [Finite F] [CharP F 2] in
private theorem star_msCharacteristic (Y : Subgroup R) :
    let T := (starCentralizer R Y).map R.subtype
    MSCharacteristicCondition (T.subgroupOf (K ⊔ T)) := by
  let S := starCentralizer R Y
  let T := S.map R.subtype
  let M := K ⊔ T
  let e : S ≃* T.subgroupOf M :=
    (S.equivMapOfInjective R.subtype R.subtype_injective).trans
      (subgroupOfEquivOfLe (show T ≤ M from le_sup_right)).symm
  change MSCharacteristicCondition (T.subgroupOf M)
  intro C hC hne hnormal
  let := hC
  let D := C.comap e.toMonoidHom
  let : D.Characteristic := characteristic_comap_equiv e C
  let A := D.map S.subtype
  let : S.Characteristic := starCentralizer_characteristic R Y
  let : A.Characteristic := inferInstance
  have hDC : D.map e.toMonoidHom = C := by
    rw [map_comap_eq_self_of_surjective e.surjective]
  have hmaps : A.map R.subtype = (C.map (T.subgroupOf M).subtype).map M.subtype := by
    rw [←hDC,map_map,map_map,map_map]
    rfl
  have hn : M ≤ normalizer (A.map R.subtype : Set H) := by
    rw [hmaps]
    apply (normal_subgroupOf_iff_le_normalizer (map_subtype_le _)).mp
    rw [subgroupOf_map_subtype_eq]
    exact hnormal
  have hAn : (A.map R.subtype).Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_le_iff.mp
    rw [←original_sup h]
    exact sup_le (le_sup_left.trans hn)
      (R.le_normalizer.trans (normalizer_le_normalizer_characteristic_image R A))
  have hz : A = ⊥ := h.characteristic.eq_bot_of_normal A hAn
  have hD : D = ⊥ := (map_eq_bot_iff_of_injective D S.subtype_injective).mp hz
  exact hne (by rw [←hDC,hD,Subgroup.map_bot])

omit [Finite F] [CharP F 2] in
/-- The original odd-index witness restricts to the literal star overgroup;
marked preservation identifies its core with the star radical itself. -/
theorem star_odd_index_radical_of_restriction (Y : Subgroup R)
    (he : let T := (starCentralizer R Y).map R.subtype
      T.subgroupOf (K ⊔ T) = R.subgroupOf (K ⊔ T)) :
    let T := (starCentralizer R Y).map R.subtype
    MSOddIndexRadical (T.subgroupOf (K ⊔ T)) := by
  let T := (starCentralizer R Y).map R.subtype
  let M := K ⊔ T
  let : M.Normal := star_overgroup_normal h Y
  obtain ⟨A,hA,hodd,hcore⟩ := h.radical
  change A.pCoreIn 2 = R at hcore
  have hRA : R ≤ A := hcore ▸ A.pCoreIn_le 2
  refine ⟨A.subgroupOf M,lt_top_iff_ne_top.mpr ?_,
    odd_index_restriction A M hodd,?_⟩
  · intro ht
    have hMA : M ≤ A := subgroupOf_eq_top.mp ht
    exact hA.not_ge ((original_sup h) ▸ sup_le (le_sup_left.trans hMA) hRA)
  · change (A.subgroupOf M).pCoreIn 2 = T.subgroupOf M
    rw [core_restriction,hcore]
    exact he.symm

/-- Full intrinsic MS input on the star, retaining the original quotient
marking. The core equality premise is supplied by marked preservation. -/
private def starInputOfRestriction (Y : Subgroup R)
    (he : let T := (starCentralizer R Y).map R.subtype
      T.subgroupOf (K ⊔ T) = R.subgroupOf (K ⊔ T)) :
    let T := (starCentralizer R Y).map R.subtype
    Input (K.subgroupOf (K ⊔ T)) (T.subgroupOf (K ⊔ T)) n F := by
  let T := (starCentralizer R Y).map R.subtype
  let M := K ⊔ T
  let : M.Normal := star_overgroup_normal h Y
  let := h.component_normal
  refine {
    nonbinary := h.nonbinary
    field_card := h.field_card
    sqtk := h.sqtk.subgroup M
    fitting := ?_
    component := h.component.subgroupOf le_sup_left
    product := ?_
    radical := star_odd_index_radical_of_restriction h Y he
    characteristic := by exact star_msCharacteristic h Y
    quotientEquiv := (subgroupOfCoreQuotientEquiv le_sup_left).trans h.quotientEquiv }
  · apply le_antisymm _ ((pCore_le_fitting _ 2).trans (fitting_le_generalizedFitting _))
    rw [pCore_subnormal_eq_comap 2 (inferInstance : M.Normal).isSubnormal]
    apply map_le_iff_le_comap.mp
    rw [←h.fitting]
    exact generalizedFitting_map_subtype_le_of_isSubnormal _
      (inferInstance : M.Normal).isSubnormal
  · intro x
    obtain ⟨k,hk,t,ht,he⟩ := mem_sup_of_normal_left.mp x.property
    exact ⟨⟨k,mem_sup_left hk⟩,hk,⟨t,mem_sup_right ht⟩,ht,Subtype.ext he⟩

omit [Finite F] [CharP F 2] in
private theorem starInput_marked_radical (Y : Subgroup R)
    (he : let T := (starCentralizer R Y).map R.subtype
      T.subgroupOf (K ⊔ T) = R.subgroupOf (K ⊔ T)) :
    let T := (starCentralizer R Y).map R.subtype
    let M := K ⊔ T
    ((T.subgroupOf M).subgroupOf (K.subgroupOf M)).map
      (componentProjection (starInputOfRestriction h Y he)) =
        (T.subgroupOf K).map (componentProjection h) := by
  dsimp only
  ext x
  constructor
  · rintro ⟨k,hk,rfl⟩
    exact ⟨subgroupOfEquivOfLe le_sup_left k,hk,rfl⟩
  · rintro ⟨k,hk,rfl⟩
    exact ⟨⟨⟨k.val,mem_sup_left k.property⟩,k.property⟩,hk,rfl⟩

omit [Finite F] [CharP F 2] in
/-- The saturated original star preserves the Sylow alternative in both
directions, through the same component quotient and its complete kernel. -/
theorem star_sylow_iff_original (Y : Subgroup R)
    (he : let T := (starCentralizer R Y).map R.subtype
      T.subgroupOf (K ⊔ T) = R.subgroupOf (K ⊔ T))
    (hmark : (((starCentralizer R Y).map R.subtype).subgroupOf K).map
      (componentProjection h) = (R.subgroupOf K).map (componentProjection h)) :
    let T := (starCentralizer R Y).map R.subtype
    (∃ S : Sylow 2 (K ⊔ T : Subgroup H), (S : Subgroup _) = T.subgroupOf (K ⊔ T)) ↔
      ∃ S : Sylow 2 H, (S : Subgroup H) = R := by
  dsimp only
  rw [original_sylow_iff_marked_sylow (starInputOfRestriction h Y he),
    original_sylow_iff_marked_sylow h,starInput_marked_radical h Y he,hmark]

omit h [Finite F] [CharP F 2] in
/-- Every minimum characteristic cut lies in every characteristic cut,
since the intersection is again an admissible cut. -/
private theorem minimum_le_characteristic_cut (d : CharacteristicReduction K R)
    (T : Subgroup R) (hT : T.Characteristic)
    (hcut : (K ⊔ T.map R.subtype) ⊓ pCore 2 H ≤ T.map R.subtype) :
    d.subgroup ≤ T := by
  let := d.characteristic
  let := hT
  have he : d.subgroup ⊓ T = d.subgroup := by
    apply eq_of_le_of_card_ge inf_le_left
    apply d.card_minimal _ inferInstance
    rw [map_inf _ _ _ R.subtype_injective]
    intro x hx
    exact ⟨d.core_containment ⟨(sup_le_sup_left inf_le_left K) hx.1,hx.2⟩,
      hcut ⟨(sup_le_sup_left inf_le_right K) hx.1,hx.2⟩⟩
  rw [←he]
  exact inf_le_right

/-- The original source produces a saturated intrinsic MS pair, with its
literal marking, inner image, and the supplied minimum replacement embedded
in the same original star. No distance is transferred to the star graph. -/
theorem exists_source_star_intrinsic_reduction (d : CharacteristicReduction K R) :
    ∃ P : Sylow 2 (Ltilde R (alpha R)), ∃ Y : Subgroup R,
      Y.map (embedS R) = componentSylowSeed R (alpha R) P ∧
      Q R (beta R) ≤ normalizer (Y.map (embedS R) : Set (FreeAmalgam R)) ∧
      d.subgroup ≤ starCentralizer R Y ∧
      (let T := (starCentralizer R Y).map R.subtype
       let M := K ⊔ T
       ∃ hs : Input (K.subgroupOf M) (T.subgroupOf M) n F,
         hs.quotientEquiv = (subgroupOfCoreQuotientEquiv le_sup_left).trans h.quotientEquiv ∧
         T.subgroupOf M = R.subgroupOf M ∧
         (normalizer (T.subgroupOf M : Set M)).pCoreIn 2 = T.subgroupOf M ∧
         K.subgroupOf M ⊔ pCore 2 M = ⊤ ∧
         ((T.subgroupOf K).map (componentProjection h)) =
           (R.subgroupOf K).map (componentProjection h) ∧
         ((∃ S : Sylow 2 M, (S : Subgroup M) = T.subgroupOf M) ↔
           ∃ S : Sylow 2 H, (S : Subgroup H) = R)) := by
  obtain ⟨P,Y,hY,hn,hmark,he,hsat⟩ := exists_source_star_marked_saturation h
  obtain ⟨geometry,hpos,_⟩ := h.positive_even_geometry
  have hZ := h.original_starSpan_le_moving_fixed geometry hpos Y P hY hn
  obtain ⟨hcut,hinner⟩ := star_cut_of_span_le h P Y hY hZ
  refine ⟨P,Y,hY,hn,minimum_le_characteristic_cut d _ inferInstance hcut,
    starInputOfRestriction h Y he,rfl,he,hsat,?_,hmark,
      star_sylow_iff_original h Y he hmark⟩
  let T := (starCentralizer R Y).map R.subtype
  let M := K ⊔ T
  let : M.Normal := star_overgroup_normal h Y
  have hcore : pCore 2 M = (pCore 2 H).comap M.subtype :=
    pCore_subnormal_eq_comap 2 (inferInstance : M.Normal).isSubnormal
  apply top_unique
  intro x _
  have hx : (x : H) ∈ K ⊔ pCore 2 H := (sup_le le_sup_left hinner) x.property
  obtain ⟨k,hk,q,hq,hkq⟩ := mem_sup_of_normal_right.mp hx
  have hqM : q ∈ M := by
    have hh := M.mul_mem (M.inv_mem (mem_sup_left hk)) x.property
    simpa only [←hkq,inv_mul_cancel_left] using hh
  have hq' : (⟨q,hqM⟩ : M) ∈ pCore 2 M := hcore.symm ▸ hq
  have hh := mul_mem_sup (show (⟨k,mem_sup_left hk⟩ : M) ∈ K.subgroupOf M from hk) hq'
  exact (show (⟨k,mem_sup_left hk⟩ : M) * ⟨q,hqM⟩ = x from Subtype.ext hkq) ▸ hh

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
