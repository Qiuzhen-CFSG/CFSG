module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.Restriction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.WholeCore
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Transport

/-!
# The characteristic replacement and its original odd-index witness

Restrict the component and its literal two-core quotient to the minimum
characteristic overgroup. The actual quotient action remains faithful, so FF
recognition constructs the natural moved quotient at the original field degree.
A whole-core Frattini bound then gives shortness and the original block model.

The original odd-index witness restricts with core R intersect the overgroup,
not with the replacement radical. On the marked component quotient, its core
is still the image of R intersect K, and it normalizes the replacement image.
This supplies the genuine witness for the later radical comparison.

Source: Aschbacher--Smith C.1.31--32, pp.135--136; MS93 (3.6)--(3.7),
pp.870--877, and Section 7, pp.932--933. The whole-core bound and field-four
restriction remain separate conclusions to be proved.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
open ChapterB.QuasisimpleSource MSCentralOrbit
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : BinaryMS.MS93.CharacteristicReduction K R)

include h

omit [Finite H] [Finite F] [CharP F 2] in
theorem original_sup : K ⊔ R = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨k,hk,r,hr,rfl⟩ := h.product x
  exact mul_mem_sup hk hr

omit [Finite F] [CharP F 2] in
theorem replacement_normal : d.overgroup.Normal := by
  let := h.component_normal
  exact d.overgroup_normal_of_sup (original_sup h)

omit [Finite H] [Finite F] [CharP F 2] in
theorem replacement_component : (K.subgroupOf d.overgroup).IsCComponent :=
  h.component.subgroupOf le_sup_left

omit [Finite F] [CharP F 2] in
theorem replacement_product :
    ∀ x : d.overgroup, ∃ k ∈ K.subgroupOf d.overgroup, ∃ r ∈ d.radical, k*r=x := by
  let := h.component_normal
  intro x
  obtain ⟨k,hk,r,hr,he⟩ := mem_sup_of_normal_left.mp x.property
  exact ⟨⟨k,mem_sup_left hk⟩,hk,⟨r,mem_sup_right hr⟩,hr,Subtype.ext he⟩

omit [Finite H] [Finite F] [CharP F 2] in
theorem replacement_isPGroup : IsPGroup 2 d.radical :=
  (h.radical.isPGroup.to_subgroup d.subgroup).of_equiv d.radicalEquiv

omit [Finite F] [CharP F 2] in
theorem replacement_residual : pResidual 2 d.overgroup = K.subgroupOf d.overgroup :=
  component_eq_residual _ _ (replacement_component h d) (replacement_isPGroup h d)
    (replacement_product h d)

omit [Finite F] [CharP F 2] in
theorem replacement_component_normal : (K.subgroupOf d.overgroup).Normal := by
  rw [←replacement_residual h d]
  infer_instance

omit [Finite F] [CharP F 2] in
theorem replacement_fitting : generalizedFitting d.overgroup = pCore 2 d.overgroup := by
  have hn := (replacement_normal h d).isSubnormal
  apply le_antisymm _ ((pCore_le_fitting _ 2).trans (fitting_le_generalizedFitting _))
  rw [pCore_subnormal_eq_comap 2 hn]
  apply map_le_iff_le_comap.mp
  rw [←h.fitting]
  exact generalizedFitting_map_subtype_le_of_isSubnormal _ hn

omit [Finite F] [CharP F 2] in
theorem replacement_selfCentralizing :
    centralizer (pCore 2 d.overgroup : Set d.overgroup) ≤ pCore 2 d.overgroup := by
  simpa only [replacement_fitting h d] using (centralizer_generalizedFitting_le d.overgroup)

omit [Finite F] [CharP F 2] in
theorem replacement_core_le : pCore 2 d.overgroup ≤ d.radical := by
  let := h.component_normal
  exact d.core_le_radical_of_sup (original_sup h)

omit [Finite H] [Finite F] [CharP F 2] in
theorem replacement_characteristic : MSCharacteristicCondition d.radical :=
  d.msCharacteristic_of_sup (original_sup h) h.characteristic

omit [Finite F] [CharP F 2] in
theorem replacement_ne_bot : d.radical ≠ ⊥ := by
  intro hr
  have hq : pCore 2 d.overgroup = ⊥ := le_bot_iff.mp (hr ▸ replacement_core_le h d)
  have ht : (⊤ : Subgroup d.overgroup) ≤ ⊥ := by
    intro x _
    have hx : x ∈ centralizer (pCore 2 d.overgroup : Set d.overgroup) := by
      rw [hq]
      intro y hy
      have hy' : y = 1 := hy
      simp only [hy',one_mul,mul_one]
    exact hq ▸ replacement_selfCentralizing h d hx
  exact (replacement_component h d).ne_bot (le_bot_iff.mp (le_top.trans ht))

@[expose] noncomputable def replacementQuotientEquiv :
    ((K.subgroupOf d.overgroup) ⧸ pCore 2 (K.subgroupOf d.overgroup)) ≃*
      Matrix.symplecticGroup (Fin 2) F :=
  (subgroupOfCoreQuotientEquiv le_sup_left).trans h.quotientEquiv

omit [Finite H] [Finite F] [CharP F 2] in
theorem replacementQuotientEquiv_mk (k : K.subgroupOf d.overgroup) :
    replacementQuotientEquiv h d (QuotientGroup.mk' _ k) =
      h.quotientEquiv (QuotientGroup.mk' (pCore 2 K) (subgroupOfEquivOfLe le_sup_left k)) := rfl

omit [Finite H] in
theorem replacement_quotient_simple :
    IsSimpleGroup ((K.subgroupOf d.overgroup) ⧸ pCore 2 (K.subgroupOf d.overgroup)) := by
  let := h.quotient_simple
  exact (subgroupOfCoreQuotientEquiv (show K ≤ d.overgroup from le_sup_left)).isSimpleGroup

theorem replacement_omegaOrbit_centralizer :
    centralizer (omegaOrbit d.radical : Set d.overgroup) = pCore 2 d.overgroup := by
  let := replacement_component_normal h d
  let := replacement_quotient_simple h d
  exact MSCentralOrbit.omegaOrbit_centralizer (K.subgroupOf d.overgroup) d.radical
    (replacement_isPGroup h d) (replacement_ne_bot h d) (replacement_core_le h d)
    (replacement_selfCentralizing h d) (replacement_product h d)
    (replacement_characteristic h d)

theorem replacement_centralOmega_centralizer :
    centralizer (omegaCenterIn (pCore 2 d.overgroup) : Set d.overgroup) =
      pCore 2 d.overgroup :=
  MSCentralOrbit.centralOmega_centralizer d.radical (replacement_core_le h d)
    (replacement_selfCentralizing h d) (replacement_omegaOrbit_centralizer h d)

theorem replacement_centralOmega_isFFModule :
    IsFFModule (NormalElementaryQuotient.representation
      (omegaCenterIn (pCore 2 d.overgroup)) (QuotientGroup.mk' (pCore 2 d.overgroup))
      (QuotientGroup.mk'_surjective _)
      ((QuotientGroup.ker_mk' _).trans (replacement_centralOmega_centralizer h d).symm)) :=
  MSCentralOrbit.centralOmega_isFFModule d.radical (replacement_characteristic h d)
    (replacement_isPGroup h d) (replacement_ne_bot h d) (replacement_core_le h d)
    (replacement_selfCentralizing h d) (replacement_omegaOrbit_centralizer h d)
    (QuotientGroup.mk' (pCore 2 d.overgroup)) (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _)

theorem replacement_component_image_structure :
    let C := (K.subgroupOf d.overgroup).map (QuotientGroup.mk' (pCore 2 d.overgroup))
    (K.subgroupOf d.overgroup).Normal ∧ C.Normal ∧ IsSimpleGroup C ∧ IsQuasisimple C ∧
      centralizer (C : Set (d.overgroup ⧸ pCore 2 d.overgroup)) = ⊥ := by
  let := replacement_quotient_simple h d
  exact MSCentralOrbit.component_image_structure _ _ (replacement_component h d)
    (replacement_isPGroup h d) (replacement_product h d)

omit [Finite F] [CharP F 2] in
theorem replacement_component_image_card :
    Nat.card ((K.subgroupOf d.overgroup).map (QuotientGroup.mk' (pCore 2 d.overgroup))) =
      Nat.card (Matrix.symplecticGroup (Fin 2) F) :=
  (Nat.card_congr (cComponentTwoCoreQuotientEquiv (replacement_component h d)).symm.toEquiv).trans
    (Nat.card_congr (replacementQuotientEquiv h d).toEquiv)

omit [Finite F] [CharP F 2] in
theorem replacement_component_image_sqtk : IsSQTK KnownSimple.IsKnownSimple
    ((K.subgroupOf d.overgroup).map (QuotientGroup.mk' (pCore 2 d.overgroup))) := by
  have hk := (h.sqtk.subgroup d.overgroup).subgroup (K.subgroupOf d.overgroup)
  have hq : IsSQTK KnownSimple.IsKnownSimple
      ((K.subgroupOf d.overgroup) ⧸ pCore 2 (K.subgroupOf d.overgroup)) := by
    refine ⟨?_,hk.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    rw [primeRank_quotient_eq_of_isTwoGroup p ho _ pCore_isPGroup]
    exact hk.stronglyQuasithin p hp ho
  exact (IsSQTK.equiv (cComponentTwoCoreQuotientEquiv (replacement_component h d))).mp hq

theorem replacement_centralOmega_moved_natural :
    let C := (K.subgroupOf d.overgroup).map (QuotientGroup.mk' (pCore 2 d.overgroup))
    let : C.Normal := (replacement_component_image_structure h d).2.1
    let ρ := NormalElementaryQuotient.representation
      (omegaCenterIn (pCore 2 d.overgroup)) (QuotientGroup.mk' (pCore 2 d.overgroup))
      (QuotientGroup.mk'_surjective _)
      ((QuotientGroup.ker_mk' _).trans (replacement_centralOmega_centralizer h d).symm)
    IsIrrPlus ρ C (subspaceCommutator ρ ⊤ C) ∧
      ∃ E : BinaryField, E.degree = n ∧
        Nonempty (ActionEquiv ((MovedSection.ofNormal ρ C).action.comp C.subtype)
          (binarySymplectic E)) := by
  obtain ⟨hK,hC,hs,hq,hcent⟩ := replacement_component_image_structure h d
  let := hK
  let := hC
  let := hs
  let := hq
  dsimp only
  apply ff_card_sp_moved_natural _ _ F h.field_card h.nonbinary
    (replacement_component_image_card h d) hcent (replacement_component_image_sqtk h d)
  · exact NormalElementaryQuotient.representation_injective _ _ _ _
  · exact replacement_centralOmega_isFFModule h d

/-- Whole-core recognition can be performed in the replacement group without
asserting that its radical has an odd-index witness. -/
theorem short_and_natural_of_replacement_frattini_small
    (hsmall : ⁅pCore 2 d.overgroup,K.subgroupOf d.overgroup⁆ ≤
      (frattini (pCore 2 d.overgroup)).map (pCore 2 d.overgroup).subtype ⊔
        omegaCenterIn (pCore 2 d.overgroup)) :
    IsShort K ∧ ∃ E : BinaryField, E.degree = n ∧
      IsLinearBlockModel K (binarySymplectic E) := by
  obtain ⟨hK,hC,hs,hq,_⟩ := replacement_component_image_structure h d
  let := hK
  let := hC
  let := hs
  let := hq
  let := (replacement_component h d).perfect
  have hperfect : IsPPerfect 2 (K.subgroupOf d.overgroup) := by
    rw [←replacement_residual h d]
    exact isPPerfect_pResidual 2
  obtain ⟨he,helem,hcentral⟩ :=
    intrinsic_core_of_frattini_small (K.subgroupOf d.overgroup) hperfect hsmall
  obtain ⟨hi,E,hE,⟨e⟩⟩ := replacement_centralOmega_moved_natural h d
  have hfitK : generalizedFitting (K.subgroupOf d.overgroup) =
      pCore 2 (K.subgroupOf d.overgroup) := by
    apply le_antisymm _ ((pCore_le_fitting _ 2).trans (fitting_le_generalizedFitting _))
    rw [pCore_subnormal_eq_comap 2 (replacement_component h d).subnormal]
    apply map_le_iff_le_comap.mp
    rw [←replacement_fitting h d]
    exact generalizedFitting_map_subtype_le_of_isSubnormal _ (replacement_component h d).subnormal
  let q := QuotientGroup.mk' (pCore 2 d.overgroup)
  let hk := (QuotientGroup.ker_mk' _).trans (replacement_centralOmega_centralizer h d).symm
  have hshort : IsShort (K.subgroupOf d.overgroup) :=
    ⟨inferInstance,hperfect,hfitK,helem,hcentral,
      Or.inl (IsQuasisimple.of_mulEquiv
        (cComponentTwoCoreQuotientEquiv (replacement_component h d)).symm),
      BlockMovingSection.irreducible_of_moving (omegaCenterIn (pCore 2 d.overgroup))
        (K.subgroupOf d.overgroup) q (QuotientGroup.mk'_surjective _) hk he hi⟩
  have hmodel : IsLinearBlockModel (K.subgroupOf d.overgroup) (binarySymplectic E) :=
    BlockMovingSection.model_of_moving (omegaCenterIn (pCore 2 d.overgroup))
      (K.subgroupOf d.overgroup) q (QuotientGroup.mk'_surjective _) hk he
      (cComponentTwoCoreQuotientEquiv (replacement_component h d)) (fun _ => rfl) _ e
  let eK : K.subgroupOf d.overgroup ≃* K := subgroupOfEquivOfLe le_sup_left
  exact ⟨hshort.of_mulEquiv eK,E,hE,hmodel.of_mulEquiv eK⟩

/-- The degree-two reduced whole-core branch returns the original component,
with its intrinsic quotient and conjugation model. -/
theorem block_of_degree_two_replacement_frattini_small (hn : n = 2)
    (hsmall : ⁅pCore 2 d.overgroup,K.subgroupOf d.overgroup⁆ ≤
      (frattini (pCore 2 d.overgroup)).map (pCore 2 d.overgroup).subtype ⊔
        omegaCenterIn (pCore 2 d.overgroup)) : IsSp4FourBlock K := by
  obtain ⟨hs,E,hE,ρ,hmodel,hact⟩ :=
    short_and_natural_of_replacement_frattini_small h d hsmall
  refine ⟨hs,E.Carrier,inferInstance,inferInstance,?_,ρ,hmodel,hact⟩
  rw [E.card_eq,hE,hn]
  decide

omit h [Finite F] [CharP F 2] in
private theorem relative_index_dvd_of_normal_right (A J : Subgroup H) [J.Normal] :
    (A.subgroupOf J).index ∣ A.index := by
  have he : A.relIndex J * J.index = A.relIndex (A ⊔ J) * J.index := by
    calc
      _ = (A ⊓ J).index := by
        rw [←inf_relIndex_right A J]
        exact relIndex_mul_index inf_le_right
      _ = J.relIndex A * A.index := by
        rw [←inf_relIndex_left A J]
        exact (relIndex_mul_index inf_le_left).symm
      _ = J.relIndex A * (A.relIndex (A ⊔ J) * (A ⊔ J).index) := by
        rw [relIndex_mul_index le_sup_left]
      _ = A.relIndex (A ⊔ J) * (J.relIndex A * (A ⊔ J).index) := by ac_rfl
      _ = _ := by rw [←relIndex_sup_right A J,relIndex_mul_index le_sup_right]
  have hi : A.relIndex J = A.relIndex (A ⊔ J) :=
    mul_right_cancel₀ J.index_ne_zero_of_finite he
  change A.relIndex J ∣ A.index
  rw [hi]
  exact relIndex_dvd_index_of_le le_sup_left

omit h [Finite F] [CharP F 2] in
private theorem restricted_core_of_normal (A J : Subgroup H) [J.Normal] :
    (A.subgroupOf J).pCoreIn 2 = (A.pCoreIn 2).subgroupOf J := by
  let e : A.subgroupOf J ≃* J.subgroupOf A := {
    toFun x := ⟨⟨x.val.val,x.property⟩,x.val.property⟩
    invFun x := ⟨⟨x.val.val,x.property⟩,x.val.property⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_mul' _ _ := rfl }
  have hn : (J.subgroupOf A).Normal := inferInstance
  apply map_injective J.subtype_injective
  change ((pCore 2 (A.subgroupOf J)).map (A.subgroupOf J).subtype).map J.subtype = _
  calc
    _ = ((pCore 2 (A.subgroupOf J)).map e.toMonoidHom).map
        (A.subtype.comp (J.subgroupOf A).subtype) := by rw [map_map,map_map]; rfl
    _ = (pCore 2 (J.subgroupOf A)).map (A.subtype.comp (J.subgroupOf A).subtype) := by
      rw [pCore_map_iso]
    _ = ((J.subgroupOf A) ⊓ pCore 2 A).map A.subtype := by
      rw [pCore_subnormal_eq_comap 2 hn.isSubnormal,←map_map,map_comap_eq,range_subtype]
    _ = (A ⊓ J) ⊓ A.pCoreIn 2 := by
      rw [map_inf _ _ _ A.subtype_injective,subgroupOf_map_subtype,inf_comm J A]
      rfl
    _ = J ⊓ A.pCoreIn 2 := by
      rw [inf_assoc,inf_left_comm,inf_eq_right.mpr (A.pCoreIn_le 2)]
    _ = _ := by rw [subgroupOf_map_subtype, inf_comm]

omit [Finite F] [CharP F 2] in
/-- The original witness restricts with core R intersect the replacement
overgroup. It does not assert that this core is the replacement radical. -/
theorem original_witness_restricted :
    ∃ A : Subgroup H, A < ⊤ ∧ Odd A.index ∧ A.pCoreIn 2 = R ∧
      A.subgroupOf d.overgroup < ⊤ ∧ Odd (A.subgroupOf d.overgroup).index ∧
      (A.subgroupOf d.overgroup).pCoreIn 2 = R.subgroupOf d.overgroup ∧
      d.radical ≤ R.subgroupOf d.overgroup ∧
      A.subgroupOf d.overgroup ≤ normalizer (d.radical : Set d.overgroup) := by
  obtain ⟨A,hA,hodd,hcore⟩ := h.radical
  have hRA : R ≤ A := hcore ▸ map_subtype_le (pCore 2 A)
  let := replacement_normal h d
  have hcore' : (A.subgroupOf d.overgroup).pCoreIn 2 = R.subgroupOf d.overgroup := by
    rw [restricted_core_of_normal]
    exact congrArg (fun B : Subgroup H => B.subgroupOf d.overgroup) hcore
  refine ⟨A,hA,hodd,hcore,lt_top_iff_ne_top.mpr ?_,
    hodd.of_dvd_nat (relative_index_dvd_of_normal_right A d.overgroup),hcore',?_,?_⟩
  · intro he
    have hJA : d.overgroup ≤ A := subgroupOf_eq_top.mp he
    have hKA : K ≤ A := le_sup_left.trans hJA
    exact hA.not_ge ((original_sup h) ▸ sup_le hKA hRA)
  · intro x hx
    obtain ⟨r,hr,he⟩ := hx
    change (x : H) ∈ R
    change (r : H) = (x : H) at he
    exact he ▸ r.property
  · let := d.characteristic
    have hAn : A ≤ normalizer (R : Set H) := by
      rw [←hcore]
      exact normalizer_le_normalizer_characteristic_image A (pCore 2 A) |>.trans' A.le_normalizer
    have hAd : A ≤ normalizer (d.ambient : Set H) :=
      hAn.trans (normalizer_le_normalizer_characteristic_image R d.subgroup)
    intro a ha
    apply mem_normalizer_iff.mpr
    intro x
    exact (mem_normalizer_iff.mp (hAd ha)) x.val

omit [Finite F] [CharP F 2] in
/-- The original odd-index witness restricts to the component, and normalizes
the intersection of the replacement with that component. -/
theorem original_component_witness :
    ∃ A : Subgroup K, A < ⊤ ∧ Odd A.index ∧
      A.pCoreIn 2 = R.subgroupOf K ∧
      A ≤ normalizer (d.ambient.subgroupOf K : Set K) := by
  obtain ⟨A,hA,hodd,hcore⟩ := h.radical
  have hRA : R ≤ A := hcore ▸ map_subtype_le (pCore 2 A)
  let := h.component_normal
  refine ⟨A.subgroupOf K,lt_top_iff_ne_top.mpr ?_,
    hodd.of_dvd_nat (relative_index_dvd_of_normal_right A K),?_,?_⟩
  · intro he
    exact hA.not_ge ((original_sup h) ▸ sup_le (subgroupOf_eq_top.mp he) hRA)
  · rw [restricted_core_of_normal]
    exact congrArg (fun B : Subgroup H => B.subgroupOf K) hcore
  · let := d.characteristic
    have hAn : A ≤ normalizer (R : Set H) := by
      rw [←hcore]
      exact A.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image A (pCore 2 A))
    have hAd : A ≤ normalizer (d.ambient : Set H) :=
      hAn.trans (normalizer_le_normalizer_characteristic_image R d.subgroup)
    intro a ha
    apply mem_normalizer_iff.mpr
    intro x
    exact (mem_normalizer_iff.mp (hAd ha)) x.val

/-- The original marking, on representatives of the actual component. -/
@[expose] noncomputable def componentProjection :
    K →* Matrix.symplecticGroup (Fin 2) F :=
  h.quotientEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))

omit [Finite H] [Finite F] [CharP F 2] in
theorem componentProjection_surjective : Function.Surjective (componentProjection h) :=
  h.quotientEquiv.surjective.comp (QuotientGroup.mk'_surjective _)

omit [Finite H] [Finite F] [CharP F 2] in
theorem componentProjection_kernel : (componentProjection h).ker = pCore 2 K := by
  rw [componentProjection,MonoidHom.ker_comp_of_injective _ _ h.quotientEquiv.injective,
    QuotientGroup.ker_mk']

omit [CharP F 2] in
/-- A proper odd-index witness on the literal symplectic quotient. Its core
is the image of the original R intersect K, while its normalizer action also
preserves the smaller characteristic replacement intersect K. -/
theorem original_marked_witness :
    ∃ A : Subgroup (Matrix.symplecticGroup (Fin 2) F), A < ⊤ ∧ Odd A.index ∧
      A.pCoreIn 2 = (R.subgroupOf K).map (componentProjection h) ∧
      A ≤ normalizer ((d.ambient.subgroupOf K).map (componentProjection h) :
        Set (Matrix.symplecticGroup (Fin 2) F)) := by
  obtain ⟨A,hA,hodd,hcore,hnorm⟩ := original_component_witness h d
  let q := componentProjection h
  have hq : Function.Surjective q := componentProjection_surjective h
  have hk : IsPGroup 2 q.ker := by
    rw [componentProjection_kernel]
    exact pCore_isPGroup
  have hkA : q.ker ≤ A := by
    rw [componentProjection_kernel]
    exact (pCore_le_map_pCore_of_prime_not_dvd_index A hodd.not_two_dvd_nat).trans
      (map_subtype_le _)
  refine ⟨A.map q,lt_top_iff_ne_top.mpr ?_,hodd.of_dvd_nat (A.index_map_dvd hq),?_,?_⟩
  · intro he
    have he' := congrArg (fun B => B.comap q) he
    rw [comap_map_eq_self hkA,comap_top] at he'
    exact hA.ne he'
  · rw [←map_pCoreIn_of_ker_isPGroup q hk,hcore]
  · exact (map_mono hnorm).trans ((d.ambient.subgroupOf K).le_normalizer_map q)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
