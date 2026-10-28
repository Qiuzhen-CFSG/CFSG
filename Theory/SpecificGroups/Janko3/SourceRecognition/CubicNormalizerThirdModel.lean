module
public import Theory.SpecificGroups.Janko3.SourceRecognition.CubicNormalizerModelPair
public import Theory.SpecificGroups.AlternatingSix.PGLNineFiveContaining
public import Theory.SpecificGroups.AlternatingSix.PGLNineOuterCentralizer
public import Theory.SpecificGroups.AlternatingSix.PGLNineTwentyConjugacy

/-!
# A fixed third-overlap model in the cubic normalizer

The fixed Sylow-five subgroup is contained in an actual A₅. Its normalizer
inside that A₅ is the full intersection of the projective pair with the
derived subgroup. This gives a source-independent third overlap. A genuine
outer involution centralizes the entire projective pair, supplying the
pair-fixing correction used to align any other such A₅ overlap.
-/

public noncomputable section
namespace Sporadic.Janko3.SourceRecognition.CubicNormalizerModel
open Subgroup
open Atlas.Comparisons.Exceptional GorensteinWalter

/-- The projective quotient of the full order-sixty pair. -/
@[expose] def projectivePair : Subgroup P := normalizer (five : Set P)
/-- Its original derived intersection of order ten. -/
@[expose] def pairTen : Subgroup P := projectivePair ⊓ derived

private theorem odd : IsOddPrimePower (Nat.card Nine.F) := by
  rw [Nine.card]
  exact ⟨3,2,by decide,by decide,by decide,by decide⟩
private theorem large : 3 < Nat.card Nine.F := by rw [Nine.card]; decide

private theorem derived_eq : derived = Matrix.ProjectiveSpecialLinearGroup.toPGL.range :=
  pgl2_commutator_eq_psl2_range_of_card_gt_three Nine.F odd large
private def derivedEquiv : derived ≃* alternatingGroup (Fin 6) :=
  (MulEquiv.subgroupCongr derived_eq).trans
    ((psl2EquivToPGLRange Nine.F).symm.trans psl2NineCoordinatesEquivAlt6)

/-- The literal projective pair has order twenty. -/
theorem projectivePair_card : Nat.card projectivePair = 20 :=
  AlternatingSix.PGLNineFiveNormalizer.five_normalizer_card _ five_card

/-- The literal derived intersection of the projective pair has order ten. -/
theorem pairTen_card : Nat.card pairTen = 10 := by
  have hle : (five : Subgroup P) ≤ derived :=
    odd_card_subgroup_le_normal_index_two derived five inferInstance derived_index
      (by rw [five_card]; decide)
  have hc : Nat.card (projectivePair.subgroupOf derived) = 10 := by
    change Nat.card ((normalizer ((five : Subgroup P) : Set P)).subgroupOf derived) = 10
    rw [subgroupOf_normalizer_eq hle]
    rw [←card_map_of_injective (f := derivedEquiv.toMonoidHom) derivedEquiv.injective,
      map_equiv_normalizer_eq]
    apply AlternatingSix.PGLNineFiveNormalizer.alternating_five_normalizer_card
    rw [card_map_of_injective derivedEquiv.injective,
      Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv,five_card]
  have hm : (projectivePair.subgroupOf derived).map derived.subtype = pairTen := by
    rw [subgroupOf_map_subtype]
    rfl
  rw [←hm,card_map_of_injective derived.subtype_injective,hc]

theorem exists_third_five :
    ∃ H : Subgroup P, pairTen ≤ H ∧ Nonempty (H ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨H,hfive,hH⟩ := AlternatingSix.PGLNineFivePairs.exists_five_overgroup
    (five : Subgroup P) five_card
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect H := Group.IsPerfect.ofSurjective
    (f := hH.some.symm.toMonoidHom) hH.some.symm.surjective
  have hHd : H ≤ derived := by
    rw [←H.commutator_eq_self]
    exact commutator_mono le_top le_top
  let R := (five : Subgroup P).subgroupOf H
  let D := (normalizer (R : Set H)).map H.subtype
  have hD : Nat.card D = 10 := by
    rw [card_map_of_injective H.subtype_injective,
      ←card_map_of_injective (f := hH.some.toMonoidHom) hH.some.injective,
      map_equiv_normalizer_eq]
    apply alternatingGroup.FiveLocalGeometry.five_normalizer_card
    rw [card_map_of_injective hH.some.injective,
      Nat.card_congr (subgroupOfEquivOfLe hfive).toEquiv,five_card]
  have hle : D ≤ pairTen := by
    apply le_inf
    · change D ≤ normalizer (five : Set P)
      have hh := R.le_normalizer_map H.subtype
      rw [map_subgroupOf_eq_of_le hfive] at hh
      exact hh
    · exact (map_subtype_le _).trans hHd
  have he : D = pairTen := eq_of_le_of_card_ge hle (by rw [hD,pairTen_card])
  exact ⟨H,he ▸ map_subtype_le _,hH⟩

/-- A fixed actual A₅ overgroup of the pair's order-ten subgroup. -/
@[expose] def thirdFive : Subgroup P := exists_third_five.choose

theorem pairTen_le_thirdFive : pairTen ≤ thirdFive := exists_third_five.choose_spec.1

theorem thirdFive_equiv : Nonempty (thirdFive ≃* alternatingGroup (Fin 5)) :=
  exists_third_five.choose_spec.2

/-- The fixed full third overlap, retaining the cubic kernel. -/
@[expose] def thirdOverlap : Subgroup Model := thirdFive.comap projection

/-- A genuine outer projective involution centralizes the full projective
pair; it is constructed entirely inside the fixed matrix model. -/
theorem exists_projective_pair_inverter :
    ∃ t : P, orderOf t = 2 ∧ t ∉ derived ∧
      t ∈ centralizer (projectivePair : Set P) := by
  obtain ⟨U,s,u,w,_hc,_hh,_hcard,_hsU,hsout,hsne,hssq,
      _huU,_huout,_husq,_huinv,_huw,_hwout,_hwsq,_hwinv,_hcent⟩ :=
    pgl2_low_two_part_torus_reflection_data Nine.F odd large
  have hs : orderOf s = 2 := orderOf_eq_prime (by simpa only [pow_two] using hssq) hsne
  let C := centralizer ({s} : Set P)
  have hc : Nat.card C = 20 :=
    AlternatingSix.PGLNineOuterCentralizer.outer_involution_centralizer_card s hs hsout
  obtain ⟨g,hg⟩ := AlternatingSix.PGLNineFiveNormalizer.twenty_subgroups_conjugate
    C projectivePair hc projectivePair_card
  let e := MulAut.conj g
  refine ⟨e s,e.orderOf_eq s |>.trans hs,?_,?_⟩
  · intro hd
    have hh := (inferInstance : derived.Normal).conj_mem (e s) hd g⁻¹
    apply hsout
    simpa [e,MulAut.conj_apply,mul_assoc] using hh
  · intro x hx
    obtain ⟨c,hc,rfl⟩ := hg.symm ▸ hx
    change e c * e s = e s * e c
    rw [←map_mul,←map_mul,mem_centralizer_singleton_iff.mp hc]
end Sporadic.Janko3.SourceRecognition.CubicNormalizerModel
