module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.Components.SolvableContaining
public import Theory.SpecificGroups.Janko1.Model.Certification.Order
public import Theory.GroupTheory.PrimeRankSquareFree

/-!
# The J₁ containing-component row of the half-Sylow argument

No distinctness or cubic-divisor assumption is needed for this row. For a
strict constrained containing component, the actual J₁ order bounds its
three-rank by one and supplies a factor of five. C.2.7 therefore identifies
its literal two-core quotient with binary SL₂. Solvability of proper full-
Sylow overgroups contradicts strict containment of the original local factor.

In the nonconstrained branch, module choice removes the ambient odd core,
so the containing component is quasisimple. Every perfect subgroup of J₁
has central two-core. Lifting through the actual central quotient kernel
would make the original moved component quasisimple, a contradiction.

Thus either original factor equals any containing component with J₁ quotient.
Equality proves that the two containing components are distinct and transports
J₁'s cubic divisor to the original quotient. The proved ranked-enlargement
contradiction now excludes the literal pair, keeping the same exchanger and
half-join throughout.

The other containing rows, the three-free enlargement, the zero-kernel
binary-three normalizer and final assembly remain with
qt-d-10-nona5-half-sylow-unique. ModuleChoiceAt is the independent input from
qt-d-10-nona5-point-selection; qt-d-10-nona5-point-control retains its final
discharge. No unconditional half-Sylow uniqueness theorem is asserted here.
Source: Aschbacher--Smith A.3.12, C.2.7 and 10.2.6,
printed pp.47--48,145--147,748--749.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Chapter3.Section02 Chapter1
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {H : Subgroup G} {t : G} {K₁ K₂ : Subgroup H}

/-- A J₁ quotient cannot contain the original moved component in a quasisimple group. -/
private theorem not_quasisimple_janko_one_overgroup {s : G} {K : Subgroup G}
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hBK : L.map (MulAut.conj s).toMonoidHom ≤ K) [IsQuasisimple K]
    (dK : (K ⧸ pCore 2 K) ≃* Janko1.Model) : False := by
  let B := (L.map (MulAut.conj s).toMonoidHom).subgroupOf K
  let eB : L ≃* B := ((MulAut.conj s).subgroupMap L).trans
    (subgroupOfEquivOfLe hBK).symm
  let q : L →* Janko1.Model := (dK.toMonoidHom.comp
    (QuotientGroup.mk' (pCore 2 K))).comp (B.subtype.comp eB.toMonoidHom)
  have hk : q.ker ≤ center L := by
    intro l hl
    have he : dK (QuotientGroup.mk (eB l : K)) = 1 := hl
    have hz := IsQuasisimple.pCore_le_center 2
      ((QuotientGroup.eq_one_iff (eB l : K)).mp (dK.map_eq_one_iff.mp he))
    apply mem_center_iff.mpr
    intro m
    apply eB.injective
    simp only [map_mul]
    apply Subtype.ext
    exact mem_center_iff.mp hz (eB m : K)
  let := mem_L_isPerfect D.maximal.1
  let f : PerfectCentralCovering.Cover L q.range := {
    toMonoidHom := q.rangeRestrict
    surjective := q.rangeRestrict_surjective
    isPerfect := inferInstance
    ker_le_center := fun l hl => hk (congrArg Subtype.val hl) }
  let : Group.IsPerfect q.range := Group.IsPerfect.range q
  have hm : (pCore 2 L).map q.rangeRestrict ≤ pCore 2 q.range :=
    le_sSup ⟨(inferInstance : (pCore 2 L).Normal).map _ q.rangeRestrict_surjective,
      pCore_isPGroup.map q.rangeRestrict⟩
  have hc : pCore 2 L ≤ center L := by
    rw [←f.comap_center]
    exact map_le_iff_le_comap.mp (hm.trans (Janko1.perfect_subgroup_pCore_two_le_center q.range))
  let := D.quasisimple
  exact source_component_not_quasisimple D (show PerfectCentralCovering.Cover L (L ⧸ pCore 2 L) from {
    toMonoidHom := QuotientGroup.mk' (pCore 2 L)
    surjective := QuotientGroup.mk'_surjective _
    isPerfect := inferInstance
    ker_le_center := by simpa only [QuotientGroup.ker_mk'] using hc }).isQuasisimple

/-- Both original C.2.7 Fitting branches exclude a strict J₁ containing quotient. -/
theorem ContainingPair.not_janko_one_quotient_of_strict
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    {s : G} (hs : s ∈ (T : Subgroup G)) {K : Subgroup G}
    (hK : K ∈ cComponentsIn H) (hKN : (K.subgroupOf H).Normal)
    (hBK : L.map (MulAut.conj s).toMonoidHom < K)
    (dK : (K ⧸ pCore 2 K) ≃* Janko1.Model) : False := by
  by_cases hf : generalizedFitting K = pCore 2 K
  · have hrJ : primeRank 3 Janko1.Model ≤ 1 :=
      primeRank_le_one_of_square_not_dvd (by rw [Janko1.card_model]; decide)
    have hr : primeRank 3 K ≤ 1 := by
      rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 K) pCore_isPGroup,
        primeRank_equiv 3 dK]
      exact hrJ
    have h5 : 5 ∣ Nat.card (K ⧸ pCore 2 K) := by
      rw [Nat.card_congr dK.toEquiv,Janko1.card_model]
      decide
    obtain ⟨F,⟨e⟩⟩ := source_rank_one_coreQuotient_linearTwo
      (C.c27_input_of_strict hn hs hK hKN hBK hf) hr h5
    exact hBK.ne (C.eq_of_solvable_sylow_quotient hs hK hBK.le
      (SolvableSylowOvergroups.of_equiv e
        Matrix.SpecialLinearGroup.isSolvable_of_proper_sylow_overgroup))
  · have hq : IsQuasisimple K := by
      let j := subgroupOfEquivOfLe hK.1
      rcases hK.2.component_or_generalizedFitting_eq_pCore
        (oddCore_eq_bot_of_moduleChoice hchoice hmany D hn hna C.half_le) with hq | he
      · let := hq.2
        exact IsQuasisimple.of_mulEquiv j
      · apply (hf ?_).elim
        have hm := congrArg (Subgroup.map j.toMonoidHom) he
        simpa only [map_generalizedFitting_equiv,pCore_map_iso] using hm
    let := hq
    exact not_quasisimple_janko_one_overgroup D hBK.le dK

/-- The first original factor must equal a containing component with J₁ quotient. -/
theorem ContainingPair.first_eq_of_janko_one_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (d : (K₁ ⧸ pCore 2 K₁) ≃* Janko1.Model) : L.subgroupOf H = K₁ := by
  by_contra he
  have hmap : (K₁.map H.subtype).subgroupOf H = K₁ :=
    comap_map_eq_self_of_injective H.subtype_injective K₁
  have hstrict := (map_lt_map_iff_of_injective H.subtype_injective).mpr
    (lt_of_le_of_ne C.first_le he)
  rw [map_subgroupOf_eq_of_le C.left_le] at hstrict
  have hid : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by ext x; simp
  rw [←Subgroup.map_id L,←hid] at hstrict
  let a := (K₁.equivMapOfInjective H.subtype H.subtype_injective).symm
  let b := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  exact C.not_janko_one_quotient_of_strict hchoice hmany hn hna (one_mem _)
    ⟨map_subtype_le _,hmap.symm ▸ C.first_component⟩ (hmap.symm ▸ C.first_normal)
    hstrict (b.trans d)

/-- Equality for the second factor retains the actual source exchanger. -/
theorem ContainingPair.second_eq_of_janko_one_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (d : (K₂ ⧸ pCore 2 K₂) ≃* Janko1.Model) :
    (L.map (MulAut.conj t).toMonoidHom).subgroupOf H = K₂ := by
  by_contra he
  have hmap : (K₂.map H.subtype).subgroupOf H = K₂ :=
    comap_map_eq_self_of_injective H.subtype_injective K₂
  have hstrict := (map_lt_map_iff_of_injective H.subtype_injective).mpr
    (lt_of_le_of_ne C.second_le he)
  rw [map_subgroupOf_eq_of_le C.right_le] at hstrict
  let a := (K₂.equivMapOfInjective H.subtype H.subtype_injective).symm
  let b := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  exact C.not_janko_one_quotient_of_strict hchoice hmany hn hna C.t_mem
    ⟨map_subtype_le _,hmap.symm ▸ C.second_component⟩ (hmap.symm ▸ C.second_normal)
    hstrict (b.trans d)

/-- A J₁ quotient of the first containing component excludes the literal pair. -/
theorem ContainingPair.impossible_of_first_janko_one_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (d : (K₁ ⧸ pCore 2 K₁) ≃* Janko1.Model) : False := by
  have he := C.first_eq_of_janko_one_quotient hchoice hmany hn hna d
  have hne : K₁ ≠ K₂ := by
    intro h
    have hi := map_mono (f := H.subtype) C.second_le
    rw [map_subgroupOf_eq_of_le C.right_le,←h,←he,
      map_subgroupOf_eq_of_le C.left_le] at hi
    exact C.t_not_normalizes (mem_normalizer_iff_map_conj_eq.mpr
      (Subgroup.eq_of_le_of_card_ge hi (card_map_of_injective (MulAut.conj t).injective).ge))
  let a : L ≃* K₁ := (subgroupOfEquivOfLe C.left_le).symm.trans (MulEquiv.subgroupCongr he)
  let b := (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans d
  apply C.impossible_of_distinct_three hchoice hmany hn hna hne
  rw [Nat.card_congr b.toEquiv,Janko1.card_model]
  decide

/-- The second containing quotient supplies distinctness and the cubic divisor with the same exchanger. -/
theorem ContainingPair.impossible_of_second_janko_one_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (d : (K₂ ⧸ pCore 2 K₂) ≃* Janko1.Model) : False := by
  have he := C.second_eq_of_janko_one_quotient hchoice hmany hn hna d
  have hne : K₁ ≠ K₂ := by
    intro h
    have hi := map_mono (f := H.subtype) C.first_le
    rw [map_subgroupOf_eq_of_le C.left_le,h,←he,
      map_subgroupOf_eq_of_le C.right_le] at hi
    have hi' := Subgroup.eq_of_le_of_card_ge hi
      (card_map_of_injective (MulAut.conj t).injective).le
    exact C.t_not_normalizes (mem_normalizer_iff_map_conj_eq.mpr hi'.symm)
  let a : L ≃* K₂ := ((MulAut.conj t).subgroupMap L).trans
    ((subgroupOfEquivOfLe C.right_le).symm.trans (MulEquiv.subgroupCongr he))
  let b := (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans d
  apply C.impossible_of_distinct_three hchoice hmany hn hna hne
  rw [Nat.card_congr b.toEquiv,Janko1.card_model]
  decide

/-- Either actual J₁ quotient is excluded without a distinctness or divisibility callback. -/
theorem ContainingPair.impossible_of_janko_one_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (he : Nonempty ((K₁ ⧸ pCore 2 K₁) ≃* Janko1.Model) ∨
      Nonempty ((K₂ ⧸ pCore 2 K₂) ≃* Janko1.Model)) : False := by
  rcases he with he | he
  all_goals obtain ⟨e⟩ := he
  · exact C.impossible_of_first_janko_one_quotient hchoice hmany hn hna e
  · exact C.impossible_of_second_janko_one_quotient hchoice hmany hn hna e
end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
