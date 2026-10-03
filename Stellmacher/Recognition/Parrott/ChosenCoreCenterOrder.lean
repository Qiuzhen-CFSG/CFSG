module

public import Stellmacher.Recognition.Parrott.ChosenCoreCenterGeometry
public import Stellmacher.Recognition.Parrott.ChosenCoreCenterLargeIntersection
public import Stellmacher.Recognition.Parrott.ChosenCoreCoveringFixed
public import Stellmacher.Recognition.Parrott.ChosenCoreCoveringLift
public import Theory.GroupTheory.PGroup.CyclicQuotientSmallKernel
public import Theory.GroupTheory.PGroup.SmallFixedThirdCommutator

/-!
# The local calculation of the chosen center

Write H=C_G(z), J=O₂(H), E=J′, and S=C_H(a), preserving the supplied
involution and fixed join F. If J∩S properly contains F, its commutators
with E∩F generate ⟨z⟩: otherwise an element outside F would centralize
both a and E∩F, contradicting C_G(F)=F. Thus z belongs to S′. Derived
weak closure then forces S′ outside E, which is the fusion obstruction
used in the center calculation. The lower bound |S|≥128 shows that an
image of order at most two modulo J suffices for this proper containment.

The conditional local-alternatives interface is retained. The exact theorem
uses the characteristic subgroup [S,S′] to exclude |Z(S)|=4. The quotient
S/(E∩S) has cyclic image modulo the core and kernel of order at most four,
so it has class at most two and [S,S′]≤E. A center of order four forces a
covering actor to fix only two elements of E∩F, an elementary group of
order sixteen. The fixed-point argument puts z in [S,S′], contradicting
derived weak closure. The existing S′ obstruction excludes center order
sixteen, leaving order eight. No assertion about the order of an actual
covering lift is needed, and the supplied witnesses remain fixed.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
printed p.676, the paragraph beginning “We claim that Z(S)”.
-/

open Subgroup
open scoped commutatorElement IsMulCommutative

namespace Stellmacher.Recognition.ParrottSecondElementaryData

variable {G : Type*} [Group G] [Finite G] {z : G}

/-- A core element of S outside F forces the original involution into S′. -/
public theorem chosen_z_mem_commutator_of_core_intersection_gt
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    d.F < J.map H.subtype ⊓ S → z ∈ (commutator S).map S.subtype := by
  intro H J S hlt
  let E := (commutator J).map (H.subtype.comp J.subtype)
  let B := J.map H.subtype ⊓ S
  let U := E ⊓ d.F
  obtain ⟨hZ, _, _, _, hupper, _, _, _⟩ := parrott_centralizer_structure z h
  have hbound : ⁅B, U⁆ ≤ zpowers z := by
    apply commutator_le.mpr
    intro b hb e he
    obtain ⟨bH, hbJ, rfl⟩ := hb.1
    obtain ⟨eJ, heJ, rfl⟩ := he.1
    let bJ : J := ⟨bH, hbJ⟩
    have heU : eJ ∈ Subgroup.upperCentralSeries J 2 := hupper ▸ heJ
    have hec : ⁅eJ, bJ⁆ ∈ center J := by
      simpa only [Subgroup.upperCentralSeries_one] using
        (Subgroup.mem_upperCentralSeries_succ_iff.mp heU bJ)
    have hbc : ⁅bJ, eJ⁆ ∈ center J := by
      simpa only [commutatorElement_inv] using (center J).inv_mem hec
    rw [← hZ]
    exact ⟨⁅bJ, eJ⁆, hbc, rfl⟩
  have hnontrivial : ⁅B, U⁆ ≠ ⊥ := by
    intro hbot
    have hBU : B ≤ centralizer (U : Set G) :=
      commutator_eq_bot_iff_le_centralizer.mp hbot
    have hBF : B ≤ d.F := by
      rw [← d.centralizer_eq]
      intro b hb
      have hCa : zpowers (d.a : G) ≤ centralizer ({b} : Set G) :=
        zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
          (mem_centralizer_singleton_iff.mp hb.2.2).symm)
      have hCU : U ≤ centralizer ({b} : Set G) := by
        intro u hu
        exact mem_centralizer_singleton_iff.mpr (hBU hb u hu)
      have hF : d.F ≤ centralizer ({b} : Set G) := by
        rw [d.fixed_join, ← d.inf_eq]
        exact sup_le hCa hCU
      intro f hf
      exact mem_centralizer_singleton_iff.mp (hF hf)
    exact (not_le_of_gt hlt) hBF
  have heq : ⁅B, U⁆ = zpowers z := by
    apply eq_of_le_of_card_ge hbound
    rw [Nat.card_zpowers, h.involution]
    exact (one_lt_card_iff_ne_bot _).mpr hnontrivial
  rw [map_subtype_commutator]
  apply commutator_mono (show B ≤ S from inf_le_right)
    (show U ≤ S from inf_le_right.trans d.le_chosen_centralizer)
  rw [heq]
  exact mem_zpowers z

/-- If S has image of order at most two modulo J, its core intersection
properly contains F, since |S|≥128 and |F|=32. -/
public theorem chosen_core_intersection_gt_of_relIndex_le_two
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let K := (pCore 2 H).map H.subtype
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    K.relIndex S ≤ 2 → d.F < K ⊓ S := by
  intro H K S hindex
  apply lt_of_le_of_ne (le_inf d.le_core d.le_chosen_centralizer)
  intro heq
  have hc := relIndex_mul_relIndex (⊥ : Subgroup G) (K ⊓ S) S bot_le inf_le_right
  rw [relIndex_bot_left, relIndex_bot_left, inf_relIndex_right, ← heq, d.card] at hc
  have hlarge := d.chosen_centralizer_card_ge h
  change 128 ≤ Nat.card S at hlarge
  nlinarith

/-- Weak closure excludes an abelian image modulo E once J∩S exceeds F. -/
public theorem chosen_commutator_not_le_derived_of_core_intersection_gt
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z)
    (hconj : IsConj z (d.a : G))
    (hderived : ∀ t : G, t ∈ (commutator (pCore 2 (centralizer ({z} : Set G)))).map
      ((centralizer ({z} : Set G)).subtype.comp
        (pCore 2 (centralizer ({z} : Set G))).subtype) → IsConj z t → t = z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    d.F < J.map H.subtype ⊓ S →
      ¬ (commutator S).map S.subtype ≤ (commutator J).map (H.subtype.comp J.subtype) := by
  intro H J S hlt
  exact d.chosen_characteristic_not_le_derived h hconj hderived (commutator S)
    inferInstance (d.chosen_z_mem_commutator_of_core_intersection_gt h hlt)

/-- The index-two center geometry turns the local order-four calculation into
exactly the requested order-eight center statement. -/
public theorem chosen_center_card_eight_iff_derived_intersection
    (d : ParrottSecondElementaryData z) :
    let H := centralizer ({z} : Set G)
    let E := (commutator (pCore 2 H)).map (H.subtype.comp (pCore 2 H).subtype)
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    let Z := (center S).map S.subtype
    Nat.card (center S) = 8 ↔ Nat.card (E ⊓ Z : Subgroup G) = 4 := by
  intro H E S Z
  have hcard := d.chosen_center_derived_index.2
  change Nat.card Z = 2 * Nat.card (E ⊓ Z : Subgroup G) at hcard
  have hmap : Nat.card Z = Nat.card (center S) :=
    card_map_of_injective S.subtype_injective
  omega

/-- Assembly of the local alternatives using derived weak closure. The second
alternative is ruled out by the characteristic subgroup S′. -/
public theorem chosen_center_card_eight_of_local_alternatives
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z)
    (hconj : IsConj z (d.a : G))
    (hderived : ∀ t : G, t ∈ (commutator (pCore 2 (centralizer ({z} : Set G)))).map
      ((centralizer ({z} : Set G)).subtype.comp
        (pCore 2 (centralizer ({z} : Set G))).subtype) → IsConj z t → t = z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    let Z := (center S).map S.subtype
    (Nat.card (E ⊓ Z : Subgroup G) = 4 ∨
      ((J.map H.subtype).relIndex S ≤ 2 ∧ (commutator S).map S.subtype ≤ E)) →
      Nat.card (center S) = 8 := by
  intro H J E S Z hlocal
  apply d.chosen_center_card_eight_iff_derived_intersection.mpr
  rcases hlocal with hfour | ⟨hindex, hle⟩
  · exact hfour
  · exact (d.chosen_commutator_not_le_derived_of_core_intersection_gt
      h hconj hderived (d.chosen_core_intersection_gt_of_relIndex_le_two h hindex) hle).elim

/-- The small core kernel and cyclic outer image give class at most two modulo E. -/
private theorem chosen_third_commutator_le_derived (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    (⁅(⊤ : Subgroup S), commutator S⁆).map S.subtype ≤ E := by
  classical
  intro H J E S
  let K := J.map H.subtype
  let U := E.subgroupOf S
  have hHE : H ≤ normalizer (E : Set G) := by
    have hh := ((commutator J).map J.subtype).le_normalizer_map H.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype,
      map_map] using hh
  let : U.Normal := normal_subgroupOf_of_le_normalizer (inf_le_left.trans hHE)
  obtain ⟨φ, _, ⟨e⟩⟩ := h.quotient_model
  let M := SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4)) φ
  let : Finite M := Finite.of_equiv
    (Multiplicative (ZMod 5) × Multiplicative (ZMod 4)) SemidirectProduct.equivProd.symm
  let f : S →* M := e.toMonoidHom.comp ((QuotientGroup.mk' J).comp (inclusion inf_le_left))
  have hfker : f.ker = K.subgroupOf S := by
    ext s
    change e (QuotientGroup.mk' J ⟨s, s.property.1⟩) = 1 ↔ (s : G) ∈ K
    rw [← e.map_one, e.injective.eq_iff]
    constructor
    · intro hs
      exact mem_map_of_mem H.subtype ((QuotientGroup.eq_one_iff (N := J) _).mp hs)
    · rintro ⟨j, hj, hjs⟩
      have heq : j = (⟨s, s.property.1⟩ : H) := Subtype.ext hjs
      exact (QuotientGroup.eq_one_iff (N := J) _).mpr (heq ▸ hj)
  have hUK : U ≤ f.ker := by
    rw [hfker]
    rintro s ⟨j, _, hjs⟩
    exact ⟨j.val, j.property, hjs⟩
  have hp : IsPGroup 2 S := d.chosen_centralizer_isPGroup h
  have hrangep : IsPGroup 2 f.range := by
    exact hp.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  let : IsCyclic f.range :=
    (SemidirectProduct.two_subgroup_isCyclic_card_dvd_four φ f.range hrangep).1
  have hUcard : Nat.card U = 16 := by
    have hc := card_map_of_injective (K := U) S.subtype_injective
    rw [subgroupOf_map_subtype] at hc
    exact hc.symm.trans d.chosen_derived_intersection.2
  have hfcard : Nat.card f.ker ≤ 64 := by
    rw [hfker]
    have hc := card_map_of_injective (K := K.subgroupOf S) S.subtype_injective
    rw [subgroupOf_map_subtype] at hc
    exact hc.symm.le.trans (d.chosen_core_intersection_card_le h)
  have hle := hp.third_commutator_le_of_cyclic_image U f hUK
    (by rw [hUcard]; exact hfcard)
  exact (map_mono hle).trans (by rw [subgroupOf_map_subtype]; exact inf_le_left)

/-- A two-element derived center forces its central involution into [S,S′]. -/
private theorem chosen_z_mem_third_commutator_of_small_center
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    let Z := (center S).map S.subtype
    Nat.card (E ⊓ Z : Subgroup G) = 2 →
      z ∈ (⁅(⊤ : Subgroup S), commutator S⁆).map S.subtype := by
  intro H J E S Z hsmall
  let U := E ⊓ d.F
  have hUS : U ≤ S := inf_le_right.trans d.le_chosen_centralizer
  have hHE : H ≤ normalizer (E : Set G) := by
    have hh := ((commutator J).map J.subtype).le_normalizer_map H.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype,
      map_map] using hh
  have hSU : S ≤ normalizer (U : Set G) :=
    (le_inf (inf_le_left.trans hHE)
      ((d.chosen_centralizer_le_sylow h).trans d.sylow_le_normalizer)).trans
        inf_normalizer_le_normalizer_inf
  let : IsElementaryAbelian 2 d.F := d.elementary
  let : IsElementaryAbelian 2 U := {
    toIsMulCommutative := ⟨⟨fun a b => Subtype.ext
      (setLike_mul_comm (s := d.F) a.property.2 b.property.2)⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun b =>
      Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2)
        (A := d.F) b b.property.2)) }
  have hUZ : U ⊓ Z = E ⊓ Z := by
    apply le_antisymm (inf_le_inf_right Z inf_le_left)
    exact le_inf (le_inf inf_le_left
      (inf_le_right.trans d.chosen_centralizer_center.2.2.1)) inf_le_right
  have hindex : (J.map H.subtype).relIndex S = 4 := by
    rcases d.chosen_core_relIndex_cases h with hi | hi
    · have hh := d.chosen_center_derived_card_ge_four_of_core_relIndex_two h hi
      change 4 ≤ Nat.card (E ⊓ Z : Subgroup G) at hh
      omega
    · exact hi
  obtain ⟨y, hyS, hyOrder⟩ := d.chosen_covering_quotient_generator h hindex
  have hfixed : Nat.card (U ⊓ centralizer ({(y : G)} : Set G) : Subgroup G) ≤ 2 := by
    have hle : U ⊓ centralizer ({(y : G)} : Set G) ≤ E ⊓ Z :=
      le_inf (inf_le_left.trans inf_le_left)
        ((inf_le_inf_right _ inf_le_left).trans (d.chosen_covering_fixed_le_center h y hyS hyOrder))
    exact (card_le_of_le hle).trans_eq hsmall
  apply Subgroup.mem_third_commutator_of_small_fixed S U
    (d.chosen_centralizer_isPGroup h) hUS hSU d.inf_card z h.involution
    ⟨d.z_mem_inf, d.chosen_centralizer_center.1⟩
    (by change Nat.card (U ⊓ Z : Subgroup G) = 2; rw [hUZ]; exact hsmall)
    (y : G) hyS hfixed

/-- The center of the supplied centralizer has order eight under derived weak
closure and the supplied conjugacy. Self-normalization of F is not needed. -/
public theorem chosen_center_card_eight
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z)
    (hconj : IsConj z (d.a : G))
    (hderived : ∀ t : G, t ∈ (commutator (pCore 2 (centralizer ({z} : Set G)))).map
      ((centralizer ({z} : Set G)).subtype.comp
        (pCore 2 (centralizer ({z} : Set G))).subtype) → IsConj z t → t = z) :
    let S := centralizer ({z} : Set G) ⊓ centralizer ({(d.a : G)} : Set G)
    Nat.card (center S) = 8 := by
  intro S
  rcases d.chosen_center_derived_card_cases h with htwo | hfour | height
  · exact (d.chosen_characteristic_not_le_derived h hconj hderived
      (⁅(⊤ : Subgroup S), commutator S⁆) inferInstance
      (d.chosen_z_mem_third_commutator_of_small_center h htwo)
      (d.chosen_third_commutator_le_derived h)).elim
  · exact d.chosen_center_card_eight_of_local_alternatives h hconj hderived (Or.inl hfour)
  · exact d.chosen_center_card_eight_of_local_alternatives h hconj hderived
      (Or.inr ⟨(d.chosen_core_relIndex_eq_two_of_center_derived_card_ge_eight
        h height.ge).le, d.chosen_large_center_commutator_le h height⟩)

end Stellmacher.Recognition.ParrottSecondElementaryData
