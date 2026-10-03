module

public import Stellmacher.Recognition.Parrott.SecondElementary
public import Stellmacher.Recognition.Parrott.DerivedLocalCenters
public import Theory.GroupTheory.C5C4ElementaryTwoSubgroup

/-!
# The core quotient of the first derived-involution centralizer

Write K for the ambient image of J=O₂(C_G(z)) and E for that of J′.
The centralizer C=C_T(t) contains E, meets K in C_K(t), and has index
four over that intersection when |C|=1024. Its derived subgroup lies in
K, since every two-subgroup of C_G(z)/J is cyclic. These facts prepare
the displacement and involution computations for Ω₁(C′).

Source: Parrott, *A characterization of the Tits' simple group* (1972),
pp.673–674 and the last two paragraphs of p.676.
-/

open Subgroup
open scoped IsMulCommutative

namespace Stellmacher.Recognition.ParrottSecondElementaryData

variable {G : Type*} [Group G] [Finite G] {z : G}

omit [Finite G] in
/-- The ambient core is contained in the supplied Sylow subgroup. -/
public theorem core_le_sylow (d : ParrottSecondElementaryData z) :
    (pCore 2 (centralizer ({z} : Set G))).map
      (centralizer ({z} : Set G)).subtype ≤ (d.sylow : Subgroup G) := by
  rw [d.sylow_map]
  exact map_mono (pCore_isPGroup.le_sylow_of_normal d.localSylow)

/-- The first local centralizer contains the whole derived core. -/
public theorem derived_le_t_centralizer (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    ∀ t ∈ E, E ≤ (d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G) := by
  intro H J E t ht
  let : IsElementaryAbelian 2 (commutator J) :=
    (parrott_centralizer_structure z h).2.2.2.2.2.1
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map (H.subtype.comp J.subtype)
  have hEK : E ≤ J.map H.subtype := by
    rw [show E = ((commutator J).map J.subtype).map H.subtype from
      (map_map _ _ _).symm]
    exact map_mono (map_subtype_le _)
  intro e he
  exact ⟨d.core_le_sylow (hEK he),
    mem_centralizer_singleton_iff.mpr (setLike_mul_comm he ht)⟩

/-- The core intersection has order 256, so a centralizer of order 1024
covers the full quotient of order four. -/
public theorem t_centralizer_core_relIndex (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    ∀ t ∈ E, t ∉ zpowers z →
      let C := (d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G)
      Nat.card C = 1024 → (J.map H.subtype).relIndex C = 4 := by
  intro H J E t ht htz C hC
  let K := J.map H.subtype
  have hmeet : K ⊓ C = K ⊓ centralizer ({t} : Set G) := by
    rw [show C = (d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G) from rfl,
      ← inf_assoc, inf_eq_left.mpr d.core_le_sylow]
  have hc : Nat.card (K ⊓ C : Subgroup G) = 256 := by
    rw [hmeet]
    exact parrott_derived_core_centralizer_card z h t ht htz
  have hh := (K.subgroupOf C).index_mul_card
  have hsub : Nat.card (K.subgroupOf C) = 256 := by
    rw [← card_map_of_injective (K := K.subgroupOf C) C.subtype_injective,
      subgroupOf_map_subtype, hc]
  change K.relIndex C * Nat.card (K.subgroupOf C) = Nat.card C at hh
  rw [hsub, hC] at hh
  change K.relIndex C = 4
  omega

/-- A centralizer of order 1024 contains an actor of order four modulo
the core. This is the actor used in the derived displacement calculation. -/
public theorem t_centralizer_exists_quotient_order_four
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    ∀ t ∈ E, t ∉ zpowers z →
      let C := (d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G)
      Nat.card C = 1024 →
      ∃ y : H, (y : G) ∈ C ∧ orderOf (QuotientGroup.mk' J y) = 4 := by
  intro H J E t ht htz C hC
  have hCH : C ≤ H := inf_le_left.trans (by rw [d.sylow_map]; exact map_subtype_le _)
  let L := C.subgroupOf H
  let q := QuotientGroup.mk' J
  obtain ⟨φ, _, ⟨e⟩⟩ := h.quotient_model
  let M := SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4)) φ
  let : Finite M := Finite.of_equiv
    (Multiplicative (ZMod 5) × Multiplicative (ZMod 4)) SemidirectProduct.equivProd.symm
  let f := e.toMonoidHom.comp q
  let A := L.map f
  have hp : IsPGroup 2 C := d.sylow.isPGroup'.to_le inf_le_left
  have hLtwo : IsPGroup 2 L := hp.of_injective
    (subgroupOfEquivOfLe hCH).toMonoidHom (subgroupOfEquivOfLe hCH).injective
  let : IsCyclic A :=
    (SemidirectProduct.two_subgroup_isCyclic_card_dvd_four φ A (hLtwo.map f)).1
  have hrel : (J.map H.subtype).relIndex C = Nat.card A := by
    calc
      _ = (J.map H.subtype).relIndex (L.map H.subtype) := by
        rw [map_subgroupOf_eq_of_le hCH]
      _ = J.relIndex L := relIndex_map_map_of_injective J L H.subtype_injective
      _ = Nat.card (L.map q) := by
        have hh := relIndex_ker L q
        rw [QuotientGroup.ker_mk'] at hh
        exact hh
      _ = Nat.card A := by
        have hh := card_map_of_injective (K := L.map q) (f := e.toMonoidHom) e.injective
        rw [map_map] at hh
        exact hh.symm
  have hA : Nat.card A = 4 := hrel.symm.trans (d.t_centralizer_core_relIndex h t ht htz hC)
  obtain ⟨a, ha⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp (inferInstance : IsCyclic A)
  rw [hA] at ha
  obtain ⟨y, hy, hya⟩ := a.property
  refine ⟨y, hy, ?_⟩
  have hf : orderOf (f y) = 4 := by
    rw [hya]
    exact (orderOf_injective A.subtype A.subtype_injective a).trans ha
  simpa only [f, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e.orderOf_eq] using hf

omit [Finite G] in
/-- The derived subgroup of any subgroup of the supplied Sylow lies in
the original two-core, because its image in H/J is cyclic. -/
public theorem sylow_subgroup_commutator_le_core (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (C : Subgroup G)
    (hCT : C ≤ (d.sylow : Subgroup G)) :
    (commutator C).map C.subtype ≤
      (pCore 2 (centralizer ({z} : Set G))).map
        (centralizer ({z} : Set G)).subtype := by
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  have hCH : C ≤ H := hCT.trans (by rw [d.sylow_map]; exact map_subtype_le _)
  let i : C →* H := inclusion hCH
  obtain ⟨φ, _, ⟨e⟩⟩ := h.quotient_model
  let f := e.toMonoidHom.comp ((QuotientGroup.mk' J).comp i)
  have hp : IsPGroup 2 C := d.sylow.isPGroup'.to_le hCT
  have hr : IsPGroup 2 f.range := hp.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  let : IsCyclic f.range :=
    (SemidirectProduct.two_subgroup_isCyclic_card_dvd_four φ f.range hr).1
  have hker : commutator C ≤ f.rangeRestrict.ker :=
    Abelianization.commutator_subset_ker f.rangeRestrict
  rintro c ⟨b, hb, rfl⟩
  have hf : f b = 1 := congrArg (fun x : f.range => x.val) (hker hb)
  have hq : QuotientGroup.mk' J (i b) = 1 :=
    e.injective (hf.trans (map_one e).symm)
  exact mem_map_of_mem H.subtype ((QuotientGroup.eq_one_iff (N := J) (i b)).mp hq)

/-- The central involution already lies in C′: the core intersection is
too large to centralize E, and its commutators with E lie in ⟨z⟩. -/
public theorem involution_line_le_t_centralizer_commutator
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    ∀ t ∈ E, t ∉ zpowers z →
      let C := (d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G)
      zpowers z ≤ (commutator C).map C.subtype := by
  intro H J E t ht htz C
  let K := J.map H.subtype
  let D := K ⊓ centralizer ({t} : Set G)
  let embed := H.subtype.comp J.subtype
  obtain ⟨hZ, _, _, _, hUpper, _, hEcard, _⟩ := parrott_centralizer_structure z h
  have hKE : ⁅K, E⁆ ≤ zpowers z := by
    have hbound : ⁅(⊤ : Subgroup J), commutator J⁆ ≤ center J := by
      rw [commutator_comm, hUpper]
      simpa only [Subgroup.upperCentralSeries_one] using
        commutator_upperCentralSeries_top_le J 1
    have hh := map_mono (f := embed) hbound
    rw [map_commutator, hZ] at hh
    have htop : (⊤ : Subgroup J).map embed = K := by
      rw [← map_map, ← MonoidHom.range_eq_map, range_subtype]
    rw [htop] at hh
    exact hh
  have hbound : ⁅D, E⁆ ≤ zpowers z := (commutator_mono inf_le_left le_rfl).trans hKE
  have hne : ⁅D, E⁆ ≠ ⊥ := by
    intro hbot
    have hDE : D ≤ E := by
      rw [← show centralizer (E : Set G) = E from parrott_derived_centralizer z h]
      exact commutator_eq_bot_iff_le_centralizer.mp hbot
    have hc := card_le_of_le hDE
    have hDc : Nat.card D = 256 := parrott_derived_core_centralizer_card z h t ht htz
    have hEc : Nat.card E = 32 :=
      (card_map_of_injective (K := commutator J) (f := embed)
        (H.subtype_injective.comp J.subtype_injective)).trans hEcard
    rw [hDc, hEc] at hc
    omega
  have heq : ⁅D, E⁆ = zpowers z := by
    apply eq_of_le_of_card_ge hbound
    rw [Nat.card_zpowers, h.involution]
    exact Nat.succ_le_of_lt ((one_lt_card_iff_ne_bot _).mpr hne)
  rw [map_subtype_commutator, ← heq]
  exact commutator_mono (inf_le_inf_right _ d.core_le_sylow)
    (d.derived_le_t_centralizer h t ht)

end Stellmacher.Recognition.ParrottSecondElementaryData
