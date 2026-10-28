module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.OrbitPersistence.Reduction
public import Theory.GroupTheory.PGroup.NormalSubgroups

/-!
# Involution fusion and persistence

A nontrivial normal subgroup of a finite two-group meets its center. Apply
this to T intersect L^u inside N_T(L^u) = N_T(L). A single involution class
in L^u then moves every involution of the container to a central representative
in this index-two subgroup. Conjugation by L^u fixes both z and L.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, p.1174,
Lemma 16.2.6(1). The intrinsic fusion and even-order premises remain to be
proved for the listed models. This conditional reduction is not that lemma's
source-theorem assembly.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry
universe v
variable {G : Type v} [Group G] [Finite G]
variable {T : Sylow 2 G} {z : G} {L : Subgroup G} {u : G}

private theorem exists_central_involution (h : CentralComponentSetup T z L)
    (heven : 2 ∣ Nat.card L) :
    ∃ a : G, a ∈ (T : Subgroup G) ⊓ L ∧ orderOf a = 2 ∧
      a ∈ centralizer (((T : Subgroup G) ⊓ normalizer (L : Set G)) : Set G) := by
  let N : Subgroup G := (T : Subgroup G) ⊓ normalizer (L : Set G)
  let D := L.subgroupOf N
  let : D.Normal := normal_subgroupOf_of_le_normalizer inf_le_right
  obtain ⟨S, hS⟩ := h.exists_component_sylow
  have hD : D ≠ ⊥ := by
    intro he
    apply S.ne_bot_of_dvd_card heven
    rw [hS]
    apply eq_bot_iff.mpr
    intro x hx
    have hxN : (x : G) ∈ N := ⟨hx, L.le_normalizer x.property⟩
    have hxD : (⟨x, hxN⟩ : N) ∈ D := x.property
    rw [he, mem_bot] at hxD
    exact Subtype.ext (congrArg (fun y : N => (y : G)) hxD)
  let : Nontrivial D := (nontrivial_iff_ne_bot D).mpr hD
  have hN : IsPGroup 2 N := T.isPGroup'.of_injective
    (inclusion (show N ≤ (T : Subgroup G) from inf_le_left)) (inclusion_injective _)
  let : Fact (IsPGroup 2 N) := ⟨hN⟩
  obtain ⟨A, _, hAD, hAcard, hAc⟩ :=
    exists_central_subgroup_card_eq_prime_in_normal (p := 2) D inferInstance
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := A) 2 (by rw [hAcard])
  refine ⟨a, ⟨a.val.property.1, hAD a.property⟩, ?_, ?_⟩
  · simpa only [orderOf_coe] using ha
  · apply mem_centralizer_iff.mpr
    intro x hx
    exact congrArg Subtype.val (mem_center_iff.mp (hAc a.property) ⟨x, hx⟩)

omit [Finite G] in
private theorem map_centralizer_singleton (e : G ≃* G) (t : G) :
    (involutionCentralizer t).map e.toMonoidHom = involutionCentralizer (e t) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    change e y * e t = e t * e y
    simpa only [map_mul] using congrArg e (mem_centralizer_singleton_iff.mp hy)
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    apply mem_centralizer_singleton_iff.mpr
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using mem_centralizer_singleton_iff.mp hx

omit [Finite G] in
private theorem component_map (e : G ≃* G) {t : G} (hL : IsCentralizerComponent t L) :
    IsCentralizerComponent (e t) (L.map e.toMonoidHom) := by
  have hm := (show IsComponentIn L (involutionCentralizer t) from hL).map e
  rwa [map_centralizer_singleton] at hm

namespace TwoComponentOrbit
variable (o : TwoComponentOrbit T z L u) (h : CentralComponentSetup T z L)
include o h

omit [Finite G] in
theorem container_le_centralizer : involutionContainer z L u ≤ centralizer (L : Set G) := by
  apply sup_le
  · apply zpowers_le.mpr
    apply mem_centralizer_iff.mpr
    intro x hx
    exact mem_centralizer_singleton_iff.mp (h.component.1 hx)
  · exact commutator_eq_bot_iff_le_centralizer.mp (by
      rw [commutator_comm]; exact o.commute h)

omit [Finite G] in
theorem container_le_centralizer_z : involutionContainer z L u ≤ involutionCentralizer z :=
  sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)) (o.swapped_component h).1

/-- A central representative in the index-two normalizer suffices for transfer. -/
theorem component_of_central_representative (transfer : SmallCentralizerIndexTransfer G)
    {t : G} (ht : t ∈ involutionContainer z L u) (ht2 : orderOf t = 2)
    (htT : t ∈ T)
    (htN : t ∈ centralizer (((T : Subgroup G) ⊓ normalizer (L : Set G)) : Set G)) :
    IsCentralizerComponent t L := by
  apply h.component_of_small_index_of_transfer transfer ht2
    ⟨htT, o.container_le_centralizer h ht⟩
  have hn : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ involutionCentralizer t := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp htN x hx)
  have hi := relIndex_le_of_le_left hn (show
    ((T : Subgroup G) ⊓ normalizer (L : Set G)).relIndex (T : Subgroup G) ≠ 0 from
    Subgroup.index_ne_zero_of_finite)
  rw [inf_relIndex_left, o.normalizer_index h] at hi
  exact hi

omit [Finite G] in
/-- Conjugating by the swapped factor fixes both z and L. -/
theorem swapped_conj_fixes {g : G} (hg : g ∈ conjugate L u) :
    (MulAut.conj g) z = z ∧ L.map (MulAut.conj g).toMonoidHom = L := by
  constructor
  · have hc := mem_centralizer_singleton_iff.mp ((o.swapped_component h).1 hg)
    change g * z * g⁻¹ = z
    rw [hc, mul_inv_cancel_right]
  · exact mem_normalizer_iff_map_conj_eq.mp
      (centralizer_le_normalizer _ (o.container_le_centralizer h
        ((le_sup_right : conjugate L u ≤ involutionContainer z L u) hg)))

/-- Every involution in the container can be moved to the index-two
normalizer's centralizer, using fusion in the swapped factor. -/
theorem componentPersistence_of_involution_fusion
    (transfer : SmallCentralizerIndexTransfer G)
    (heven : 2 ∣ Nat.card L)
    (fusion : ∀ a b : L, orderOf a = 2 → orderOf b = 2 → IsConj a b) :
    ComponentPersistence z L u := by
  let U := conjugate L u
  let eU : L ≃* U := (MulAut.conj u⁻¹).subgroupMap L
  have hU : CentralComponentSetup T z U :=
    ⟨h.involution, h.mem_sylow, h.sylow_centralizes, o.swapped_component h⟩
  obtain ⟨a, ha, ha2, haN⟩ := exists_central_involution hU
    (by rwa [← Nat.card_congr eU.toEquiv])
  have haN' : a ∈ centralizer
      (((T : Subgroup G) ⊓ normalizer (L : Set G)) : Set G) := by
    apply mem_centralizer_iff.mpr
    intro x hx
    exact mem_centralizer_iff.mp haN x ((o.normalizer_inter_eq h).ge hx)
  have hzN : z ∈ centralizer
      (((T : Subgroup G) ⊓ normalizer (L : Set G)) : Set G) := by
    apply mem_centralizer_iff.mpr
    intro x hx
    exact mem_centralizer_singleton_iff.mp (h.sylow_centralizes hx.1)
  have hzU : zpowers z ≤ normalizer (U : Set G) := by
    apply zpowers_le.mpr
    apply centralizer_le_normalizer
    apply mem_centralizer_iff.mpr
    intro x hx
    exact mem_centralizer_singleton_iff.mp (hU.component.1 hx)
  intro t ht ht2
  have ht' : t ∈ (↑(zpowers z ⊔ U) : Set G) := ht
  rw [coe_mul_of_left_le_normalizer_right _ _ hzU] at ht'
  obtain ⟨w, hw, b, hb, rfl⟩ := ht'
  have hwT : w ∈ T := (zpowers_le.mpr h.mem_sylow) hw
  have hwN := (zpowers_le.mpr hzN) hw
  have hw2 : w ^ 2 = 1 := by
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [← h.involution]
    exact orderOf_dvd_of_mem_zpowers hw
  have hwb : Commute w b := by
    have hzw : zpowers z ≤ involutionCentralizer b := by
      apply zpowers_le.mpr
      exact mem_centralizer_singleton_iff.mpr
        (mem_centralizer_singleton_iff.mp (hU.component.1 hb)).symm
    exact mem_centralizer_singleton_iff.mp (hzw hw)
  have hb2 : b ^ 2 = 1 := by
    have hp : (w * b) ^ 2 = 1 := by rw [← ht2]; exact pow_orderOf_eq_one _
    rwa [hwb.mul_pow, hw2, one_mul] at hp
  by_cases hb1 : b = 1
  · subst b
    apply o.component_of_central_representative h transfer ht ht2
    · simpa using hwT
    · simpa using hwN
  · have hbOrder : orderOf (⟨b, hb⟩ : U) = 2 := by
      rw [← orderOf_coe]
      exact orderOf_eq_prime hb2 hb1
    have haOrder : orderOf (⟨a, ha.2⟩ : U) = 2 := by simpa using ha2
    have hc := eU.toMonoidHom.map_isConj (fusion (eU.symm ⟨b, hb⟩)
      (eU.symm ⟨a, ha.2⟩) (by simpa using hbOrder) (by simpa using haOrder))
    have hc' : IsConj (⟨b, hb⟩ : U) ⟨a, ha.2⟩ := by simpa using hc
    obtain ⟨g, hg⟩ := isConj_iff.mp hc'
    let e : G ≃* G := MulAut.conj (g : G)
    have hef := o.swapped_conj_fixes h g.property
    have hew : e w = w := by
      obtain ⟨k, rfl⟩ := hw
      simp only [map_zpow, e, hef.1]
    have heb : e b = a := congrArg Subtype.val hg
    have het : e (w * b) = w * a := by rw [map_mul, hew, heb]
    have horder : orderOf (w * a) = 2 := by rw [← het, e.orderOf_eq, ht2]
    have hmem : w * a ∈ involutionContainer z L u :=
      mul_mem_sup hw ha.2
    have hcomp := o.component_of_central_representative h transfer hmem horder
      ((T : Subgroup G).mul_mem hwT ha.1) ((centralizer _).mul_mem hwN haN')
    have hback := component_map e.symm hcomp
    have heL : L.map e.symm.toMonoidHom = L := by
      have hf : L.map e.toMonoidHom = L := hef.2
      have hm := congrArg (Subgroup.map e.symm.toMonoidHom) hf
      have hid : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by
        ext x
        exact e.symm_apply_apply x
      rw [Subgroup.map_map, hid, Subgroup.map_id] at hm
      exact hm.symm
    rw [heL, ← het, e.symm_apply_apply] at hback
    exact hback

omit o h in
/-- Even order in L supplies the actual involution required by 16.2.7. -/
theorem exists_swapped_involution (heven : 2 ∣ Nat.card L) :
    ∃ t : G, t ∈ conjugate L u ∧ orderOf t = 2 := by
  let e : L ≃* conjugate L u := (MulAut.conj u⁻¹).subgroupMap L
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := L) 2 heven
  exact ⟨e t, (e t).property, by simpa only [orderOf_coe, e.orderOf_eq] using ht⟩

end TwoComponentOrbit
namespace CounterexampleSetup
variable {K : GroupClass.{v}} (c : CounterexampleSetup K T z L)
include c

/-- (E1) forces every nontrivial component to have even order. -/
theorem component_even : 2 ∣ Nat.card L := by
  have hcore := Subgroup.IsSubnormal.pPrimeCore_eq_bot
    (c.global.evenType.oddCore z c.localSetup.involution)
    (L.subgroupOf (involutionCentralizer z)) c.localSetup.component.2.1
  have hm := pPrimeCore_map_iso 2 (subgroupOfEquivOfLe c.localSetup.component.1)
  have hLcore : pPrimeCore 2 L = ⊥ := by
    simpa only [hcore, Subgroup.map_bot] using hm.symm
  let : Nontrivial L := (nontrivial_iff_ne_bot L).mpr
    (show IsComponentIn L (involutionCentralizer z) from c.localSetup.component).ne_bot
  by_contra hodd
  have hc := Nat.prime_two.coprime_iff_not_dvd.mpr hodd
  have htop : (⊤ : Subgroup L) = ⊥ := pPrimeCore_eq_bot_iff.mp hLcore ⊤
    inferInstance (by simpa only [Nat.card_congr Subgroup.topEquiv.toEquiv] using hc)
  exact top_ne_bot htop

/-- The second factor has an involution, without any model order input. -/
theorem exists_swapped_involution : ∃ t : G, t ∈ conjugate L u ∧ orderOf t = 2 :=
  TwoComponentOrbit.exists_swapped_involution c.component_even

/-- The simple-case reduction now needs only its intrinsic involution fusion. -/
theorem componentPersistence_of_involution_fusion
    (o : TwoComponentOrbit T z L u) (transfer : SmallCentralizerIndexTransfer G)
    (fusion : ∀ a b : L, orderOf a = 2 → orderOf b = 2 → IsConj a b) :
    ComponentPersistence z L u :=
  o.componentPersistence_of_involution_fusion c.localSetup transfer c.component_even fusion

/-- A.1.34(2) constructs all orbit witnesses needed by the conditional 16.2.7. -/
theorem exists_orbit_with_involution (a134 : ComponentPairExhaustion K G) :
    ∃ u : G, TwoComponentOrbit T z L u ∧
      (normalizer (L : Set G)).relIndex (T : Subgroup G) = 2 ∧
      ∃ t : G, t ∈ conjugate L u ∧ orderOf t = 2 := by
  obtain ⟨u, ho⟩ := c.exists_twoComponentOrbit a134
  exact ⟨u, ho, ho.normalizer_index c.localSetup, c.exists_swapped_involution⟩

end CounterexampleSetup
end CFSG.Quasithin.Chapter16.CounterexampleGeometry

end
