module

public import Theory.GroupTheory.PGroup.CriticalNonelementaryCenter
public import Theory.GroupTheory.PGroup.NonelementaryClassTwoQuaternion
public import Theory.GroupTheory.SylowPGroupAutomizer
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.SpecificGroups.QuaternionEightInvolution
public import Stellmacher.Recognition.NormalEightCriticalQuaternionSupplement

/-!
# Quaternion factors from nonelementary critical centers

A nonelementary center in a nonabelian critical subgroup singles out an
involution fixed by the full Sylow normalizer. More specifically, if the
critical derived subgroup has order two, every quaternion subgroup inside
the critical subgroup has that fixed involution. Thus a quaternion subgroup
with a centralizer supplement supplies precisely the factor and fixed-point
data used in the square-fusion contradiction.

The final theorem assembles the structural extraction: the intrinsic
three-involution theorem constructs an internal quaternion supplement and
proves derived order two; the cubic-action argument extends a quaternion
subgroup to a centralizer supplement in the full Sylow subgroup. The derived
involution then gives the required fixed point. Source: MacWilliams,
Trans. AMS 150 (1970), §3(iii)–(iv), pp.367–369.
-/

open Subgroup
open scoped commutatorElement

private theorem fixed_of_characteristic_two
    {G : Type*} [Group G] [Finite G] (H : Subgroup G)
    (K : Subgroup H) [K.Characteristic] (hK : Nat.card K = 2)
    (z : H) (hz : orderOf z = 2) (hzK : z ∈ K) :
    normalizer (H : Set G) ≤ centralizer ({(z : G)} : Set G) := by
  have he : zpowers z = K := eq_of_le_of_card_ge (zpowers_le.mpr hzK)
    (by rw [Nat.card_zpowers, hz, hK])
  apply normalizer_le_centralizer_of_characteristic_involution H K z
    ((orderOf_coe z).trans hz)
  rw [← he, MonoidHom.map_zpowers]
  rfl

namespace Sylow

/-- A nonelementary critical center yields a normalizer-fixed critical involution. -/
public theorem exists_fixed_critical_involution_of_nonelementary_center
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 4)
    {C : Subgroup S} (hC : IsCriticalPSubgroup 2 C)
    (hnonab : ¬ IsMulCommutative C)
    (hbad : ¬ IsElementaryAbelian 2 (center C)) :
    ∃ z : C, orderOf z = 2 ∧
      normalizer (S : Set G) ≤ centralizer ({((z : S) : G)} : Set G) := by
  let : C.Characteristic := hC.characteristic
  obtain ⟨K, hKchar, hK⟩ := hC.exists_characteristic_two_of_nonelementary_center
    S.isPGroup' hno hZ hnonab hbad
  let : K.Characteristic := hKchar
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := K) 2 (by rw [hK])
  let D := K.map C.subtype
  let : D.Characteristic := inferInstance
  have hD : Nat.card D = 2 := (card_map_of_injective C.subtype_injective).trans hK
  have hzC : orderOf (z : C) = 2 := (orderOf_coe z).trans hz
  refine ⟨z, hzC, fixed_of_characteristic_two (S : Subgroup G) D hD
    ((z : C) : S) ((orderOf_coe (z : C)).trans hzC) ?_⟩
  exact mem_map_of_mem C.subtype z.property

/-- A quaternion subgroup of a critical subgroup with derived order two has
normalizer-fixed involution. The centralizer supplement remains an explicit premise. -/
public theorem quaternion_factor_of_critical_derived_two
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    {C : Subgroup S} (hC : IsCriticalPSubgroup 2 C)
    (hD : Nat.card (commutator C) = 2)
    (Q : Subgroup S) (hQC : Q ≤ C) (e : Q ≃* QuaternionGroup 2)
    (hgen : Q ⊔ centralizer (Q : Set S) = ⊤) :
    ∃ Q : Subgroup S, Nonempty (Q ≃* QuaternionGroup 2) ∧
      Q ⊔ centralizer (Q : Set S) = ⊤ ∧
      ∃ z : Q, orderOf z = 2 ∧
        normalizer (S : Set G) ≤ centralizer ({((z : S) : G)} : Set G) := by
  let : C.Characteristic := hC.characteristic
  let z := e.symm (QuaternionGroup.a 2)
  have hz : orderOf z = 2 := (e.symm.orderOf_eq _).trans (by
    rw [QuaternionGroup.orderOf_a]
    decide)
  let f : Q →* C := inclusion hQC
  have hzD : f z ∈ commutator C := by
    have he : z = ⁅e.symm (QuaternionGroup.a 1), e.symm (QuaternionGroup.xa 0)⁆ := by
      apply e.injective
      simp only [z, map_commutatorElement, e.apply_symm_apply]
      decide
    rw [he, map_commutatorElement]
    exact commutator_mem_commutator (mem_top _) (mem_top _)
  let D := (commutator C).map C.subtype
  let : D.Characteristic := inferInstance
  have hcard : Nat.card D = 2 := (card_map_of_injective C.subtype_injective).trans hD
  refine ⟨Q, ⟨e⟩, hgen, z, hz,
    fixed_of_characteristic_two (S : Subgroup G) D hcard z
      ((orderOf_coe z).trans hz) ?_⟩
  exact mem_map_of_mem C.subtype hzD

/-- A nonelementary nonabelian critical center yields a quaternion factor
whose involution is fixed by the full Sylow normalizer. -/
public theorem quaternion_factor_of_nonelementary_critical_center
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 4)
    (hnorm : normalizer (S : Set G) ≠ (S : Subgroup G) ⊔ centralizer (S : Set G))
    {C : Subgroup S} (hC : IsCriticalPSubgroup 2 C)
    (hCnonab : ¬ IsMulCommutative C)
    (hbad : ¬ IsElementaryAbelian 2 (center C)) :
    ∃ Q : Subgroup S, Nonempty (Q ≃* QuaternionGroup 2) ∧
      Q ⊔ centralizer (Q : Set S) = ⊤ ∧
      ∃ z : Q, orderOf z = 2 ∧
        normalizer (S : Set G) ≤ centralizer ({((z : S) : G)} : Set G) := by
  have hAut := hC.not_isPGroup_mulAut_of_ambient S.isPGroup'
    (S.not_isPGroup_mulAut_of_normalizer_ne_sup_centralizer hnorm)
  obtain ⟨hD, R, ⟨eR⟩, hRgen⟩ :=
    (S.isPGroup'.to_subgroup C).quaternion_supplement_of_nonelementary_center
      hCnonab hC.quotient_elementary (hC.square_one_mem_center hno hZ)
      (hC.card_involutions_eq_three hno hZ) hbad hAut
  obtain ⟨Q, hQC, ⟨eQ⟩, hQgen⟩ :=
    S.quaternion_supplement_of_internal hno hZ hnorm hC hCnonab hbad R eR hRgen
  exact S.quaternion_factor_of_critical_derived_two hC hD Q hQC eQ hQgen

end Sylow
