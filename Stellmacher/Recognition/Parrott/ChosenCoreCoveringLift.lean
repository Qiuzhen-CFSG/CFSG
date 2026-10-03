module

public import Stellmacher.Recognition.Parrott.ChosenCoreCenterLocalBounds
public import Stellmacher.Recognition.Parrott.SylowFiveLift

/-!
# Fourth powers of selected covering lifts

When the chosen centralizer S covers an order-four subgroup of H/J,
its cyclic quotient image supplies a generator. Replace a representative
by one in a Sylow-five normalizer, preserving its class modulo J. Its
fourth power then lies in Z(J), whose ambient image is ⟨z⟩, and therefore
centralizes E=J′. The replacement remains in the supplied Sylow-two
subgroup because it differs from the original representative by J.

The selected lift is not asserted to lie in S, nor to have order four.
The theorem controls its quotient class and its fourth power.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
p.674, the Sylow-five-normalizer lift, and p.676, the covering branch.
-/

open Subgroup

namespace Stellmacher.Recognition.ParrottSecondElementaryData

variable {G : Type*} [Group G] [Finite G] {z : G}

/-- The covering branch supplies an element of the actual centralizer
whose image has order four. No order assertion about the lift is made. -/
public theorem chosen_covering_quotient_generator
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    (J.map H.subtype).relIndex S = 4 →
      ∃ y : H, (y : G) ∈ S ∧ orderOf (QuotientGroup.mk' J y) = 4 := by
  intro H J S hi
  have hSH : S ≤ H := inf_le_left
  let L := S.subgroupOf H
  let q := QuotientGroup.mk' J
  obtain ⟨φ, _, ⟨e⟩⟩ := h.quotient_model
  let M := SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4)) φ
  let : Finite M := Finite.of_equiv
    (Multiplicative (ZMod 5) × Multiplicative (ZMod 4)) SemidirectProduct.equivProd.symm
  let f := e.toMonoidHom.comp q
  let A := L.map f
  have hp : IsPGroup 2 S := d.chosen_centralizer_isPGroup h
  have hLtwo : IsPGroup 2 L := hp.of_injective
    (subgroupOfEquivOfLe hSH).toMonoidHom (subgroupOfEquivOfLe hSH).injective
  let : IsCyclic A :=
    (SemidirectProduct.two_subgroup_isCyclic_card_dvd_four φ A (hLtwo.map f)).1
  have hrel : (J.map H.subtype).relIndex S = Nat.card A := by
    calc
      _ = (J.map H.subtype).relIndex (L.map H.subtype) := by
        rw [map_subgroupOf_eq_of_le hSH]
      _ = J.relIndex L := relIndex_map_map_of_injective J L H.subtype_injective
      _ = Nat.card (L.map q) := by
        have hh := relIndex_ker L q
        rw [QuotientGroup.ker_mk'] at hh
        exact hh
      _ = Nat.card A := by
        have hh := card_map_of_injective (K := L.map q) (f := e.toMonoidHom) e.injective
        rw [map_map] at hh
        exact hh.symm
  have hA : Nat.card A = 4 := hrel.symm.trans hi
  obtain ⟨a, ha⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp (inferInstance : IsCyclic A)
  rw [hA] at ha
  obtain ⟨y, hy, hya⟩ := a.property
  refine ⟨y, hy, ?_⟩
  have hf : orderOf (f y) = 4 := by
    rw [hya]
    exact (orderOf_injective A.subtype A.subtype_injective a).trans ha
  simpa only [f, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e.orderOf_eq] using hf

/-- In the covering branch one can choose a lift in the supplied Sylow
whose quotient order is four and whose fourth power belongs to ⟨z⟩. -/
public theorem chosen_covering_exists_lift_fourth_power_mem_zpowers
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    (J.map H.subtype).relIndex S = 4 →
      ∃ y : H, (y : G) ∈ (d.sylow : Subgroup G) ∧
        orderOf (QuotientGroup.mk' J y) = 4 ∧ (y : G) ^ 4 ∈ zpowers z := by
  intro H J S hi
  let q := QuotientGroup.mk' J
  obtain ⟨x, hxS, hx4⟩ := chosen_covering_quotient_generator d h hi
  obtain ⟨y, hyx, hy4⟩ := parrott_quotient_exists_lift_pow_mem_core_center z h
    (q x) 4 (hx4 ▸ pow_orderOf_eq_one (q x))
  have hyJ : y * x⁻¹ ∈ J := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q (y * x⁻¹) = 1
    rw [map_mul, map_inv, hyx, mul_inv_cancel]
  have hJT : J.map H.subtype ≤ (d.sylow : Subgroup G) := by
    rw [d.sylow_map]
    exact map_mono (pCore_isPGroup.le_sylow_of_normal d.localSylow)
  have hyT : (y : G) ∈ (d.sylow : Subgroup G) := by
    have hdiff := hJT (mem_map_of_mem H.subtype hyJ)
    have hxT := d.chosen_centralizer_le_sylow h hxS
    have hh := d.sylow.mul_mem hdiff hxT
    change (y : G) * (x : G)⁻¹ * (x : G) ∈ (d.sylow : Subgroup G) at hh
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh
  refine ⟨y, hyT, hyx.symm ▸ hx4, ?_⟩
  have hZ := (parrott_centralizer_structure z h).1
  rw [← hZ, ← map_map]
  exact mem_map_of_mem H.subtype hy4

/-- A selected covering lift has quotient order four and fourth power
centralizing the derived core. No assertion about the lift's order is needed. -/
public theorem chosen_covering_exists_lift_fourth_power_centralizing_derived
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    (J.map H.subtype).relIndex S = 4 →
      ∃ y : H, (y : G) ∈ (d.sylow : Subgroup G) ∧
        orderOf (QuotientGroup.mk' J y) = 4 ∧
        (y : G) ^ 4 ∈ centralizer (E : Set G) := by
  intro H J E S hi
  obtain ⟨y, hyT, hy4, hyZ⟩ :=
    d.chosen_covering_exists_lift_fourth_power_mem_zpowers h hi
  refine ⟨y, hyT, hy4, ?_⟩
  have hzC : z ∈ centralizer (E : Set G) := by
    rintro e ⟨j, _, rfl⟩
    exact mem_centralizer_singleton_iff.mp j.val.property
  exact (zpowers_le.mpr hzC) hyZ

end Stellmacher.Recognition.ParrottSecondElementaryData
