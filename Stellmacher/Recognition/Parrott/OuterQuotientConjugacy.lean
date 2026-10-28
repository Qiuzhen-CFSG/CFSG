module

public import Stellmacher.Recognition.Parrott.CoreQuotientAction
public import Theory.GroupAction.FiveFourInvolutionFixed

/-!
# Conjugacy modulo the derived core

For an outer involution y in H=C_G(z), every y-fixed vector of J/J′ is a
single y-displacement: the faithful five-four action has equal fixed and
displacement spaces. Lifting a displacement representative to J shows that
y and ya are J-conjugate modulo J′ whenever a belongs to J and commutes
with y. This supplies the quotient conjugacy used in the outer suborbit count.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
pp.674 and 676.
-/

open Subgroup

namespace Stellmacher.Recognition

/-- A core element commuting with an outer involution gives a conjugate
of that involution modulo the derived core. -/
public theorem parrott_outer_quotient_conjugacy
    {G : Type*} [Group G] [Finite G]
    (z : G) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let DH := (commutator J).map J.subtype
    ∀ y : H, orderOf y = 2 → y ∉ J →
      ∀ a : H, a ∈ J → Commute a y →
        ∃ t : J, (y * a)⁻¹ * ((t : H) * y * (t : H)⁻¹) ∈ DH := by
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let D := commutator J
  let DH := D.map J.subtype
  let V := J ⧸ D
  let qJ := QuotientGroup.mk' J
  let qD := QuotientGroup.mk' D
  change ∀ y : H, orderOf y = 2 → y ∉ J → _
  intro y hy hyJ a ha hay
  obtain ⟨f, hf, heval⟩ := parrott_core_quotient_action z h
  obtain ⟨hElem, hVcard⟩ := parrott_core_abelianization_structure z h
  let : IsElementaryAbelian 2 V := hElem
  obtain ⟨φ, hφ, ⟨e⟩⟩ := h.quotient_model
  let M := SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4)) φ
  let fM : M →* MulAut V := f.comp e.symm.toMonoidHom
  have hfM : Function.Injective fM := hf.comp e.symm.injective
  let u : M := e (qJ y)
  have hu : orderOf u = 2 := by
    rw [e.orderOf_eq]
    apply orderOf_eq_prime
    · rw [← map_pow, show y ^ 2 = 1 from hy ▸ pow_orderOf_eq_one y, map_one]
    · exact fun hh => hyJ ((QuotientGroup.eq_one_iff y).mp hh)
  have hevalM (b b' : J) (hb : (b' : H) = y * (b : H) * y⁻¹) :
      fM u (qD b) = qD b' := by
    simpa only [fM, u, qJ, qD, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      e.symm_apply_apply] using heval y b b' hb
  let aJ : J := ⟨a, ha⟩
  have hfixed : fM u (qD aJ) = qD aJ :=
    hevalM aJ aJ (mul_inv_eq_iff_eq_mul.mpr hay.symm.eq).symm
  obtain ⟨w, hw⟩ := Theory.GroupAction.five_four_involution_exists_displacement
    hVcard φ hφ fM hfM u hu (qD aJ) hfixed
  obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective D w
  let t' : J := ⟨y * (t : H) * y⁻¹,
    (inferInstance : J.Normal).conj_mem t t.property y⟩
  have ht' := hevalM t t' rfl
  have hmem : aJ⁻¹ * (t' * t⁻¹) ∈ D := by
    apply (QuotientGroup.eq_one_iff _).mp
    change qD (aJ⁻¹ * (t' * t⁻¹)) = 1
    rw [map_mul, map_inv, map_mul, map_inv, ← ht', hw, inv_mul_cancel]
  have hh := mem_map_of_mem J.subtype hmem
  refine ⟨t, ?_⟩
  have hyinv : y⁻¹ = y := inv_eq_self_of_orderOf_eq_two hy
  change a⁻¹ * (y * (t : H) * y⁻¹ * (t : H)⁻¹) ∈ DH at hh
  convert hh using 1
  simp only [mul_inv_rev, hyinv, mul_assoc]

end Stellmacher.Recognition
