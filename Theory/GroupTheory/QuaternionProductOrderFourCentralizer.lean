module

public import Theory.GroupTheory.QuaternionCentralProductIntrinsic

/-!
# Order-four witnesses in embedded quaternion products

Every element of Q₈ times a commuting subgroup centralizes an element
of order four in the quaternion factor: choose a commuting quaternion
coordinate, then retain its embedding. Conjugation transports the
witness back through the actual conjugator.

For an embedded Q₈ ◦ Q₈ containing a proper normal subgroup V, its
generating involutions give one outside V. If all involutions in the
actual quotient are conjugate, lifting that conjugator supplies both
involution lifts and coverage of ambient involutions by conjugates of
the quaternion product. No classification of group extensions is used.

Source: the local nonsplit-block route for Aschbacher–Smith 14.4.5,
printed p.1008. The single quotient involution class is an explicit
separate model fact, not inferred from a family name.
-/

open Subgroup
open scoped Pointwise

namespace Subgroup

private theorem quaternion_commuting_four : ∀ x : QuaternionGroup 2,
    ∃ r : QuaternionGroup 2, Commute x r ∧ orderOf r = 4 := by
  have h : ∀ x : QuaternionGroup 2, ∃ r, x*r = r*x ∧ r^4=1 ∧ r^2≠1 := by decide
  intro x
  obtain ⟨r,hr,hr4,hr2⟩ := h x
  refine ⟨r,hr,?_⟩
  have hd := orderOf_dvd_of_pow_eq_one hr4
  have hn : ¬ orderOf r ∣ 2 := fun hh => hr2 (orderOf_dvd_iff_pow_eq_one.mp hh)
  have hle : orderOf r ≤ 4 := Nat.le_of_dvd (by decide) hd
  interval_cases horder : orderOf r <;> simp_all

/-- Every element of a product of a quaternion group with a commuting group
centralizes an element of order four in the first factor. -/
public theorem exists_commuting_order_four_of_quaternion_product
    {G : Type*} [Group G] (B C : Subgroup G)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b*c=c*b)
    (x : G) (hx : x ∈ B ⊔ C) : ∃ r ∈ B, Commute x r ∧ orderOf r = 4 := by
  obtain ⟨e⟩ := hB
  have hn : C ≤ normalizer (B : Set G) := by
    apply le_trans ?_ (centralizer_le_normalizer _)
    intro c hc b hb
    exact hcomm b hb c hc
  have hprod : x ∈ (B : Set G) * (C : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left B C hn]
    exact hx
  obtain ⟨b,hb,c,hc,rfl⟩ := hprod
  obtain ⟨r,hr,hr4⟩ := quaternion_commuting_four (e ⟨b,hb⟩)
  let rB := e.symm r
  have hbr : Commute b (rB : G) := by
    have hh : Commute (⟨b,hb⟩ : B) rB := by
      apply e.injective
      simpa only [map_mul, rB, MulEquiv.apply_symm_apply] using hr.eq
    exact hh.map B.subtype
  have hcr : Commute c (rB : G) := (hcomm rB rB.property c hc).symm
  refine ⟨rB,rB.property,hbr.mul_left hcr,?_⟩
  rw [Subgroup.orderOf_coe]
  exact e.symm.orderOf_eq r |>.trans hr4

/-- The witness retains the actual quaternion-product carrier. -/
public theorem QuaternionCentralProductData.exists_commuting_order_four
    {U : Type*} [Group U] (d : QuaternionCentralProductData U) (x : U) :
    ∃ r : U, Commute x r ∧ orderOf r = 4 := by
  obtain ⟨r,_,hr,hr4⟩ := exists_commuting_order_four_of_quaternion_product
    d.left d.right d.left_model d.commute x (d.span ▸ mem_top x)
  exact ⟨r,hr,hr4⟩

/-- Conjugating into an embedded quaternion product transports its order-four
witness back with the same actual conjugator. -/
public theorem exists_commuting_order_four_of_conj_mem_quaternion
    {G : Type*} [Group G] (U : Subgroup G) (d : QuaternionCentralProductData U)
    (y g : G) (hyg : MulAut.conj g y ∈ U) :
    ∃ r : G, Commute y r ∧ orderOf r = 4 := by
  obtain ⟨r,hr,hr4⟩ := d.exists_commuting_order_four (⟨MulAut.conj g y,hyg⟩ : U)
  refine ⟨MulAut.conj g⁻¹ (r : G), ?_, ?_⟩
  · have h := (hr.map U.subtype).map (MulAut.conj g⁻¹).toMonoidHom
    change Commute (MulAut.conj g⁻¹ (MulAut.conj g y))
      (MulAut.conj g⁻¹ (r : G)) at h
    have hy : MulAut.conj g⁻¹ (MulAut.conj g y) = y := by
      simp [MulAut.conj_apply, mul_assoc]
    rwa [hy] at h
  · rw [(MulAut.conj g⁻¹).orderOf_eq, Subgroup.orderOf_coe, hr4]


/-- The generating involutions of a quaternion product cannot all lie in a
proper subgroup. This produces a nontrivial quotient involution without
assuming splitting of the ambient extension. -/
public theorem exists_involution_outside_of_quaternion_core
    {G : Type*} [Group G] [Finite G] (V U : Subgroup G)
    (d : QuaternionCentralProductData U) (hproper : ¬ U ≤ V) :
    ∃ z ∈ U, z ∉ V ∧ z^2 = 1 := by
  classical
  by_contra hn
  apply hproper
  have hle : closure {x : U | x ∈ d.left ⊔ d.right ∧ x^2=1} ≤ V.subgroupOf U := by
    apply (closure_le _).mpr
    intro x hx
    by_contra hxV
    exact hn ⟨x,x.property,hxV,congrArg Subtype.val hx.2⟩
  rw [quaternion_central_product_involutions_generate d.left d.right d.left_model
    d.right_model d.intersection_card d.commute, d.span] at hle
  intro x hx
  exact hle (show (⟨x,hx⟩ : U) ∈ ⊤ from mem_top _)

/-- A single involution class in the actual quotient suffices both to lift
quotient involutions and to conjugate every ambient involution into U. -/
public theorem quaternion_involution_lifts_and_cover_of_single_quotient_class
    {G : Type*} [Group G] [Finite G] (V U : Subgroup G) [V.Normal]
    (d : QuaternionCentralProductData U) (hVU : V ≤ U) (hproper : ¬ U ≤ V)
    (hclass : ∀ a b : G ⧸ V, orderOf a = 2 → orderOf b = 2 → IsConj a b) :
    (∀ q : G ⧸ V, orderOf q = 2 →
      ∃ y : G, y^2=1 ∧ QuotientGroup.mk' V y = q) ∧
    (∀ y : G, orderOf y = 2 → ∃ g : G, MulAut.conj g y ∈ U) := by
  let π := QuotientGroup.mk' V
  obtain ⟨z,hzU,hzV,hz2⟩ := exists_involution_outside_of_quaternion_core V U d hproper
  have hzq : orderOf (π z) = 2 := orderOf_eq_prime
    (by rw [← map_pow,hz2,map_one])
    (fun h => hzV ((QuotientGroup.eq_one_iff z).mp h))
  have hconj (x g : G) : π (MulAut.conj g x) = MulAut.conj (π g) (π x) := by
    simp only [MulAut.conj_apply,map_mul,map_inv]
  constructor
  · intro q hq
    obtain ⟨c,hc⟩ := isConj_iff.mp (hclass (π z) q hzq hq)
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective V c
    exact ⟨MulAut.conj g z, by rw [← map_pow,hz2,map_one], (hconj z g).trans hc⟩
  · intro y hy
    by_cases hyV : y ∈ V
    · exact ⟨1, by simpa using hVU hyV⟩
    have hyq : orderOf (π y) = 2 := orderOf_eq_prime
      (by rw [← map_pow, ← hy,pow_orderOf_eq_one,map_one])
      (fun h => hyV ((QuotientGroup.eq_one_iff y).mp h))
    obtain ⟨c,hc⟩ := isConj_iff.mp (hclass (π y) (π z) hyq hzq)
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective V c
    have hh : π (MulAut.conj g y) = π z := (hconj y g).trans hc
    have hv : z⁻¹ * MulAut.conj g y ∈ V := (QuotientGroup.eq_one_iff _).mp (by
      change π (z⁻¹ * MulAut.conj g y) = 1
      rw [map_mul,map_inv,hh,inv_mul_cancel])
    refine ⟨g, ?_⟩
    simpa only [mul_inv_cancel_left] using U.mul_mem hzU (hVU hv)

end Subgroup
