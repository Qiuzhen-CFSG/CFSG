module

public import Theory.GroupTheory.ElementaryInvolutionFixedJoin

/-!
# Changing an involution lift in the elementary fixed join

For a normal elementary abelian two-subgroup E, two involutions outside E
with the same image in G/E define the same subgroup ⟨a⟩(E ∩ C_G(a)).
Their difference is an involution in E, which commutes with either lift.
Thus the second lift lies in the first fixed join; the fixed-intersection
theorem identifies the two centralizer hyperplanes and hence the joins.

The fixed join also commutes with injective homomorphisms, allowing these
equalities to be transported through subgroup inclusions and conjugation.

This is the lift-change part of Parrott's representative choice at printed
p.676 of *A characterization of the Tits' simple group* (1972). Choosing a
conjugate quotient coset still requires an orbit argument.
-/

open Subgroup

/-- Fixed joins commute with injective homomorphisms. -/
public theorem Subgroup.map_zpowers_sup_inf_centralizer
    {G K : Type*} [Group G] [Group K]
    (E : Subgroup G) (a : G) (f : G →* K) (hf : Function.Injective f) :
    (zpowers a ⊔ (E ⊓ centralizer ({a} : Set G))).map f =
      zpowers (f a) ⊔ (E.map f ⊓ centralizer ({f a} : Set K)) := by
  rw [Subgroup.map_sup, MonoidHom.map_zpowers]
  congr 1
  apply le_antisymm
  · rintro x ⟨b, hb, rfl⟩
    refine ⟨mem_map_of_mem f hb.1, mem_centralizer_singleton_iff.mpr ?_⟩
    simpa only [map_mul] using congrArg f (mem_centralizer_singleton_iff.mp hb.2)
  · rintro x ⟨⟨b, hb, rfl⟩, hc⟩
    refine ⟨b, ⟨hb, mem_centralizer_singleton_iff.mpr ?_⟩, rfl⟩
    apply hf
    simpa only [map_mul] using mem_centralizer_singleton_iff.mp hc

private theorem mem_fixed_join_of_involution_quotient_eq
    {G : Type*} [Group G] (E : Subgroup G) [E.Normal] [IsElementaryAbelian 2 E]
    (a b : G) (ha : orderOf a = 2) (hb : orderOf b = 2)
    (hab : QuotientGroup.mk' E a = QuotientGroup.mk' E b) :
    b ∈ zpowers a ⊔ (E ⊓ centralizer ({a} : Set G)) := by
  have ha2 : a * a = 1 := by simpa only [pow_two, ha] using pow_orderOf_eq_one a
  have hb2 : b * b = 1 := by simpa only [pow_two, hb] using pow_orderOf_eq_one b
  have hai : a⁻¹ = a := inv_eq_iff_mul_eq_one.mpr ha2
  have hbi : b⁻¹ = b := inv_eq_iff_mul_eq_one.mpr hb2
  have hd : a⁻¹ * b ∈ E := QuotientGroup.eq.mp hab
  have hd2 : (a⁻¹ * b) ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian _ hd
  have hdi : (a⁻¹ * b)⁻¹ = a⁻¹ * b :=
    inv_eq_iff_mul_eq_one.mpr (by simpa only [pow_two] using hd2)
  have hcomm : b * a = a * b := by
    simpa only [mul_inv_rev, inv_inv, hai, hbi] using hdi
  have hdc : a⁻¹ * b ∈ centralizer ({a} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    calc
      a⁻¹ * b * a = a⁻¹ * (b * a) := mul_assoc _ _ _
      _ = b := by rw [hcomm, inv_mul_cancel_left]
      _ = a * (a⁻¹ * b) := (mul_inv_cancel_left _ _).symm
  have hm := (zpowers a ⊔ (E ⊓ centralizer ({a} : Set G))).mul_mem
    (show a ∈ zpowers a ⊔ (E ⊓ centralizer ({a} : Set G)) from
      mem_sup_left (mem_zpowers a))
    (show a⁻¹ * b ∈ zpowers a ⊔ (E ⊓ centralizer ({a} : Set G)) from
      mem_sup_right ⟨hd, hdc⟩)
  simpa only [mul_inv_cancel_left] using hm

/-- The fixed join depends only on the quotient coset of its involution lift. -/
public theorem elementary_involution_fixed_join_eq_of_quotient_eq
    {G : Type*} [Group G] [Finite G]
    (E : Subgroup G) [E.Normal] [IsElementaryAbelian 2 E]
    (a b : G) (ha : orderOf a = 2) (hb : orderOf b = 2)
    (haE : a ∉ E) (hbE : b ∉ E)
    (hab : QuotientGroup.mk' E a = QuotientGroup.mk' E b) :
    zpowers a ⊔ (E ⊓ centralizer ({a} : Set G)) =
      zpowers b ⊔ (E ⊓ centralizer ({b} : Set G)) := by
  have hbF := mem_fixed_join_of_involution_quotient_eq E a b ha hb hab
  have haF := mem_fixed_join_of_involution_quotient_eq E b a hb ha hab.symm
  obtain ⟨_, _, _, _, houter⟩ := elementary_involution_fixed_join_data E a ha haE
  have hfixed := houter b hbF (fun hh => hbE hh.1)
  apply le_antisymm
  · exact sup_le (zpowers_le.mpr haF) (hfixed.symm.le.trans le_sup_right)
  · exact sup_le (zpowers_le.mpr hbF) (hfixed.le.trans le_sup_right)
