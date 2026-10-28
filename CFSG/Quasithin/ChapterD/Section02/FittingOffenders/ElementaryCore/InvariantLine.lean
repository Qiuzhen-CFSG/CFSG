module

public import Theory.GroupTheory.PGroup.CharacteristicCenterReduction
public import Theory.GroupAction.KleinFourFactorization
public import Theory.GroupTheory.SpecificGroups.KleinFourGenerators
public import Theory.Frattini.PGroup

/-!
# Detecting the Frattini subgroup by an invariant central line

For a four-group A normalizing a finite three-group P, a nontrivial Φ(P)
contains an A-invariant central subgroup of order three. Intersect Φ(P) with
Z(P), use the nontrivial central intersection theorem, and restrict conjugation
to this characteristic intersection. The simultaneous fixed/inverted
factorization for two generators of A supplies a nonidentity element on which
each generator acts by a sign. An appropriate power has order three and its
cyclic subgroup is normalized by A.

The center and Frattini subgroup are intrinsic to P; their ambient images use
P.subtype. Only normalization by A is required, so neither normality of P in G
nor the additional source hypothesis C_P(A) = 1 is needed for this step.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), D.2.14(2), printed p.186: the detection step in the
passage from exclusion of central invariant lines in Φ(P) to Φ(P) = 1.
-/

open Subgroup
open scoped IsMulCommutative

namespace CFSG.Quasithin.ChapterD.ElementaryCore

private theorem exists_sign_element {H : Type*} [Group H] [Finite H] [Nontrivial H]
    (hodd : Odd (Nat.card H)) (a b : MulAut H)
    (ha : Function.Involutive a) (hb : Function.Involutive b) (hab : Commute a b) :
    ∃ x : H, x ≠ 1 ∧ (a x = x ∨ a x = x⁻¹) ∧ (b x = x ∨ b x = x⁻¹) := by
  obtain ⟨x, hx⟩ := exists_ne (1 : H)
  obtain ⟨⟨h, u, v, w⟩, he⟩ :=
    (MulAut.fixed_inverted_four_factor_bijective hodd a b ha hb hab).surjective x
  by_cases hh : h.val = 1
  · by_cases hu : u.val = 1
    · by_cases hv : v.val = 1
      · refine ⟨w, ?_, Or.inr w.property.1, Or.inr w.property.2⟩
        intro hw
        exact hx (by simpa only [hh, hu, hv, hw, one_mul] using he.symm)
      · exact ⟨v, hv, Or.inr v.property.1, Or.inl v.property.2⟩
    · exact ⟨u, hu, Or.inl u.property.1, Or.inr u.property.2⟩
  · exact ⟨h, hh, Or.inl h.property.1, Or.inl h.property.2⟩

private theorem exists_order_three_sign_element
    {H E : Type*} [Group H] [Finite H] [Nontrivial H]
    [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hH : IsPGroup 3 H) (hE : Nat.card E = 4) (f : E →* MulAut H) :
    ∃ x : H, orderOf x = 3 ∧ ∀ e : E, f e x = x ∨ f e x = x⁻¹ := by
  have hsquare (e : E) : e ^ 2 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 E) e
  have hinv (e : E) : Function.Involutive (f e) := by
    intro x
    change (f e * f e) x = x
    rw [← map_mul, ← pow_two, hsquare e, map_one]
    rfl
  let : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨a, ha⟩ := exists_ne (1 : E)
  obtain ⟨b, hb, hba⟩ := ENat.exists_ne_ne_of_three_le (α := E)
    (by simp only [ENat.card_eq_coe_natCard, hE]; decide) 1 a
  have hab : Commute a b := mul_comm a b
  have haa : a * a = 1 := by simpa only [pow_two] using hsquare a
  have hbb : b * b = 1 := by simpa only [pow_two] using hsquare b
  have hK := isKleinFour_closure_pair a b haa hbb ha hb hba.symm hab
  have hgen : closure ({a, b} : Set E) = ⊤ :=
    eq_top_of_card_eq _ (hK.card_four.trans hE.symm)
  have hforms (e : E) : e = 1 ∨ e = a ∨ e = b ∨ e = a * b :=
    (mem_closure_pair_iff a b haa hbb hab e).mp (by rw [hgen]; trivial)
  obtain ⟨n, hn⟩ := hH.exists_card_eq
  have hodd : Odd (Nat.card H) := hn ▸ (by decide : Odd 3).pow
  have hfcomm : Commute (f a) (f b) := hab.map f
  obtain ⟨y, hy, hya, hyb⟩ := exists_sign_element hodd (f a) (f b)
    (hinv a) (hinv b) hfcomm
  obtain ⟨m, hm⟩ := hH.exists_orderOf_eq_pow y
  have hm0 : m ≠ 0 := by
    intro h
    exact hy (orderOf_eq_one_iff.mp (by simpa only [h, pow_zero] using hm))
  have hd : 3 ∣ orderOf y := hm ▸ dvd_pow_self 3 hm0
  let x := y ^ (orderOf y / 3)
  have hx : orderOf x = 3 := orderOf_pow_orderOf_div (ne_of_gt (orderOf_pos y)) hd
  have hxa : f a x = x ∨ f a x = x⁻¹ := by
    rcases hya with h | h
    · exact Or.inl (by simp only [x, map_pow, h])
    · exact Or.inr (by simp only [x, map_pow, h, inv_pow])
  have hxb : f b x = x ∨ f b x = x⁻¹ := by
    rcases hyb with h | h
    · exact Or.inl (by simp only [x, map_pow, h])
    · exact Or.inr (by simp only [x, map_pow, h, inv_pow])
  refine ⟨x, hx, fun e => ?_⟩
  rcases hforms e with rfl | rfl | rfl | rfl
  · exact Or.inl (by simp)
  · exact hxa
  · exact hxb
  · rw [map_mul, MulAut.mul_apply]
    rcases hxa with ha | ha <;> rcases hxb with hb | hb <;> simp [ha, hb]

variable {G : Type*} [Group G] [Finite G]

/-- Nontrivial Φ(P) is detected by an A-invariant ambient central line of order three. -/
public theorem exists_invariant_central_line_in_frattini
    (P A : Subgroup G) (hP : IsPGroup 3 P)
    [IsElementaryAbelian 2 A] (hA : Nat.card A = 4)
    (hn : A ≤ normalizer (P : Set G)) (hphi : frattini P ≠ ⊥) :
    ∃ Z : Subgroup G, Z ≤ (center P).map P.subtype ∧ Nat.card Z = 3 ∧
      A ≤ normalizer (Z : Set G) ∧ Z ≤ (frattini P).map P.subtype := by
  let D : Subgroup P := center P ⊓ frattini P
  have hD : D ≠ ⊥ := center_inf_ne_bot_of_normal hP (frattini P) hphi
  let : Nontrivial D := (nontrivial_iff_ne_bot D).mpr hD
  let f : A →* MulAut D := (MulAut.characteristic D).comp
    (P.normalizerMonoidHom.comp (inclusion hn))
  obtain ⟨x, hx, hs⟩ := exists_order_three_sign_element (hP.to_subgroup D) hA f
  let z : G := (x.val : G)
  refine ⟨zpowers z, zpowers_le.mpr ?_, ?_, ?_, zpowers_le.mpr ?_⟩
  · exact mem_map_of_mem P.subtype x.property.1
  · rw [Nat.card_zpowers]
    simpa only [z, Subgroup.orderOf_coe] using hx
  · intro a ha
    rw [mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    rcases hs ⟨a, ha⟩ with hf | hf
    · have hz : a * z * a⁻¹ = z := congrArg (fun u : D => (u.val : G)) hf
      change zpowers (a * z * a⁻¹) = zpowers z
      rw [hz]
    · have hz : a * z * a⁻¹ = z⁻¹ := congrArg (fun u : D => (u.val : G)) hf
      change zpowers (a * z * a⁻¹) = zpowers z
      rw [hz, zpowers_inv]
  · exact mem_map_of_mem P.subtype x.property.2

end CFSG.Quasithin.ChapterD.ElementaryCore
