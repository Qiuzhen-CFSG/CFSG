module

public import Theory.GroupAction.Extraspecial27InvolutionFixed
public import Theory.Frattini.PGroup

/-!
# Extraspecial three-groups with a center-fixing involution

The Frattini subgroup of an extraspecial three-group is its center.
At order 27, a nonidentity involutive automorphism fixing the center has
exponent-three domain and inverts its Frattini quotient. The fixed/inverted
factorization puts the fixed factor in the center; the cube of the inverted
factor is both fixed and inverted, and hence trivial by odd order.

This supplies the exponent and inversion assertions in Aschbacher--Smith,
*The Classification of Quasithin Groups*, Appendix D, printed p.192
(`refs/quasithin.pdf`, PDF p.203).
-/

@[expose] public section

open Subgroup
namespace IsExtraspecial

theorem frattini_eq_center_three
    {P : Type*} [Group P] [Finite P] [IsExtraspecial 3 P] :
    frattini P = center P := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP : IsPGroup 3 P := isPGroup 3 P
  let : Fact (IsPGroup 3 P) := ⟨hP⟩
  let : IsElementaryAbelian 3 (P ⧸ center P) := quotient_elementary_abelian 3 P
  let : Fact (IsPGroup 3 (P ⧸ center P)) := ⟨hP.to_quotient _⟩
  have hle : frattini P ≤ center P := by
    have h := frattini_le_comap_frattini_of_surjective
      (QuotientGroup.mk'_surjective (center P))
    rw [frattini_eq_bot_of_isElementaryAbelian (R := P ⧸ center P) (p := 3)] at h
    simpa using h
  have hne : frattini P ≠ ⊥ := by
    intro hbot
    let : IsElementaryAbelian 3 P :=
      (frattini_eq_bot_iff_isElementaryAbelian (p := 3)).mp hbot
    let : Nontrivial (P ⧸ center P) := quotient_nontrivial 3 P
    have hs : Subsingleton (P ⧸ center P) :=
      QuotientGroup.subsingleton_iff.mpr center_eq_top
    exact not_subsingleton (P ⧸ center P) hs
  have hd : Nat.card (frattini P) ∣ 3 := by
    rw [← center_order_p 3 P]
    exact card_dvd_of_le hle
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with hc | hc
  · exact (hne (card_eq_one.mp hc)).elim
  · apply eq_of_le_of_card_ge hle
    rw [hc, center_order_p 3 P]

theorem exponent_and_frattini_inversion_of_card27
    {P : Type*} [Group P] [Finite P] [IsExtraspecial 3 P]
    (hP : Nat.card P = 27) (a : MulAut P) (ha : Function.Involutive a)
    (hne : a ≠ 1) (hcenter : ∀ z ∈ center P, a z = z) :
    Monoid.exponent P = 3 ∧
      ∀ x : P, QuotientGroup.mk' (frattini P) (a x) =
        (QuotientGroup.mk' (frattini P) x)⁻¹ := by
  have hodd : Odd (Nat.card P) := by rw [hP]; decide
  have hfixed := MulAut.fixed_eq_center_of_extraspecial27_involution hP a ha hne hcenter
  let : IsElementaryAbelian 3 (P ⧸ center P) := quotient_elementary_abelian 3 P
  have hcube (x : P) : x ^ 3 ∈ center P := by
    apply (QuotientGroup.eq_one_iff _).mp
    change (QuotientGroup.mk' (center P)) (x ^ 3) = 1
    rw [map_pow]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 3 (P ⧸ center P)) _
  have hcubec (c : P) (hc : c ∈ center P) : c ^ 3 = 1 := by
    have hh := pow_card_eq_one' (x := (⟨c, hc⟩ : center P))
    rw [center_order_p 3 P] at hh
    exact congrArg Subtype.val hh
  have hdata (x : P) : x ^ 3 = 1 ∧
      QuotientGroup.mk' (center P) (a x) = (QuotientGroup.mk' (center P) x)⁻¹ := by
    obtain ⟨⟨c,v⟩, ⟨hc,hv,hcv⟩, _⟩ :=
      Theory.GroupTheory.existsUnique_fixed_inverted_mul_of_odd_card hodd a ha x
    have hcZ : c ∈ center P := hfixed ▸ ((MulAut.mem_fixedSubgroup a c).mpr hc)
    have hv3 : v ^ 3 = 1 := by
      have hi : v ^ 3 = (v ^ 3)⁻¹ := by
        calc
          v ^ 3 = a (v ^ 3) := (hcenter _ (hcube v)).symm
          _ = (v ^ 3)⁻¹ := by rw [map_pow, hv, inv_pow]
      have hs : (v ^ 3) ^ 2 = 1 := by
        rw [pow_two]
        calc
          v ^ 3 * v ^ 3 = (v ^ 3)⁻¹ * v ^ 3 := congrArg (· * v ^ 3) hi
          _ = 1 := inv_mul_cancel _
      exact hodd.coprime_two_right.pow_left_bijective.injective
        (hs.trans (one_pow 2).symm)
    constructor
    · rw [← hcv, (show Commute c v from (mem_center_iff.mp hcZ v).symm).mul_pow,
        hcubec c hcZ, hv3, mul_one]
    · have hqc : QuotientGroup.mk' (center P) c = 1 :=
        (QuotientGroup.eq_one_iff _).mpr hcZ
      rw [← hcv, map_mul, hc, hv, map_mul, map_inv, map_mul, hqc, one_mul, one_mul]
  constructor
  · have hd : Monoid.exponent P ∣ 3 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x => (hdata x).1
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
    · have hall : ∀ x : P, x = 1 := by
        intro x
        simpa [h1] using Monoid.pow_exponent_eq_one x
      have : Subsingleton P := ⟨fun x y => (hall x).trans (hall y).symm⟩
      have hh : Nat.card P = 1 := Nat.card_unique
      omega
    · exact h3
  · intro x
    apply QuotientGroup.eq_iff_div_mem.mpr
    change a x / x⁻¹ ∈ frattini P
    rw [frattini_eq_center_three (P := P)]
    exact QuotientGroup.eq_iff_div_mem.mp (hdata x).2
end IsExtraspecial
