module

public import Theory.Frattini.BinarySquares
public import Mathlib.GroupTheory.SpecificGroups.KleinFour
public import Mathlib.GroupTheory.PGroup
public import Theory.GroupTheory.SpecificGroups.KleinFourAut

open scoped IsMulCommutative commutatorElement
open Subgroup

namespace IsPGroup

public theorem isMulCommutative_of_card_sixteen_of_exponent_four_of_square_range
    {H : Type*} [Group H] [Finite H]
    (hH : IsPGroup 2 H) (hcard : Nat.card H = 16)
    (hexp : ∀ x : H, x ^ 4 = 1)
    (hsquares : Set.range (fun x : H => x ^ 2) = (frattini H : Set H))
    (hphi : Nat.card (frattini H) = 4) : IsMulCommutative H := by
  let : Fact (IsPGroup 2 H) := ⟨hH⟩
  let V := frattini H
  have hVexp : ∀ x : V, x ^ 2 = 1 := by
    intro x
    apply Subtype.ext
    change (x : H) ^ 2 = 1
    have hxset : (x : H) ∈ (frattini H : Set H) := x.property
    rw [← hsquares] at hxset
    obtain ⟨z, hz⟩ := hxset
    rw [← hz]
    simpa [← pow_mul] using hexp z
  let : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by rw [hphi]; omega)
  have hVexp_eq : Monoid.exponent V = 2 := by
    have hd : Monoid.exponent V ∣ 2 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hVexp
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
    · exact ((Nat.ne_of_gt Monoid.one_lt_exponent) h).elim
    · exact h
  let : IsElementaryAbelian 2 V := {
    toIsMulCommutative := by
      apply isMulCommutative_iff.mpr
      intro x y
      exact mul_comm_of_exponent_two hVexp_eq x y
    exponent_dvd_p := by
      apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      exact hVexp }
  let : IsKleinFour V := ⟨hphi, hVexp_eq⟩
  have hsquare_mem (x : H) : x ^ 2 ∈ V :=
    pth_power_mem_frattini_of_isPGroup (p := 2) x
  let conj : H →* MulAut V := MulAut.conjNormal
  let R := conj.range
  have hR16 : Nat.card R ∣ 16 := by
    exact hcard ▸ Subgroup.card_range_dvd conj
  have hR6 : Nat.card R ∣ 6 := by
    rw [← IsKleinFour.card_mulAut V]
    exact R.card_subgroup_dvd_card
  have hRle : Nat.card R ≤ 6 := Nat.le_of_dvd (by decide) hR6
  have hRcases : Nat.card R = 1 ∨ Nat.card R = 2 := by
    interval_cases Nat.card R <;> omega
  have hcentral : V ≤ center H := by
    rcases hRcases with hR1 | hR2
    · let : Subsingleton R := (Nat.card_eq_one_iff_unique.mp hR1).1
      intro v hv
      apply mem_center_iff.mpr
      intro g
      have hgR : (⟨conj g, ⟨g, rfl⟩⟩ : R) = 1 := Subsingleton.elim _ _
      have hg : conj g = 1 := congrArg Subtype.val hgR
      have hv' := congrArg (fun f : MulAut V => (f ⟨v, hv⟩ : H)) hg
      have hvconj' : g * (v : H) * g⁻¹ = (v : H) := by
        simpa [conj, MulAut.conjNormal_apply] using hv'
      calc
        g * (v : H) = (g * (v : H) * g⁻¹) * g := by group
        _ = (v : H) * g := by rw [hvconj']
    · obtain ⟨u, hu, huuniq⟩ := (Nat.card_eq_two_iff' (1 : R)).mp hR2
      obtain ⟨a, ha⟩ := u.property
      have hconj_cases (g : H) : conj g = 1 ∨ conj g = conj a := by
        by_cases hg : conj g = 1
        · exact Or.inl hg
        · right
          have hgR : (⟨conj g, ⟨g, rfl⟩⟩ : R) ≠ 1 := by
            intro hh
            exact hg (congrArg Subtype.val hh)
          have hh := huuniq ⟨conj g, ⟨g, rfl⟩⟩ hgR
          exact congrArg Subtype.val hh |>.trans ha.symm
      have hfix_sq (g : H) : (conj a) ⟨g ^ 2, hsquare_mem g⟩ = ⟨g ^ 2, hsquare_mem g⟩ := by
        rcases hconj_cases g with hg | hg
        · have hcomm : ∀ v : V, g * (v : H) = (v : H) * g := by
            intro v
            have hvconj := congrArg (fun f : MulAut V => (f v : H)) hg
            have hvconj' : g * (v : H) * g⁻¹ = (v : H) := by
              simpa [conj, MulAut.conjNormal_apply] using hvconj
            calc
              g * (v : H) = (g * (v : H) * g⁻¹) * g := by group
              _ = (v : H) * g := by rw [hvconj']
          have hc : a * g * a⁻¹ * g⁻¹ ∈ V := by
            apply (commutator_le_frattini_of_isPGroup (R := H) (p := 2))
            exact commutator_mem_commutator (mem_top a) (mem_top g)
          apply Subtype.ext
          have hdecomp : a * g * a⁻¹ = (a * g * a⁻¹ * g⁻¹) * g := by group
          change a * (g ^ 2) * a⁻¹ = g ^ 2
          rw [show a * g ^ 2 * a⁻¹ = (a * g * a⁻¹) * (a * g * a⁻¹) by
            simp only [pow_two]
            group]
          rw [hdecomp]
          let d : H := a * g * a⁻¹ * g⁻¹
          have hd : d ∈ V := hc
          have hv := hcomm ⟨d, hd⟩
          have hd2 : d ^ 2 = 1 := congrArg Subtype.val (hVexp ⟨d, hd⟩)
          change d * g * (d * g) = g ^ 2
          calc
            d * g * (d * g) = d * (g * d) * g := by simp only [mul_assoc]
            _ = d * (d * g) * g := by rw [hv]
            _ = g ^ 2 := by
              rw [show d * (d * g) * g = d ^ 2 * g ^ 2 by
                simp only [pow_two, mul_assoc]]
              rw [hd2, one_mul]
        · have hh := congrArg (fun f : MulAut V => (f ⟨g ^ 2, hsquare_mem g⟩ : H)) hg
          apply Subtype.ext
          rw [MulAut.conjNormal_apply] at hh
          calc
            a * g ^ 2 * a⁻¹ = g * g ^ 2 * g⁻¹ := hh.symm
            _ = g ^ 2 := by group
      have halpha : conj a = 1 := by
        apply MulEquiv.ext
        intro v
        have hvset : (v : H) ∈ (frattini H : Set H) := v.property
        rw [← hsquares] at hvset
        obtain ⟨g, hg⟩ := hvset
        have hf := hfix_sq g
        have hg' : (⟨g ^ 2, hsquare_mem g⟩ : V) = v := by
          apply Subtype.ext
          exact hg
        rw [← hg']
        exact hf
      exact (hu (by
        apply Subtype.ext
        exact ha.symm.trans halpha)).elim
  let Q := H ⧸ V
  have hQcard : Nat.card Q = 4 := by
    have hh := V.card_mul_index
    rw [index_eq_card, hcard, hphi] at hh
    change 4 * Nat.card Q = 16 at hh
    omega
  let : IsElementaryAbelian 2 Q := by
    exact isElementaryAbelian_quotient_frattini (R := H) (p := 2)
  let : Nontrivial Q := Finite.one_lt_card_iff_nontrivial.mp (by rw [hQcard]; omega)
  let : IsKleinFour Q := ⟨hQcard, by
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact IsElementaryAbelian.exponent_eq_prime⟩
  let q : H →* Q := QuotientGroup.mk' V
  have hsame (x y : H) (hxy : q x = q y) :
      (⟨x ^ 2, hsquare_mem x⟩ : V) = ⟨y ^ 2, hsquare_mem y⟩ := by
    have hm : x⁻¹ * y ∈ V := (QuotientGroup.eq.mp hxy)
    have hc : Commute x (x⁻¹ * y) := mem_center_iff.mp (hcentral hm) x
    have he := hc.mul_pow 2
    have hd2 : (x⁻¹ * y) ^ 2 = 1 := congrArg Subtype.val (hVexp ⟨x⁻¹ * y, hm⟩)
    apply Subtype.ext
    simpa [mul_inv_cancel_left, hd2] using he.symm
  let square : Q → V :=
    Quotient.lift (fun x : H => (⟨x ^ 2, hsquare_mem x⟩ : V)) (by
      intro x y hxy
      exact hsame x y (Quotient.sound hxy))
  have hsq_surj : Function.Surjective square := by
    intro v
    have hvset : (v : H) ∈ (frattini H : Set H) := v.property
    rw [← hsquares] at hvset
    obtain ⟨x, hx⟩ := hvset
    refine ⟨q x, ?_⟩
    apply Subtype.ext
    change x ^ 2 = (v : H)
    exact hx
  let : Fintype Q := Fintype.ofFinite Q
  let : Fintype V := Fintype.ofFinite V
  have hcardQV : Fintype.card Q = Fintype.card V := by
    calc
      Fintype.card Q = Nat.card Q := (Nat.card_eq_fintype_card).symm
      _ = 4 := hQcard
      _ = Nat.card V := hphi.symm
      _ = Fintype.card V := Nat.card_eq_fintype_card
  have hsq_bij : Function.Bijective square :=
    (Fintype.bijective_iff_surjective_and_card square).2 ⟨hsq_surj, hcardQV⟩
  let e : Q ≃ V := Equiv.ofBijective square hsq_bij
  have hone : e 1 = 1 := by
    apply Subtype.ext
    change (1 : H) ^ 2 = 1
    simp
  let me : Q ≃* V := IsKleinFour.mulEquiv' e hone hVexp_eq
  have hmul (x y : H) : (x * y) ^ 2 = x ^ 2 * y ^ 2 := by
    have hm := me.map_mul (q x) (q y)
    change (⟨(x * y) ^ 2, hsquare_mem (x * y)⟩ : V) =
      ⟨x ^ 2, hsquare_mem x⟩ * ⟨y ^ 2, hsquare_mem y⟩ at hm
    exact congrArg Subtype.val hm
  exact ⟨⟨fun x y => by
    have hc : ⁅x, y⁆ ∈ V :=
      (commutator_le_frattini_of_isPGroup (R := H) (p := 2))
        (commutator_mem_commutator (mem_top x) (mem_top y))
    have hcent : ⁅x, y⁆ ∈ center H := hcentral hc
    have hsq := hmul x y
    have hformula : (x * y) ^ 2 = x ^ 2 * y ^ 2 * ⁅x,y⁆ := by
      symm
      calc
        x ^ 2 * y ^ 2 * ⁅x,y⁆ = ⁅x,y⁆ * (x ^ 2 * y ^ 2) := mem_center_iff.mp hcent _
        _ = x * y * x⁻¹ * (y⁻¹ * x ^ 2) * y ^ 2 := by
          simp only [commutatorElement_def, mul_assoc]
        _ = x * y * x⁻¹ * (x ^ 2 * y⁻¹) * y ^ 2 := by
          rw [mem_center_iff.mp (hcentral (hsquare_mem x))]
        _ = (x * y) ^ 2 := by simp only [pow_two]; group
    have heq : (x ^ 2 * y ^ 2) * 1 = (x ^ 2 * y ^ 2) * ⁅x,y⁆ := by
      calc
        (x ^ 2 * y ^ 2) * 1 = (x * y) ^ 2 := by simpa using hsq.symm
        _ = (x ^ 2 * y ^ 2) * ⁅x,y⁆ := hformula
    have hc1 : ⁅x,y⁆ = 1 := (mul_left_cancel heq).symm
    exact commutatorElement_eq_one_iff_mul_comm.mp hc1⟩⟩

end IsPGroup
