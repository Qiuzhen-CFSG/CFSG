module

public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderCoarse

@[expose] public section

open scoped IsMulCommutative commutatorElement

namespace SmallNonabelianTwoGroup

variable {Q : Type*} [Group Q] [Finite Q]

omit [Finite Q] in
theorem frattini_two_square_eq_one (hfrattini : Nat.card (frattini Q) = 2)
    (central : frattini Q) : central ^ 2 = 1 := by
  simpa only [hfrattini] using (pow_card_eq_one' (x := central))

omit [Finite Q] in
theorem square_eq_of_frattini_coset_eq (hfrattini : Nat.card (frattini Q) = 2)
    {left right : Q}
    (heq : (QuotientGroup.mk' (frattini Q)) left =
      (QuotientGroup.mk' (frattini Q)) right) : left ^ 2 = right ^ 2 := by
  have hmem : left⁻¹ * right ∈ frattini Q := QuotientGroup.eq.mp heq
  have hcentral := Subgroup.central_of_normal_card_two (frattini Q) hfrattini hmem
  have hcomm : Commute left (left⁻¹ * right) := Subgroup.mem_center_iff.mp hcentral left
  have hpow : (left⁻¹ * right) ^ 2 = 1 :=
    congrArg Subtype.val (frattini_two_square_eq_one hfrattini ⟨_, hmem⟩)
  have h := hcomm.mul_pow 2
  simpa only [mul_inv_cancel_left, hpow, mul_one] using h.symm

noncomputable def frattiniSquare (htwo : IsPGroup 2 Q)
    (hfrattini : Nat.card (frattini Q) = 2) : Q ⧸ frattini Q → frattini Q :=
  Quotient.lift
    (fun element => ⟨element ^ 2, by
      let : Fact (IsPGroup 2 Q) := ⟨htwo⟩
      exact pth_power_mem_frattini_of_isPGroup (p := 2) element⟩)
    (by
      intro left right heq
      apply Subtype.ext
      exact square_eq_of_frattini_coset_eq hfrattini (Quotient.sound heq))

theorem frattiniSquare_mk (htwo : IsPGroup 2 Q)
    (hfrattini : Nat.card (frattini Q) = 2) (element : Q) :
    (frattiniSquare htwo hfrattini (QuotientGroup.mk' (frattini Q) element) : Q) =
      element ^ 2 := rfl

theorem frattiniSquare_one (htwo : IsPGroup 2 Q)
    (hfrattini : Nat.card (frattini Q) = 2) :
    frattiniSquare htwo hfrattini 1 = 1 := by
  apply Subtype.ext
  exact one_pow 2

omit [Finite Q] in
theorem frattini_two_fixed (hfrattini : Nat.card (frattini Q) = 2)
    (aut : MulAut Q) (element : frattini Q) : aut (element : Q) = element := by
  obtain ⟨central, hcentral, hunique⟩ := (Nat.card_eq_two_iff' (1 : frattini Q)).mp hfrattini
  let image := MulAut.characteristic (frattini Q) aut element
  by_cases hone : element = 1
  · simp [hone]
  · have himage : image ≠ 1 := by
      intro h
      apply hone
      exact (MulAut.characteristic (frattini Q) aut).injective (h.trans (map_one _).symm)
    exact congrArg Subtype.val ((hunique image himage).trans (hunique element hone).symm)

theorem frattiniSquare_invariant (htwo : IsPGroup 2 Q)
    (hfrattini : Nat.card (frattini Q) = 2) (aut : MulAut Q)
    (vector : Q ⧸ frattini Q) :
    frattiniSquare htwo hfrattini (Subgroup.quotientAut (frattini Q) aut vector) =
      frattiniSquare htwo hfrattini vector := by
  induction vector using QuotientGroup.induction_on with
  | H element =>
    apply Subtype.ext
    change (frattiniSquare htwo hfrattini
      (Subgroup.quotientAut (frattini Q) aut (QuotientGroup.mk' (frattini Q) element)) : Q) =
        (frattiniSquare htwo hfrattini (QuotientGroup.mk' (frattini Q) element) : Q)
    rw [Subgroup.quotientAut_apply_mk, frattiniSquare_mk, frattiniSquare_mk]
    rw [← map_pow]
    exact frattini_two_fixed hfrattini aut
      (frattiniSquare htwo hfrattini (QuotientGroup.mk' (frattini Q) element))

theorem frattini_commutator_mem (htwo : IsPGroup 2 Q) (left right : Q) :
    ⁅left, right⁆ ∈ frattini Q := by
  let : Fact (IsPGroup 2 Q) := ⟨htwo⟩
  exact commutator_le_frattini_of_isPGroup (p := 2)
    (Subgroup.commutator_mem_commutator (Subgroup.mem_top left) (Subgroup.mem_top right))

theorem square_mul_eq_square_mul_square_mul_commutator
    (htwo : IsPGroup 2 Q) (hfrattini : Nat.card (frattini Q) = 2)
    (left right : Q) :
    (left * right) ^ 2 = left ^ 2 * right ^ 2 * ⁅left, right⁆ := by
  let : Fact (IsPGroup 2 Q) := ⟨htwo⟩
  have hcentral := Subgroup.central_of_normal_card_two (frattini Q) hfrattini
  have hleft : ∀ other : Q, other * left ^ 2 = left ^ 2 * other :=
    Subgroup.mem_center_iff.mp (hcentral (pth_power_mem_frattini_of_isPGroup (p := 2) left))
  have hcomm : ∀ other : Q, other * ⁅left, right⁆ = ⁅left, right⁆ * other :=
    Subgroup.mem_center_iff.mp (hcentral (frattini_commutator_mem htwo left right))
  symm
  calc
    left ^ 2 * right ^ 2 * ⁅left, right⁆ =
        ⁅left, right⁆ * (left ^ 2 * right ^ 2) := hcomm _
    _ = left * right * left⁻¹ * (right⁻¹ * left ^ 2) * right ^ 2 := by
      simp only [commutatorElement_def, mul_assoc]
    _ = left * right * left⁻¹ * (left ^ 2 * right⁻¹) * right ^ 2 := by rw [hleft]
    _ = (left * right) ^ 2 := by simp only [pow_two]; group

noncomputable def frattiniPolar (htwo : IsPGroup 2 Q)
    (hfrattini : Nat.card (frattini Q) = 2)
    (left right : Q ⧸ frattini Q) : frattini Q :=
  (frattiniSquare htwo hfrattini left * frattiniSquare htwo hfrattini right)⁻¹ *
    frattiniSquare htwo hfrattini (left * right)

theorem frattiniSquare_mul (htwo : IsPGroup 2 Q)
    (hfrattini : Nat.card (frattini Q) = 2) (left right : Q ⧸ frattini Q) :
    frattiniSquare htwo hfrattini (left * right) =
      frattiniSquare htwo hfrattini left * frattiniSquare htwo hfrattini right *
        frattiniPolar htwo hfrattini left right := by
  simp only [frattiniPolar, mul_inv_cancel_left]

theorem frattiniPolar_mk (htwo : IsPGroup 2 Q)
    (hfrattini : Nat.card (frattini Q) = 2) (left right : Q) :
    (frattiniPolar htwo hfrattini (QuotientGroup.mk' (frattini Q) left)
      (QuotientGroup.mk' (frattini Q) right) : Q) = ⁅left, right⁆ := by
  change (left ^ 2 * right ^ 2)⁻¹ * (left * right) ^ 2 = _
  rw [square_mul_eq_square_mul_square_mul_commutator htwo hfrattini]
  exact inv_mul_cancel_left _ _

theorem frattiniPolar_mul_left (htwo : IsPGroup 2 Q)
    (hfrattini : Nat.card (frattini Q) = 2) (left right other : Q ⧸ frattini Q) :
    frattiniPolar htwo hfrattini (left * right) other =
      frattiniPolar htwo hfrattini left other * frattiniPolar htwo hfrattini right other := by
  induction left using QuotientGroup.induction_on with
  | H left =>
    induction right using QuotientGroup.induction_on with
    | H right =>
      induction other using QuotientGroup.induction_on with
      | H other =>
        apply Subtype.ext
        change (frattiniPolar htwo hfrattini
          (QuotientGroup.mk' (frattini Q) (left * right))
          (QuotientGroup.mk' (frattini Q) other) : Q) =
            (frattiniPolar htwo hfrattini (QuotientGroup.mk' (frattini Q) left)
              (QuotientGroup.mk' (frattini Q) other) : Q) *
            (frattiniPolar htwo hfrattini (QuotientGroup.mk' (frattini Q) right)
              (QuotientGroup.mk' (frattini Q) other) : Q)
        simp only [frattiniPolar_mk]
        rw [commutatorElement_mul_left_eq_conj_mul]
        have hcentral := Subgroup.central_of_normal_card_two (frattini Q) hfrattini
        have hright := Subgroup.mem_center_iff.mp
          (hcentral (frattini_commutator_mem htwo right other))
        rw [hright left]
        simp only [mul_assoc, mul_inv_cancel, mul_one]
        exact (hright ⁅left, other⁆).symm

theorem frattiniPolar_nonzero (htwo : IsPGroup 2 Q)
    (hfrattini : Nat.card (frattini Q) = 2) (hnoncomm : ¬ IsMulCommutative Q) :
    ∃ left right, frattiniPolar htwo hfrattini left right ≠ 1 := by
  by_contra hnot
  push Not at hnot
  apply hnoncomm
  apply IsMulCommutative.of_comm
  intro left right
  apply commutatorElement_eq_one_iff_mul_comm.mp
  have heq := congrArg Subtype.val
    (hnot (QuotientGroup.mk' (frattini Q) left) (QuotientGroup.mk' (frattini Q) right))
  simpa only [frattiniPolar_mk, Subgroup.coe_one] using heq

omit [Finite Q] in
theorem frattini_two_elementary (hfrattini : Nat.card (frattini Q) = 2) :
    IsElementaryAbelian 2 (frattini Q) := by
  refine { toIsMulCommutative := IsMulCommutative.of_comm ?_, exponent_dvd_p := ?_ }
  · intro left right
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp
      (Subgroup.central_of_normal_card_two (frattini Q) hfrattini left.property) right).symm
  · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      (frattini_two_square_eq_one hfrattini)

theorem elementary_image_frattini_card_ge_four
    (hfrattini : Nat.card (frattini Q) = 2)
    (elementary : Subgroup Q) (helementaryCard : Nat.card elementary = 8) :
    4 ≤ Nat.card (elementary.map (QuotientGroup.mk' (frattini Q))) := by
  have hindex : (frattini Q).relIndex elementary =
      Nat.card (elementary.map (QuotientGroup.mk' (frattini Q))) := by
    simpa only [QuotientGroup.ker_mk'] using
      (Subgroup.relIndex_ker (K := elementary) (QuotientGroup.mk' (frattini Q)))
  have hsize := ((frattini Q).subgroupOf elementary).card_mul_index
  change Nat.card ((frattini Q).subgroupOf elementary) *
    (frattini Q).relIndex elementary = Nat.card elementary at hsize
  rw [hindex, helementaryCard] at hsize
  have hkernel : Nat.card ((frattini Q).subgroupOf elementary) ≤ 2 := by
    rw [← hfrattini]
    exact Nat.card_le_card_of_injective
      (fun element : (frattini Q).subgroupOf elementary =>
        (⟨(element.val : Q), element.property⟩ : frattini Q))
      (by
        intro left right heq
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun element : frattini Q => (element : Q)) heq)
  nlinarith

theorem elementary_image_frattini_singular (htwo : IsPGroup 2 Q)
    (hfrattini : Nat.card (frattini Q) = 2) (elementary : Subgroup Q)
    (helementary : IsElementaryAbelian 2 elementary)
    (vector : Q ⧸ frattini Q)
    (hvector : vector ∈ elementary.map (QuotientGroup.mk' (frattini Q))) :
    frattiniSquare htwo hfrattini vector = 1 := by
  obtain ⟨element, helement, rfl⟩ := hvector
  apply Subtype.ext
  change element ^ 2 = 1
  let : IsElementaryAbelian 2 elementary := helementary
  exact elemPow_eq_one_of_isElementaryAbelian element helement

omit [Finite Q] in
theorem frattini_quotient_card_sixteen_of_card_thirty_two
    (hQ : Nat.card Q = 32) (hfrattini : Nat.card (frattini Q) = 2) :
    Nat.card (Q ⧸ frattini Q) = 16 := by
  have hsize := Subgroup.card_eq_card_quotient_mul_card_subgroup (frattini Q)
  rw [hQ, hfrattini] at hsize
  omega

end SmallNonabelianTwoGroup
