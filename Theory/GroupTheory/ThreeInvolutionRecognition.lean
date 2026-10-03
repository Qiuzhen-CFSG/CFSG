module

public import Theory.GroupTheory.QuaternionGenerated
public import Theory.GroupTheory.AbelianExponentFourRecognition
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Theory.GroupTheory.NormalizedSupCard

namespace ThreeInvolution

variable {G : Type*} [Group G]

public theorem swap_of_square (first second central : G)
    (hfirst : first ^ 2 = 1) (hsecond : second ^ 2 = 1)
    (hsquare : (first * second) ^ 2 = central) :
    first * second = central * (second * first) := by
  calc
    first * second = (first * second) ^ 2 * (second * first) := by
      simp only [pow_two] at hfirst hsecond ⊢
      simp only [mul_assoc, ← mul_assoc second second, hsecond, one_mul,
        hfirst, mul_one]
    _ = central * (second * first) := by rw [hsquare]

public theorem product_square (first second third central : G)
    (hfirst : first ^ 2 = 1) (hsecond : second ^ 2 = 1)
    (hthird : third ^ 2 = 1) (hcentral : central ^ 2 = 1)
    (hcf : Commute central first) (hcs : Commute central second)
    (hfs : (first * second) ^ 2 = central)
    (hst : (second * third) ^ 2 = central)
    (hft : (first * third) ^ 2 = central) :
    (first * second * third) ^ 2 = central := by
  have hsf := swap_of_square first second central hfirst hsecond hfs
  have hts := swap_of_square second third central hsecond hthird hst
  have htf := swap_of_square first third central hfirst hthird hft
  have hf : first * first = 1 := by simpa [pow_two] using hfirst
  have hs : second * second = 1 := by simpa [pow_two] using hsecond
  have ht : third * third = 1 := by simpa [pow_two] using hthird
  have hz : central * central = 1 := by simpa [pow_two] using hcentral
  calc
    (first * second * third) ^ 2 =
        first * second * (third * first) * second * third := by simp [pow_two, mul_assoc]
    _ = first * second * (central * (first * third)) * second * third := by
      rw [show third * first = central * (first * third) from
        by rw [htf, ← mul_assoc, hz, one_mul]]
    _ = central * (first * second * first) * (third * second) * third := by
      rw [← mul_assoc (first * second) central, ← (hcf.mul_right hcs).eq]
      group
    _ = central * (central * second) * (central * (second * third)) * third := by
      rw [show first * second * first = central * second by rw [hsf]; simp [mul_assoc, hf]]
      rw [show third * second = central * (second * third) from
        by rw [hts, ← mul_assoc, hz, one_mul]]
    _ = central := by
      simp only [mul_assoc, hcs.eq, ← mul_assoc central central, hz, one_mul,
        ← mul_assoc second second, hs, ht, mul_one]

public structure Relations (first second third central : G) : Prop where
  first_square : first ^ 2 = 1
  second_square : second ^ 2 = 1
  third_square : third ^ 2 = 1
  central_square : central ^ 2 = 1
  central_ne_one : central ≠ 1
  central_first : Commute central first
  central_second : Commute central second
  central_third : Commute central third
  first_second_square : (first * second) ^ 2 = central
  second_third_square : (second * third) ^ 2 = central
  first_third_square : (first * third) ^ 2 = central

public theorem commute_mul_of_swaps (moving left right central : G)
    (hcentral : central ^ 2 = 1) (hleft : Commute central left)
    (hswapLeft : moving * left = central * (left * moving))
    (hswapRight : moving * right = central * (right * moving)) :
    Commute moving (left * right) := by
  change moving * (left * right) = left * right * moving
  calc
    moving * (left * right) = central * (left * (moving * right)) := by
      rw [← mul_assoc, hswapLeft, mul_assoc, mul_assoc]
    _ = central * (left * (central * (right * moving))) := by rw [hswapRight]
    _ = left * right * moving := by
      rw [← mul_assoc left central, ← hleft.eq, ← mul_assoc,
        ← mul_assoc central central, ← pow_two, hcentral]
      simp [mul_assoc]

namespace Relations

variable {first second third central : G}
variable (relations : Relations first second third central)

include relations

public theorem triple_square : (first * second * third) ^ 2 = central :=
  product_square first second third central relations.first_square relations.second_square
    relations.third_square relations.central_square relations.central_first
    relations.central_second relations.first_second_square relations.second_third_square
    relations.first_third_square

public theorem triple_order : orderOf (first * second * third) = 4 := by
  apply orderOf_eq_four_of_fourth_power
  · rw [show 4 = 2 * 2 from rfl, pow_mul, relations.triple_square,
      relations.central_square]
  · rw [relations.triple_square]
    exact relations.central_ne_one

public theorem first_second_order : orderOf (first * second) = 4 := by
  apply orderOf_eq_four_of_fourth_power
  · rw [show 4 = 2 * 2 from rfl, pow_mul, relations.first_second_square,
      relations.central_square]
  · rw [relations.first_second_square]
    exact relations.central_ne_one

public theorem first_second_swap : first * second = central * (second * first) :=
  swap_of_square first second central relations.first_square relations.second_square
    relations.first_second_square

public theorem second_third_swap : second * third = central * (third * second) :=
  swap_of_square second third central relations.second_square relations.third_square
    relations.second_third_square

public theorem first_third_swap : first * third = central * (third * first) :=
  swap_of_square first third central relations.first_square relations.third_square
    relations.first_third_square

public theorem second_first_swap : second * first = central * (first * second) := by
  rw [relations.first_second_swap, ← mul_assoc, ← pow_two,
    relations.central_square, one_mul]

public theorem third_second_swap : third * second = central * (second * third) := by
  rw [relations.second_third_swap, ← mul_assoc, ← pow_two,
    relations.central_square, one_mul]

public theorem third_first_swap : third * first = central * (first * third) := by
  rw [relations.first_third_swap, ← mul_assoc, ← pow_two,
    relations.central_square, one_mul]

public theorem triple_commute_first : Commute (first * second * third) first := by
  have hpair := commute_mul_of_swaps first second third central
    relations.central_square relations.central_second relations.first_second_swap
    relations.first_third_swap
  simpa only [mul_assoc] using ((Commute.refl first).mul_right hpair).symm

public theorem triple_commute_second : Commute (first * second * third) second := by
  have hpair := commute_mul_of_swaps second first third central
    relations.central_square relations.central_first relations.second_first_swap
    relations.second_third_swap
  have hequal : first * second * third = central * (first * third * second) := by
    rw [mul_assoc, relations.second_third_swap, ← mul_assoc first central,
      ← relations.central_first.eq]
    simp only [mul_assoc]
  rw [hequal]
  exact relations.central_second.mul_left (hpair.mul_right (Commute.refl second)).symm

public theorem triple_commute_third : Commute (first * second * third) third := by
  have hpair := commute_mul_of_swaps third first second central
    relations.central_square relations.central_first relations.third_first_swap
    relations.third_second_swap
  exact (hpair.mul_right (Commute.refl third)).symm

public theorem triple_centralizes :
    first * second * third ∈ Subgroup.centralizer
      (Subgroup.closure ({first, second, third} : Set G) : Set G) := by
  rw [Subgroup.centralizer_closure]
  intro element helement
  rcases helement with rfl | rfl | rfl
  · exact relations.triple_commute_first.eq.symm
  · exact relations.triple_commute_second.eq.symm
  · exact relations.triple_commute_third.eq.symm

public theorem pair_product : (first * second) * (second * third) = first * third := by
  have hs : second * second = 1 := by simpa [pow_two] using relations.second_square
  simp only [mul_assoc, ← mul_assoc second second, hs, one_mul]

public theorem quaternion_inversion :
    (second * third) * (first * second) * (second * third)⁻¹ = (first * second)⁻¹ := by
  have hs : second * second = 1 := by simpa [pow_two] using relations.second_square
  have hf : first * first = 1 := by simpa [pow_two] using relations.first_square
  have hfi : first⁻¹ = first := inv_eq_of_mul_eq_one_right hf
  have hsi : second⁻¹ = second := inv_eq_of_mul_eq_one_right hs
  apply mul_right_cancel (b := second * third)
  rw [mul_assoc ((second * third) * (first * second)), inv_mul_cancel, mul_one,
    mul_inv_rev, hfi, hsi]
  calc
    second * third * (first * second) = second * (third * first) * second := by group
    _ = second * (central * (first * third)) * second := by rw [relations.third_first_swap]
    _ = central * (second * first) * (third * second) := by
      rw [← mul_assoc second central, ← relations.central_second.eq]
      group
    _ = central * (second * first) * (central * (second * third)) := by
      rw [relations.third_second_swap]
    _ = second * first * (second * third) := by
      rw [← mul_assoc (central * (second * first)) central,
        (relations.central_second.mul_right relations.central_first).eq,
        mul_assoc (second * first) central central, ← pow_two,
        relations.central_square, mul_one]

public theorem quaternion_outside : second * third ∉ Subgroup.zpowers (first * second) := by
  rintro ⟨power, hpower⟩
  have hcomm : Commute (second * third) (first * second) := by
    rw [← hpower]
    exact (Commute.refl (first * second)).zpow_left power
  have hequal : first * second = (first * second)⁻¹ := by
    simpa only [hcomm.eq, mul_inv_cancel_right] using relations.quaternion_inversion
  have hone : (first * second) ^ 2 = 1 := by
    rw [pow_two]
    nth_rw 2 [hequal]
    exact mul_inv_cancel _
  exact relations.central_ne_one (relations.first_second_square.symm.trans hone)

public theorem quaternion_model :
    Nat.card (Subgroup.closure ({first * second, second * third} : Set G)) = 8 ∧
      Nonempty (Subgroup.closure ({first * second, second * third} : Set G) ≃*
        QuaternionGroup 2) := by
  exact QuaternionGroup.closure_equiv_of_relations (by decide : 0 < 2)
    (first * second) (second * third) relations.first_second_order
    (relations.second_third_square.trans relations.first_second_square.symm)
    relations.quaternion_inversion relations.quaternion_outside

public theorem factor_join :
    Subgroup.closure ({first, second, third} : Set G) =
      Subgroup.zpowers (first * second * third) ⊔
        Subgroup.closure ({first * second, second * third} : Set G) := by
  let whole := Subgroup.closure ({first, second, third} : Set G)
  let factors := Subgroup.zpowers (first * second * third) ⊔
    Subgroup.closure ({first * second, second * third} : Set G)
  have htriple : first * second * third ∈ factors :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have hfirstSecond : first * second ∈ factors :=
    Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have hsecondThird : second * third ∈ factors :=
    Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have hfirst : first ∈ factors := by
    convert factors.mul_mem htriple (factors.inv_mem hsecondThird) using 1; group
  have hsecond : second ∈ factors := by
    convert factors.mul_mem (factors.inv_mem hfirst) hfirstSecond using 1; group
  have hthird : third ∈ factors := by
    convert factors.mul_mem (factors.inv_mem hfirstSecond) htriple using 1; group
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro element (rfl | rfl | rfl)
    · exact hfirst
    · exact hsecond
    · exact hthird
  · have hf : first ∈ whole := Subgroup.subset_closure (by simp)
    have hs : second ∈ whole := Subgroup.subset_closure (by simp)
    have ht : third ∈ whole := Subgroup.subset_closure (by simp)
    apply sup_le
    · exact Subgroup.zpowers_le.mpr (whole.mul_mem (whole.mul_mem hf hs) ht)
    · apply (Subgroup.closure_le _).mpr
      rintro element (rfl | rfl)
      · exact whole.mul_mem hf hs
      · exact whole.mul_mem hs ht

public theorem cyclic_factor_centralizes :
    Subgroup.zpowers (first * second * third) ≤ Subgroup.centralizer
      (Subgroup.closure ({first, second, third} : Set G) : Set G) :=
  Subgroup.zpowers_le.mpr relations.triple_centralizes

public theorem quaternion_factor_le :
    Subgroup.closure ({first * second, second * third} : Set G) ≤
      Subgroup.closure ({first, second, third} : Set G) := by
  rw [relations.factor_join]
  exact le_sup_right

public theorem factor_commute (left : G)
    (hleft : left ∈ Subgroup.zpowers (first * second * third)) (right : G)
    (hright : right ∈ Subgroup.closure ({first * second, second * third} : Set G)) :
    left * right = right * left :=
  (relations.cyclic_factor_centralizes hleft right
    (relations.quaternion_factor_le hright)).symm

public theorem factor_intersection_card [Finite G] :
    Nat.card (Subgroup.zpowers (first * second * third) ⊓
      Subgroup.closure ({first * second, second * third} : Set G) : Subgroup G) = 2 := by
  let cyclic := Subgroup.zpowers (first * second * third)
  let quaternion := Subgroup.closure ({first * second, second * third} : Set G)
  have hcentralCyclic : central ∈ cyclic := by
    rw [← relations.triple_square]
    exact cyclic.pow_mem (Subgroup.mem_zpowers _) 2
  have hcentralQuaternion : central ∈ quaternion := by
    rw [← relations.first_second_square]
    exact quaternion.pow_mem (Subgroup.subset_closure (by simp)) 2
  have hlower : Subgroup.zpowers central ≤ cyclic ⊓ quaternion :=
    Subgroup.zpowers_le.mpr ⟨hcentralCyclic, hcentralQuaternion⟩
  have hlowerCard : Nat.card (Subgroup.zpowers central) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime relations.central_square relations.central_ne_one
  have hupper : cyclic ⊓ quaternion ≤
      (Subgroup.center quaternion).map quaternion.subtype := by
    intro element helement
    refine ⟨⟨element, helement.2⟩, Subgroup.mem_center_iff.mpr ?_, rfl⟩
    intro other
    exact Subtype.ext (relations.factor_commute element helement.1 other other.property).symm
  obtain ⟨model⟩ := relations.quaternion_model.2
  have hmodelCenter : Nat.card (Subgroup.center (QuaternionGroup 2)) = 2 := by
    let predicate : QuaternionGroup 2 → Prop := fun element =>
      ∀ other : QuaternionGroup 2, other * element = element * other
    have hcard : Fintype.card {element // predicate element} = 2 := by decide
    rw [Nat.card_congr (Equiv.subtypeEquivRight
      (fun _ => Subgroup.mem_center_iff)), Nat.card_eq_fintype_card]
    exact hcard
  have hupperCard : Nat.card ((Subgroup.center quaternion).map quaternion.subtype) = 2 := by
    rw [Subgroup.card_subtype]
    exact (Nat.card_congr (Subgroup.centerCongr model).toEquiv).trans hmodelCenter
  have hlowerBound := Subgroup.card_le_of_le hlower
  have hupperBound := Subgroup.card_le_of_le hupper
  change Nat.card (cyclic ⊓ quaternion : Subgroup G) = 2
  omega

public theorem generated_card [Finite G] :
    Nat.card (Subgroup.closure ({first, second, third} : Set G)) = 16 := by
  have hnormalize : Subgroup.closure ({first * second, second * third} : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers (first * second * third) : Set G) := by
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro right hright left hleft
    exact relations.factor_commute left hleft right hright
  have hcard := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes
    (Subgroup.zpowers (first * second * third))
    (Subgroup.closure ({first * second, second * third} : Set G)) hnormalize
  rw [Nat.card_zpowers, relations.triple_order, relations.quaternion_model.1,
    relations.factor_intersection_card, ← relations.factor_join] at hcard
  omega

public theorem first_second_not_commute : ¬ Commute first second := by
  intro hcommute
  have hone : (first * second) ^ 2 = 1 := by
    rw [hcommute.mul_pow, relations.first_square, relations.second_square, one_mul]
  exact relations.central_ne_one (relations.first_second_square.symm.trans hone)

public theorem first_order : orderOf first = 2 := by
  apply orderOf_eq_prime relations.first_square
  intro hequal
  apply relations.first_second_not_commute
  rw [hequal]
  exact Commute.one_left second

public theorem first_not_cyclic : first ∉ Subgroup.zpowers (first * second * third) := by
  intro hfirst
  apply relations.first_second_not_commute
  exact (relations.cyclic_factor_centralizes hfirst second
    (Subgroup.subset_closure (by simp))).symm

public theorem first_cyclic_disjoint [Finite G] :
    Disjoint (Subgroup.zpowers first) (Subgroup.zpowers (first * second * third)) := by
  classical
  apply disjoint_iff_inf_le.mpr
  intro element helement
  obtain ⟨power, hpower, rfl⟩ := Finset.mem_image.mp
    (mem_zpowers_iff_mem_range_orderOf.mp helement.1)
  have hbound : power < 2 := by simpa [relations.first_order] using hpower
  change first ^ power = 1
  interval_cases power
  · exact pow_zero _
  · exact False.elim (relations.first_not_cyclic (by simpa using helement.2))

public theorem first_cyclic_model [Finite G] :
    Nat.card (Subgroup.zpowers first ⊔ Subgroup.zpowers (first * second * third) :
      Subgroup G) = 8 ∧
    Nonempty ((Subgroup.zpowers first ⊔ Subgroup.zpowers (first * second * third) :
      Subgroup G) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 4))) := by
  have hcomm (left : Subgroup.zpowers first)
      (right : Subgroup.zpowers (first * second * third)) :
      Commute (left : G) (right : G) := by
    obtain ⟨leftPower, hleft⟩ := left.property
    obtain ⟨rightPower, hright⟩ := right.property
    rw [← hleft, ← hright]
    exact relations.triple_commute_first.symm.zpow_zpow leftPower rightPower
  let productMap := (Subgroup.zpowers first).subtype.noncommCoprod
    (Subgroup.zpowers (first * second * third)).subtype hcomm
  have hinjective : Function.Injective productMap := by
    apply (MonoidHom.noncommCoprod_injective _ _ hcomm).mpr
    exact ⟨Subtype.val_injective, Subtype.val_injective,
      by simpa using relations.first_cyclic_disjoint⟩
  have hrange : productMap.range = Subgroup.zpowers first ⊔
      Subgroup.zpowers (first * second * third) := by
    exact (MonoidHom.noncommCoprod_range _ _ hcomm).trans (by simp)
  let firstModel : Subgroup.zpowers first ≃* Multiplicative (ZMod 2) :=
    mulEquivOfCyclicCardEq (by simpa using relations.first_order)
  let cyclicModel : Subgroup.zpowers (first * second * third) ≃* Multiplicative (ZMod 4) :=
    mulEquivOfCyclicCardEq (by simpa using relations.triple_order)
  let model := (MulEquiv.subgroupCongr hrange.symm).trans
    ((MonoidHom.ofInjective hinjective).symm.trans (firstModel.prodCongr cyclicModel))
  refine ⟨?_, ⟨model⟩⟩
  rw [Nat.card_congr model.toEquiv]
  simp

public theorem seed_centralizer_eq [Finite G] :
    Subgroup.closure ({first, second, third} : Set G) ⊓
      Subgroup.centralizer (Subgroup.closure ({first, central} : Set G) : Set G) =
        Subgroup.zpowers first ⊔ Subgroup.zpowers (first * second * third) := by
  let whole := Subgroup.closure ({first, second, third} : Set G)
  let seed := Subgroup.closure ({first, central} : Set G)
  let fixed := whole ⊓ Subgroup.centralizer (seed : Set G)
  let split := Subgroup.zpowers first ⊔ Subgroup.zpowers (first * second * third)
  have hfirst : first ∈ whole := Subgroup.subset_closure (by simp)
  have hsecond : second ∈ whole := Subgroup.subset_closure (by simp)
  have hthird : third ∈ whole := Subgroup.subset_closure (by simp)
  have hseed : seed ≤ whole := by
    apply (Subgroup.closure_le _).mpr
    rintro element (rfl | rfl)
    · exact hfirst
    · rw [← relations.first_second_square]
      exact whole.pow_mem (whole.mul_mem hfirst hsecond) 2
  have hsplit : split ≤ fixed := by
    apply sup_le
    · apply Subgroup.zpowers_le.mpr
      refine ⟨hfirst, ?_⟩
      change first ∈ Subgroup.centralizer (Subgroup.closure ({first, central} : Set G) : Set G)
      rw [Subgroup.centralizer_closure]
      rintro element (rfl | rfl)
      · rfl
      · exact relations.central_first.eq
    · apply Subgroup.zpowers_le.mpr
      refine ⟨whole.mul_mem (whole.mul_mem hfirst hsecond) hthird, ?_⟩
      exact Subgroup.centralizer_le hseed relations.triple_centralizes
  have hproper : fixed ≠ whole := by
    intro hequal
    have hfixed : second ∈ fixed := hequal ▸ hsecond
    apply relations.first_second_not_commute
    exact hfixed.2 first (Subgroup.subset_closure (by simp))
  have hfixedCardNe : Nat.card fixed ≠ 16 := by
    intro hcard
    apply hproper
    exact Subgroup.eq_of_le_of_card_ge inf_le_left
      (by rw [relations.generated_card, hcard])
  have hupper : Nat.card fixed ≤ 16 := by
    have hbound := Subgroup.card_le_of_le (show fixed ≤ whole from inf_le_left)
    rwa [relations.generated_card] at hbound
  have hlower : 8 ≤ Nat.card fixed := by
    have hbound := Subgroup.card_le_of_le hsplit
    rwa [relations.first_cyclic_model.1] at hbound
  have hdiv : Nat.card fixed ∣ 16 := by
    have hdivide := Subgroup.card_dvd_of_le (show fixed ≤ whole from inf_le_left)
    rwa [relations.generated_card] at hdivide
  have hfixedCard : Nat.card fixed = 8 := by
    obtain ⟨quotient, hequal⟩ := hdiv
    have hquotient : quotient ≤ 2 := by nlinarith
    interval_cases quotient <;> omega
  exact (Subgroup.eq_of_le_of_card_ge hsplit
    (by rw [hfixedCard, relations.first_cyclic_model.1])).symm

public theorem seed_centralizer_model [Finite G] :
    Nonempty ((Subgroup.closure ({first, second, third} : Set G) ⊓
      Subgroup.centralizer (Subgroup.closure ({first, central} : Set G) : Set G) :
        Subgroup G) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 4))) := by
  rw [relations.seed_centralizer_eq]
  exact relations.first_cyclic_model.2

end Relations

end ThreeInvolution
