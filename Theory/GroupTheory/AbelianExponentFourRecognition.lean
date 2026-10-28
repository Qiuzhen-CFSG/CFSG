module

public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic

public theorem orderOf_eq_four_of_fourth_power
    {G : Type*} [Group G] {element : G}
    (hfourth : element ^ 4 = 1) (hsquare : element ^ 2 ≠ 1) :
    orderOf element = 4 := by
  have hdiv := orderOf_dvd_of_pow_eq_one hfourth
  have hnot : ¬ orderOf element ∣ 2 := by
    simpa only [orderOf_dvd_iff_pow_eq_one] using hsquare
  have hcases : orderOf element = 1 ∨ orderOf element = 2 ∨ orderOf element = 4 := by
    have hbound := Nat.le_of_dvd (by decide : 0 < 4) hdiv
    interval_cases horder : orderOf element <;> norm_num at *
  rcases hcases with horder | horder | horder
  · simp [horder] at hnot
  · simp [horder] at hnot
  · exact horder

public theorem disjoint_zpowers_of_order_four_distinct_squares
    {G : Type*} [Group G] [Finite G] {left right : G}
    (hleft : orderOf left = 4) (hright : orderOf right = 4)
    (hdistinct : left ^ 2 ≠ right ^ 2) :
    Disjoint (Subgroup.zpowers left) (Subgroup.zpowers right) := by
  classical
  have hleftSquare : left ^ 2 ≠ 1 := by
    exact (pow_ne_one_of_lt_orderOf (by decide : 2 ≠ 0)
      (by omega : 2 < orderOf left))
  have hrightSquare : right ^ 2 ≠ 1 := by
    exact (pow_ne_one_of_lt_orderOf (by decide : 2 ≠ 0)
      (by omega : 2 < orderOf right))
  apply disjoint_iff_inf_le.mpr
  intro element helement
  obtain ⟨leftPower, hleftPower, hleftEq⟩ := Finset.mem_image.mp
    (mem_zpowers_iff_mem_range_orderOf.mp helement.1)
  obtain ⟨rightPower, hrightPower, hrightEq⟩ := Finset.mem_image.mp
    (mem_zpowers_iff_mem_range_orderOf.mp helement.2)
  have hleftBound : leftPower < 4 := by simpa [hleft] using hleftPower
  have hrightBound : rightPower < 4 := by simpa [hright] using hrightPower
  have hequal : left ^ leftPower = right ^ rightPower := hleftEq.trans hrightEq.symm
  have hsquares := congrArg (fun value : G => value ^ 2) hequal
  have hleftReduce (power : ℕ) : left ^ power = left ^ (power % 4) := by
    simpa [hleft] using (pow_mod_orderOf left power).symm
  have hrightReduce (power : ℕ) : right ^ power = right ^ (power % 4) := by
    simpa [hright] using (pow_mod_orderOf right power).symm
  change element = 1
  interval_cases leftPower <;> interval_cases rightPower <;>
    norm_num [← pow_mul, hleftReduce, hrightReduce] at hsquares <;>
    simp_all

public theorem nonempty_mulEquiv_c4_square_of_independent_roots
    {G : Type*} [Group G] [Finite G]
    (hcard : Nat.card G = 16) (left right : G)
    (hleft : left ^ 4 = 1) (hright : right ^ 4 = 1)
    (hleftSquare : left ^ 2 ≠ 1) (hrightSquare : right ^ 2 ≠ 1)
    (hdistinct : left ^ 2 ≠ right ^ 2) (hcommute : Commute left right) :
    Nonempty (G ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) := by
  have hleftOrder := orderOf_eq_four_of_fourth_power hleft hleftSquare
  have hrightOrder := orderOf_eq_four_of_fourth_power hright hrightSquare
  have hdisjoint := disjoint_zpowers_of_order_four_distinct_squares
    hleftOrder hrightOrder hdistinct
  have hcomm (first : Subgroup.zpowers left) (second : Subgroup.zpowers right) :
      Commute (first : G) (second : G) := by
    obtain ⟨firstPower, hfirstPower⟩ := Subgroup.mem_zpowers_iff.mp first.property
    obtain ⟨secondPower, hsecondPower⟩ := Subgroup.mem_zpowers_iff.mp second.property
    rw [← hfirstPower, ← hsecondPower]
    exact hcommute.zpow_zpow firstPower secondPower
  let productMap := (Subgroup.zpowers left).subtype.noncommCoprod
    (Subgroup.zpowers right).subtype hcomm
  have hinjective : Function.Injective productMap := by
    apply (MonoidHom.noncommCoprod_injective _ _ hcomm).mpr
    exact ⟨Subtype.val_injective, Subtype.val_injective, by simpa using hdisjoint⟩
  have hproductCard : Nat.card (Subgroup.zpowers left × Subgroup.zpowers right) = 16 := by
    rw [Nat.card_prod, Nat.card_zpowers, Nat.card_zpowers, hleftOrder, hrightOrder]
  have hbijective : Function.Bijective productMap :=
    (Nat.bijective_iff_injective_and_card productMap).mpr
      ⟨hinjective, hproductCard.trans hcard.symm⟩
  let leftEquiv : Subgroup.zpowers left ≃* Multiplicative (ZMod 4) :=
    mulEquivOfCyclicCardEq (by simpa using hleftOrder)
  let rightEquiv : Subgroup.zpowers right ≃* Multiplicative (ZMod 4) :=
    mulEquivOfCyclicCardEq (by simpa using hrightOrder)
  exact ⟨(MulEquiv.ofBijective productMap hbijective).symm.trans
    (leftEquiv.prodCongr rightEquiv)⟩

public theorem nonempty_mulEquiv_c4_square_of_card_involutions
    {G : Type*} [CommGroup G] [Finite G]
    (hcard : Nat.card G = 16)
    (hexponent : ∀ element : G, element ^ 4 = 1)
    (hinvolutions : Nat.card {element : G // element ^ 2 = 1} = 4) :
    Nonempty (G ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) := by
  let square : G →* G := powMonoidHom 2
  have hkernel : Nat.card square.ker = 4 := hinvolutions
  have hrange : Nat.card square.range = 4 := by
    have hproduct := square.ker.card_mul_index
    rw [Subgroup.index_ker, hkernel, hcard] at hproduct
    omega
  have hnontrivial : square.range ≠ ⊥ := by
    intro hbot
    simp [hbot] at hrange
  obtain ⟨⟨leftSquare, hleftSquare⟩, hleftNontrivial⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp hnontrivial
  obtain ⟨left, rfl⟩ := hleftSquare
  have hleftNontrivial : left ^ 2 ≠ 1 :=
    fun hequal => hleftNontrivial (Subtype.ext hequal)
  have hleftOrder := orderOf_eq_four_of_fourth_power (hexponent left) hleftNontrivial
  have hcyclicCard : Nat.card (Subgroup.zpowers (left ^ 2)) = 2 := by
    rw [Nat.card_zpowers, orderOf_pow, hleftOrder]
    norm_num
  have hnotle : ¬ square.range ≤ Subgroup.zpowers (left ^ 2) := by
    intro hle
    have hbound := Subgroup.card_le_of_le hle
    rw [hrange, hcyclicCard] at hbound
    omega
  obtain ⟨rightSquare, hrightSquare, houtside⟩ := SetLike.not_le_iff_exists.mp hnotle
  obtain ⟨right, rfl⟩ := hrightSquare
  change right ^ 2 ∉ Subgroup.zpowers (left ^ 2) at houtside
  have hrightNontrivial : right ^ 2 ≠ 1 := by
    intro hone
    apply houtside
    rw [hone]
    exact (Subgroup.zpowers (left ^ 2)).one_mem
  have hdistinct : left ^ 2 ≠ right ^ 2 := by
    intro hequal
    apply houtside
    rw [← hequal]
    exact Subgroup.mem_zpowers (left ^ 2)
  exact nonempty_mulEquiv_c4_square_of_independent_roots hcard left right
    (hexponent left) (hexponent right) hleftNontrivial hrightNontrivial hdistinct
    (Commute.all left right)
