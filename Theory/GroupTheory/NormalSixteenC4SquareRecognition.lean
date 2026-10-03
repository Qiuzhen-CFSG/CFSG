module

public import Theory.GroupTheory.AbelianExponentFourRecognition
public import Theory.GroupTheory.NormalCenterQuotient
public import Theory.GroupTheory.NormalSixteenCommutativity

/-!
# Recognition of normal subgroups of order sixteen

A normal subgroup of order sixteen in a finite center-free group is commutative
if its center has at least four elements. Characteristic power kernels and
images cannot have order two in the ambient group. If the subgroup contains an
element of order four, this forces exponent four and exactly four involutions,
giving the model `Multiplicative (ZMod 4) × Multiplicative (ZMod 4)` in
`nonempty_mulEquiv_c4_square_of_normal_order_sixteen`.

The intrinsic `recognition_of_no_characteristic_two` isolates precisely the
exclusion used in this proof. This also applies to an order-sixteen
centralizer whose characteristic subgroups of order two are excluded by
fusion, as in Janko–Thompson, Math. Z. 113 (1970), p.393.
-/

namespace NormalSixteenC4Square

public theorem pow_ker_characteristic {X : Type*} [CommGroup X] (power : ℕ) :
    (powMonoidHom power : X →* X).ker.Characteristic := by
  apply Subgroup.characteristic_iff_le_comap.mpr
  intro automorphism element helement
  change (automorphism element) ^ power = 1
  change element ^ power = 1 at helement
  rw [← map_pow, helement, map_one]

public theorem pow_range_characteristic {X : Type*} [CommGroup X] (power : ℕ) :
    (powMonoidHom power : X →* X).range.Characteristic := by
  apply Subgroup.characteristic_iff_le_comap.mpr
  rintro automorphism element ⟨root, rfl⟩
  exact ⟨automorphism root, (map_pow automorphism root power).symm⟩

public theorem characteristic_card_ne_two
    {G : Type*} [Group G] (whole : Subgroup G) [whole.Normal]
    (hcenter : Subgroup.center G = ⊥)
    (part : Subgroup whole) [part.Characteristic] : Nat.card part ≠ 2 := by
  intro htwo
  let ambient := part.map whole.subtype
  let : ambient.Normal := ConjAct.normal_of_characteristic_of_normal
  have hcard : Nat.card ambient = 2 :=
    (Subgroup.card_map_of_injective whole.subtype_injective).trans htwo
  have hcentral := Subgroup.central_of_normal_card_two ambient hcard
  have hbot : ambient = ⊥ := le_bot_iff.mp (hcenter ▸ hcentral)
  simp [hbot] at hcard

/-- The abelian order-sixteen recognition only needs exclusion of
characteristic subgroups of order two. -/
public theorem recognition_of_no_characteristic_two
    {H : Type*} [Group H] [Finite H] [IsMulCommutative H]
    (hcard : Nat.card H = 16)
    (hchar : ∀ K : Subgroup H, K.Characteristic → Nat.card K ≠ 2)
    (hfour : ∃ element : H, orderOf element = 4) :
    Nonempty (H ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) := by
  let _ : CommGroup H := IsMulCommutative.instCommGroup
  let square : H →* H := powMonoidHom 2
  let fourth : H →* H := powMonoidHom 4
  let : square.ker.Characteristic := pow_ker_characteristic 2
  let : square.range.Characteristic := pow_range_characteristic 2
  let : fourth.range.Characteristic := pow_range_characteristic 4
  obtain ⟨root, hroot⟩ := hfour
  have hrootFourth : root ^ 4 = 1 := by
    rw [← hroot]
    exact pow_orderOf_eq_one root
  have hrootSquare : root ^ 2 ≠ 1 :=
    pow_ne_one_of_lt_orderOf (by decide) (by omega)
  have hkernelNontrivial : Nontrivial square.ker := by
    apply nontrivial_of_ne (⟨root ^ 2, by
      change (root ^ 2) ^ 2 = 1
      simpa [← pow_mul] using hrootFourth⟩ : square.ker) 1
    intro hequal
    exact hrootSquare (congrArg Subtype.val hequal)
  let := hkernelNontrivial
  have hkernelLower : 4 ≤ Nat.card square.ker := by
    have hpositive := Finite.one_lt_card (α := square.ker)
    have hnotTwo := hchar square.ker inferInstance
    have hdiv : Nat.card square.ker ∣ 16 := hcard ▸ square.ker.card_subgroup_dvd_card
    have hnotThree : Nat.card square.ker ≠ 3 := by
      intro hequal
      rw [hequal] at hdiv
      norm_num at hdiv
    omega
  have hproduct : Nat.card square.ker * Nat.card square.range = 16 := by
    simpa only [Subgroup.index_ker, hcard] using square.ker.card_mul_index
  have hrangeUpper : Nat.card square.range ≤ 4 := by nlinarith
  let restricted : square.range →* H := square.comp square.range.subtype
  have hrestrictedNontrivial : Nontrivial restricted.ker := by
    let element : square.range := ⟨root ^ 2, ⟨root, rfl⟩⟩
    have helement : element ∈ restricted.ker := by
      change (root ^ 2) ^ 2 = 1
      simpa [← pow_mul] using hrootFourth
    apply nontrivial_of_ne (⟨element, helement⟩ : restricted.ker) 1
    intro hequal
    exact hrootSquare (congrArg (fun value : restricted.ker => (value : H)) hequal)
  let := hrestrictedNontrivial
  have hrestrictedRange : restricted.range = fourth.range := by
    ext element
    constructor
    · rintro ⟨⟨squareElement, rootElement, hrootElement⟩, rfl⟩
      refine ⟨rootElement, ?_⟩
      change rootElement ^ 4 = squareElement ^ 2
      change rootElement ^ 2 = squareElement at hrootElement
      rw [← hrootElement, ← pow_mul]
    · rintro ⟨rootElement, rfl⟩
      refine ⟨⟨rootElement ^ 2, ⟨rootElement, rfl⟩⟩, ?_⟩
      change (rootElement ^ 2) ^ 2 = rootElement ^ 4
      rw [← pow_mul]
  have hfourthUpper : Nat.card fourth.range ≤ 2 := by
    have hproductRestricted := restricted.ker.card_mul_index
    rw [Subgroup.index_ker, hrestrictedRange] at hproductRestricted
    have hkernelRestricted := Finite.one_lt_card (α := restricted.ker)
    nlinarith
  have hfourthCard : Nat.card fourth.range = 1 := by
    have hpositive := Nat.card_pos (α := fourth.range)
    have hnotTwo := hchar fourth.range inferInstance
    omega
  have hfourthBot : fourth.range = ⊥ := Subgroup.card_eq_one.mp hfourthCard
  have hexponent (element : H) : element ^ 4 = 1 := by
    have hmem : fourth element ∈ fourth.range := ⟨element, rfl⟩
    simpa only [hfourthBot, Subgroup.mem_bot, fourth, powMonoidHom_apply] using hmem
  have hrangeNontrivial : Nontrivial square.range := by
    apply nontrivial_of_ne (⟨root ^ 2, ⟨root, rfl⟩⟩ : square.range) 1
    intro hequal
    exact hrootSquare (congrArg Subtype.val hequal)
  let := hrangeNontrivial
  have hrangeCard : Nat.card square.range = 4 := by
    have hpositive := Finite.one_lt_card (α := square.range)
    have hnotTwo := hchar square.range inferInstance
    have hdiv : Nat.card square.range ∣ 16 := hcard ▸ square.range.card_subgroup_dvd_card
    have hnotThree : Nat.card square.range ≠ 3 := by
      intro hequal
      rw [hequal] at hdiv
      norm_num at hdiv
    omega
  have hkernelCard : Nat.card square.ker = 4 := by rw [hrangeCard] at hproduct; omega
  exact nonempty_mulEquiv_c4_square_of_card_involutions hcard hexponent hkernelCard

public theorem recognition_of_commutative
    {G : Type*} [Group G] [Finite G] (whole : Subgroup G) [whole.Normal]
    [IsMulCommutative whole]
    (hcenter : Subgroup.center G = ⊥) (hcard : Nat.card whole = 16)
    (hfour : ∃ element : whole, orderOf element = 4) :
    Nonempty (whole ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) := by
  apply recognition_of_no_characteristic_two hcard ?_ hfour
  intro part hpart
  let : part.Characteristic := hpart
  exact characteristic_card_ne_two whole hcenter part

end NormalSixteenC4Square

public theorem nonempty_mulEquiv_c4_square_of_normal_order_sixteen
    {G : Type*} [Group G] [Finite G] (whole : Subgroup G) [whole.Normal]
    (hcenter : Subgroup.center G = ⊥) (hcard : Nat.card whole = 16)
    (hcenterCard : 4 ≤ Nat.card (Subgroup.center whole))
    (hfour : ∃ element : whole, orderOf element = 4) :
    Nonempty (whole ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) := by
  let : IsMulCommutative whole :=
    NormalSixteenCommutativity.isMulCommutative_of_normal_order_sixteen
      whole hcenter hcard hcenterCard
  exact NormalSixteenC4Square.recognition_of_commutative whole hcenter hcard hfour
