module

public import Theory.GroupTheory.PGroup.OrderThirtyTwoFourFusion
public import Theory.GroupTheory.PGroup.NormalEightFour

/-!
# Fusion of a normal four without a normal elementary eight

In a Sylow two-subgroup of order 32 with a unique central involution, fusion
of the three involutions of a normal four identifies its centralizer as
`C₄ × C₄`. Only normal elementary subgroups of order at least eight are
excluded. The centralizer is normal because it has index two.

The argument extends `OrderThirtyTwoFourFusion`: central omega belongs to
the normal four under the normal-only bound. A characteristic subgroup of
order two in its centralizer would remain the central involution under a
fusion embedding, contradicting injectivity. The order-sixteen recognition
then applies, with the normality of the centralizer excluding exponent two.

Source: Janko–Thompson, Math. Z. 113 (1970), 1.3–1.4 and §4, printed p.393.
-/

open Subgroup

namespace NormalEightFourFusion

private theorem normal_map_of_characteristic_of_injective
    {H P : Type*} [Group H] [Group P]
    (f : H →* P) (hf : Function.Injective f) [f.range.Normal]
    (K : Subgroup H) [K.Characteristic] : (K.map f).Normal := by
  let e : H ≃* f.range := MulEquiv.ofBijective f.rangeRestrict
    ⟨fun _ _ h => hf (congrArg Subtype.val h), f.rangeRestrict_surjective⟩
  refine ⟨?_⟩
  rintro _ ⟨k, hk, rfl⟩ g
  let α : MulAut H := (e.trans (MulAut.conjNormal g)).trans e.symm
  refine ⟨α k, characteristic_iff_le_comap.mp inferInstance α hk, ?_⟩
  have h := e.apply_symm_apply ((MulAut.conjNormal g) (e k))
  exact congrArg Subtype.val h

private theorem normal_card_two_eq_omega_center
    {P : Type*} [Group P] [Finite P]
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 2)
    (K : Subgroup P) [K.Normal] (hK : Nat.card K = 2) :
    K = (omega₁ (center P) (p := 2)).map (center P).subtype := by
  have hcentral := central_of_normal_card_two K hK
  apply eq_of_le_of_card_ge
  · intro k hk
    refine ⟨⟨k, hcentral hk⟩, subset_closure ?_, rfl⟩
    change (⟨k, hcentral hk⟩ : center P) ^ (2 ^ 1) = 1
    apply Subtype.ext
    have hpow : (⟨k, hk⟩ : K) ^ 2 = 1 := by
      rw [← hK]
      exact pow_card_eq_one'
    simpa using congrArg Subtype.val hpow
  · rw [card_map_of_injective (center P).subtype_injective, hZ, hK]


/-- Fusion of the normal four excludes characteristic subgroups of order two
in its centralizer. -/
public theorem centralizer_four_no_characteristic_two
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (hS : Nat.card S = 32)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ A : Subgroup S, A.Normal ∧ IsElementaryAbelian 2 A ∧ 8 ≤ Nat.card A)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 4)
    (hfusion : ∀ x y : E, x ≠ 1 → y ≠ 1 → IsConj ((x : S) : G) ((y : S) : G))
    (K : Subgroup (centralizer (E : Set S))) [K.Characteristic] : Nat.card K ≠ 2 := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let C := centralizer (E : Set S)
  have hCi : C.index = 2 :=
    centralizer_index_eq_two_of_normal_four_of_card_omega_one_center_eq_two
      S.isPGroup' hZ E hE
  let : C.Normal := C.normal_of_index_eq_two hCi
  have hC : Nat.card C = 16 := by
    have hh := C.card_mul_index
    rw [hCi, hS] at hh
    omega
  intro hK
  let K₀ := K.map C.subtype
  let : K₀.Normal := ConjAct.normal_of_characteristic_of_normal
  have hK₀ : Nat.card K₀ = 2 := (card_map_of_injective C.subtype_injective).trans hK
  have hK₀Z := normal_card_two_eq_omega_center hZ K₀ hK₀
  have hK₀E : K₀ ≤ E := by
    rw [hK₀Z]
    exact omega_one_center_le_normal_four_of_no_normal_eight hno E hE
  let : Nontrivial K := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨a, ha⟩ := exists_ne (1 : K)
  let z : S := (a.val : C)
  have hzK : z ∈ K₀ := mem_map_of_mem C.subtype a.property
  have hz1 : z ≠ 1 := fun hh => ha (Subtype.ext (Subtype.ext hh))
  have hz : z ∈ center S := central_of_normal_card_two K₀ hK₀ hzK
  have hnot : ¬ E ≤ K₀ := by
    intro h
    have hh := card_le_of_le h
    omega
  obtain ⟨x, hxE, hxK⟩ := SetLike.not_le_iff_exists.mp hnot
  have hx1 : x ≠ 1 := fun hh => hxK (hh ▸ K₀.one_mem)
  have hxC : x ∈ C := le_centralizer E hxE
  let xC : C := ⟨x, hxC⟩
  have hxcentral : xC ∈ center C := by
    apply mem_center_iff.mpr
    intro c
    exact Subtype.ext (c.property x hxE).symm
  have hconj : IsConj ((xC : S) : G) (z : G) :=
    hfusion ⟨x, hxE⟩ ⟨z, hK₀E hzK⟩
      (fun hh => hx1 (congrArg Subtype.val hh))
      (fun hh => hz1 (congrArg Subtype.val hh))
  obtain ⟨f, hf, hfx⟩ := S.exists_injective_hom_of_central_isConj C xC hxcentral z hz hconj
  have hfr : Nat.card f.range = 16 := by
    rw [← Nat.card_congr (MulEquiv.ofBijective f.rangeRestrict
      ⟨fun _ _ h => hf (congrArg Subtype.val h), f.rangeRestrict_surjective⟩).toEquiv]
    exact hC
  let : f.range.Normal := f.range.normal_of_index_eq_two (by
    have hh := f.range.card_mul_index
    rw [hfr, hS] at hh
    omega)
  let : (K.map f).Normal := normal_map_of_characteristic_of_injective f hf K
  have hKf : Nat.card (K.map f) = 2 := (card_map_of_injective hf).trans hK
  have heq : K.map f = K₀ :=
    (normal_card_two_eq_omega_center hZ (K.map f) hKf).trans hK₀Z.symm
  have hzKf : f xC ∈ K.map f := by rw [hfx, heq]; exact hzK
  obtain ⟨k, hk, he⟩ := hzKf
  have hkx : k = xC := hf he
  exact hxK (mem_map_of_mem C.subtype (hkx ▸ hk))

/-- The centralizer of a fused normal four in this order-32 case is `C₄ × C₄`. -/
public theorem centralizer_four_equiv_c4_square
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (hS : Nat.card S = 32)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ A : Subgroup S, A.Normal ∧ IsElementaryAbelian 2 A ∧ 8 ≤ Nat.card A)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 4)
    (hfusion : ∀ x y : E, x ≠ 1 → y ≠ 1 → IsConj ((x : S) : G) ((y : S) : G)) :
    Nonempty ((centralizer (E : Set S)) ≃*
      (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) := by
  let C := centralizer (E : Set S)
  have hCi : C.index = 2 :=
    centralizer_index_eq_two_of_normal_four_of_card_omega_one_center_eq_two
      S.isPGroup' hZ E hE
  let : C.Normal := C.normal_of_index_eq_two hCi
  have hC : Nat.card C = 16 := by
    have hh := C.card_mul_index
    rw [hCi, hS] at hh
    omega
  have hEC : E ≤ C := le_centralizer E
  have hEZ : E.subgroupOf C ≤ center C := by
    intro e he
    apply mem_center_iff.mpr
    intro c
    exact Subtype.ext (c.property e he).symm
  have hZC : 4 ≤ Nat.card (center C) := by
    have hh := card_le_of_le hEZ
    rw [Nat.card_congr (subgroupOfEquivOfLe hEC).toEquiv, hE] at hh
    exact hh
  have hchar (K : Subgroup C) (hK : K.Characteristic) : Nat.card K ≠ 2 := by
    let : K.Characteristic := hK
    exact centralizer_four_no_characteristic_two S hS hZ hno E hE hfusion K
  let : IsMulCommutative C :=
    NormalSixteenCommutativity.isMulCommutative_of_card_sixteen_of_no_characteristic_two
      hC hZC hchar
  have hnot : ¬ (∀ x : C, x ^ 2 = 1) := by
    intro hh
    have hel : IsElementaryAbelian 2 C :=
      { toIsMulCommutative := inferInstance
        exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hh }
    exact hno ⟨C, inferInstance, hel, by omega⟩
  obtain ⟨x, hx⟩ := not_forall.mp hnot
  have hd : orderOf x ∣ 2 ^ 4 := by simpa [hC] using orderOf_dvd_natCard x
  obtain ⟨k, hk, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  have hdiv : 4 ∣ orderOf x := by
    have hnotdiv : ¬ orderOf x ∣ 2 := fun hh => hx (orderOf_dvd_iff_pow_eq_one.mp hh)
    rw [he] at hnotdiv ⊢
    interval_cases k <;> norm_num at hnotdiv <;> norm_num
  have hfour : ∃ x : C, orderOf x = 4 :=
    ⟨x ^ (orderOf x / 4), orderOf_pow_orderOf_div (orderOf_pos x).ne' hdiv⟩
  exact NormalSixteenC4Square.recognition_of_no_characteristic_two hC hchar hfour

end NormalEightFourFusion
