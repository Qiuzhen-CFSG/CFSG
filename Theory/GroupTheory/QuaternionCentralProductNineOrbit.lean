module

public import Theory.GroupTheory.QuaternionCentralProductNineAction
public import Theory.ElementaryAbelian.Extraspecial

/-!
# The involution orbit of an order-nine quaternion-product action

An order-nine subgroup acting on a normal, self-centralizing central product
of two quaternion groups acts independently on its two factors. Every
noncentral involution is a product of two noncentral factor elements. A
nonidentity cubic automorphism cycles the three quaternion axes: the known
fixed-coset theorem excludes a repeated axis, and a small finite calculation
covers all three axes and their signs. Inner conjugation supplies the signs.
The two independent factor moves therefore conjugate any two such involutions.

The prescribed actor construction is reused from `QuaternionCentralProductNineAction`.
The orbit argument requires no identification of the outer automorphism group.
Source: Janko–Thompson (1970), §4, printed p.390, PDF page 6 of
`refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf`.
-/

namespace QuaternionGroup
private abbrev Q := QuaternionGroup 2
private theorem central_square : ∀ x : Q, x ∈ Subgroup.center Q ↔ x ^ 2 = 1 := by decide
private theorem commuting_difference : ∀ x y : Q, x ^ 2 ≠ 1 → y ^ 2 ≠ 1 →
    x * y = y * x → x⁻¹ * y ∈ Subgroup.center Q := by decide
set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
private theorem three_axes : ∀ a b c y : Q,
    a * b ≠ b * a → b * c ≠ c * b → c * a ≠ a * c → y ^ 2 ≠ 1 →
    ∃ q : Q, q * a * q⁻¹ = y ∨ q * b * q⁻¹ = y ∨ q * c * q⁻¹ = y := by decide

private theorem cubic_orbit (e : MulAut Q) (he : e ^ 3 = 1) (hne : e ≠ 1)
    (x y : Q) (hx : x ^ 2 ≠ 1) (hy : y ^ 2 ≠ 1) :
    ∃ n : ℕ, ∃ q : Q, q * (e ^ n) x * q⁻¹ = y := by
  have hxe : (e x) ^ 2 ≠ 1 := by
    intro h
    apply hx
    apply e.injective
    simpa using h
  have hnc : x * e x ≠ e x * x := by
    intro h
    exact hx ((central_square x).mp
      (mem_center_of_central_difference_of_cube_eq_one_ne_one e he hne
        (commuting_difference x (e x) hx hxe h)))
  have hnc' : e x * e (e x) ≠ e (e x) * e x := by
    intro h
    exact hnc (e.injective (by simpa only [map_mul] using h))
  have he3 : e (e (e x)) = x := by
    have h := DFunLike.congr_fun he x
    simpa [pow_succ] using h
  have hnc'' : e (e x) * x ≠ x * e (e x) := by
    intro h
    apply hnc'
    apply e.injective
    simpa only [map_mul, he3] using h
  obtain ⟨q, h | h | h⟩ := three_axes x (e x) (e (e x)) y hnc hnc' hnc'' hy
  · exact ⟨0, q, by simpa using h⟩
  · exact ⟨1, q, by simpa using h⟩
  · exact ⟨2, q, by simpa [pow_two] using h⟩
end QuaternionGroup

namespace QuaternionGroup
private theorem cubic_orbit_of_equiv {G : Type*} [Group G] (model : G ≃* QuaternionGroup 2)
    (e : MulAut G) (he : e ^ 3 = 1) (hne : e ≠ 1)
    (x y : G) (hx : x ^ 2 ≠ 1) (hy : y ^ 2 ≠ 1) :
    ∃ n : ℕ, ∃ q : G, q * (e ^ n) x * q⁻¹ = y := by
  have hs (z : G) (hz : z ^ 2 ≠ 1) : (model z) ^ 2 ≠ 1 := by
    intro h
    exact hz (model.injective (by simpa using h))
  obtain ⟨n, q, hq⟩ := cubic_orbit (MulAut.congr model e)
    (by rw [← map_pow, he, map_one])
    (fun h => hne ((MulAut.congr model).injective (by simpa only [map_one] using h)))
    (model x) (model y) (hs x hx) (hs y hy)
  refine ⟨n, model.symm q, model.injective ?_⟩
  rw [← map_pow] at hq
  simpa [MulAut.congr_apply] using hq
end QuaternionGroup

namespace Subgroup
private theorem factor_move {G : Type*} [Group G] (B C A : Subgroup G)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (f : A →* MulAut B)
    (hf : ∀ a : A, ∀ b : B, (f a b : G) = a * b * (a : G)⁻¹)
    (a : A) (ha : a ^ 3 = 1) (hne : f a ≠ 1)
    (hcent : (a : G) ∈ centralizer (C : Set G))
    (b b' : B) (hb : b ^ 2 ≠ 1) (hb' : b' ^ 2 ≠ 1) :
    ∃ k ∈ centralizer (C : Set G), k * b * k⁻¹ = b' := by
  obtain ⟨model⟩ := hB
  obtain ⟨n, q, hq⟩ := QuaternionGroup.cubic_orbit_of_equiv model (f a)
    (by rw [← map_pow, ha, map_one]) hne b b' hb hb'
  refine ⟨(q : G) * (a : G) ^ n,
    (centralizer (C : Set G)).mul_mem (fun c hc => (hcomm q q.property c hc).symm)
      ((centralizer (C : Set G)).pow_mem hcent n), ?_⟩
  have hh := congrArg Subtype.val hq
  rw [← map_pow] at hh
  simp only [coe_mul, coe_inv, hf, coe_pow] at hh
  calc
    (q : G) * (a : G) ^ n * b * ((q : G) * (a : G) ^ n)⁻¹ =
      q * ((a : G) ^ n * b * ((a : G) ^ n)⁻¹) * (q : G)⁻¹ := by group
    _ = b' := hh

private theorem square_one_central {G : Type*} [Group G]
    (model : G ≃* QuaternionGroup 2) (x : G) (hx : x ^ 2 = 1) :
    x ∈ center G := by
  have ht : ∀ x y : QuaternionGroup 2, x ^ 2 = 1 → y * x = x * y := by decide
  apply mem_center_iff.mpr
  intro y
  apply model.injective
  simpa only [map_mul] using ht (model x) (model y) (by simpa using congrArg model hx)

private theorem involution_decomposition {G : Type*} [Group G] [Finite G]
    (B C : Subgroup G) (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (x : G) (hx : x ∈ B ⊔ C) (hx2 : x ^ 2 = 1)
    (hxZ : x ∉ centralizer ((B ⊔ C : Subgroup G) : Set G)) :
    ∃ b : B, ∃ c : C, (b : G) * c = x ∧ b ^ 2 ≠ 1 ∧ c ^ 2 ≠ 1 := by
  have hcB := intersection_eq_factor_center B C hB hinter hcomm
  have hcC := intersection_eq_factor_center C B hC (by simpa [inf_comm] using hinter)
    (fun c hc b hb => (hcomm b hb c hc).symm)
  have sqB (b : G) (hb : b ∈ B) (hs : b ^ 2 = 1) : b ∈ C := by
    have hz : b ∈ (center B).map B.subtype :=
      ⟨⟨b, hb⟩, square_one_central hB.some ⟨b, hb⟩ (Subtype.ext hs), rfl⟩
    rw [← hcB] at hz
    exact hz.2
  have sqC (c : G) (hc : c ∈ C) (hs : c ^ 2 = 1) : c ∈ B := by
    have hz : c ∈ (center C).map C.subtype :=
      ⟨⟨c, hc⟩, square_one_central hC.some ⟨c, hc⟩ (Subtype.ext hs), rfl⟩
    rw [← hcC] at hz
    exact hz.2
  have hninter : x ∉ B ⊓ C := by
    intro hi
    apply hxZ
    have hle : B ⊔ C ≤ centralizer ({x} : Set G) := by
      apply sup_le
      · exact fun b hb => mem_centralizer_singleton_iff.mpr (hcomm b hb x hi.2)
      · exact fun c hc => mem_centralizer_singleton_iff.mpr (hcomm x hi.1 c hc).symm
    exact fun y hy => mem_centralizer_singleton_iff.mp (hle hy)
  have hnB : x ∉ B := fun hxB => hninter ⟨hxB, sqB x hxB hx2⟩
  have hnC : x ∉ C := fun hxC => hninter ⟨sqC x hxC hx2, hxC⟩
  have hnorm : B ≤ normalizer (C : Set G) := by
    apply le_trans ?_ (centralizer_le_normalizer _)
    exact fun b hb c hc => (hcomm b hb c hc).symm
  change x ∈ ((B ⊔ C : Subgroup G) : Set G) at hx
  rw [coe_mul_of_left_le_normalizer_right B C hnorm] at hx
  obtain ⟨b, hb, c, hc, rfl⟩ := hx
  refine ⟨⟨b, hb⟩, ⟨c, hc⟩, rfl, ?_, ?_⟩
  · intro hs
    exact hnC (C.mul_mem (sqB b hb (congrArg Subtype.val hs)) hc)
  · intro hs
    exact hnB (B.mul_mem hb (sqC c hc (congrArg Subtype.val hs)))
end Subgroup

namespace Subgroup
/-- Independent cubic actions fuse all noncentral square-one elements of the join. -/
public theorem QuaternionIndependentCubics.isConj_of_noncentral_square_eq_one
    {G : Type*} [Group G] [Finite G] (B C : Subgroup G)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (actors : QuaternionIndependentCubics B C)
    (x y : G) (hx : x ∈ B ⊔ C) (hy : y ∈ B ⊔ C)
    (hx2 : x ^ 2 = 1) (hy2 : y ^ 2 = 1)
    (hxZ : x ∉ centralizer ((B ⊔ C : Subgroup G) : Set G))
    (hyZ : y ∉ centralizer ((B ⊔ C : Subgroup G) : Set G)) : IsConj x y := by
  obtain ⟨b, c, rfl, hb, hc⟩ := involution_decomposition B C hB hC hinter hcomm x hx hx2 hxZ
  obtain ⟨b', c', rfl, hb', hc'⟩ := involution_decomposition B C hB hC hinter hcomm y hy hy2 hyZ
  have hpow (a : actors.A) : a ^ 3 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp actors.elementary.exponent_dvd_p a
  obtain ⟨k, hk, hkb⟩ := factor_move B C actors.A hB hcomm actors.actionB
    actors.actionB_apply actors.x (hpow _) actors.x_actionB_ne_one actors.x_centralizes b b' hb hb'
  obtain ⟨l, hl, hlc⟩ := factor_move C B actors.A hC
    (fun c hc b hb => (hcomm b hb c hc).symm) actors.actionC
    actors.actionC_apply actors.y (hpow _) actors.y_actionC_ne_one actors.y_centralizes c c' hc hc'
  have hkc : k * (c : G) * k⁻¹ = c := by rw [← hk c c.property, mul_inv_cancel_right]
  have hlb : l * (b' : G) * l⁻¹ = b' := by rw [← hl b' b'.property, mul_inv_cancel_right]
  apply isConj_iff.mpr
  refine ⟨l * k, ?_⟩
  calc
    (l * k) * ((b : G) * c) * (l * k)⁻¹ =
      (l * (k * b * k⁻¹) * l⁻¹) * (l * (k * c * k⁻¹) * l⁻¹) := by group
    _ = (b' : G) * c' := by rw [hkb, hkc, hlb, hlc]

/-- An order-nine subgroup fuses the noncentral involutions of a normal,
self-centralizing quaternion central product. -/
public theorem isConj_noncentral_involutions_of_order_nine
    {K : Type*} [Group K] [Finite K] (H : Subgroup K) [H.Normal]
    (hself : centralizer (H : Set K) ≤ H)
    (B C : Subgroup H)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hjoin : B ⊔ C = ⊤)
    (hinter : Nat.card (B ⊓ C : Subgroup H) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (U : Subgroup K) (hU : Nat.card U = 9)
    (x y : H) (hx : orderOf x = 2) (hxZ : x ∉ center H)
    (hy : orderOf y = 2) (hyZ : y ∉ center H) : IsConj (x : K) (y : K) := by
  let B' := B.map H.subtype
  let C' := C.map H.subtype
  have hB' : Nonempty (B' ≃* QuaternionGroup 2) :=
    ⟨(B.equivMapOfInjective H.subtype H.subtype_injective).symm.trans hB.some⟩
  have hC' : Nonempty (C' ≃* QuaternionGroup 2) :=
    ⟨(C.equivMapOfInjective H.subtype H.subtype_injective).symm.trans hC.some⟩
  have hjoin' : B' ⊔ C' = H := by
    rw [← map_sup, hjoin]
    ext z
    exact ⟨fun ⟨w, _, hw⟩ => hw ▸ w.property, fun hz => ⟨⟨z, hz⟩, mem_top _, rfl⟩⟩
  have hinter' : Nat.card (B' ⊓ C' : Subgroup K) = 2 := by
    rw [← map_inf B C H.subtype H.subtype_injective, card_map_of_injective H.subtype_injective, hinter]
  have hcomm' : ∀ b ∈ B', ∀ c ∈ C', b * c = c * b := by
    rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩
    exact congrArg Subtype.val (hcomm b hb c hc)
  obtain ⟨actors, _⟩ := independent_cubics_of_nine_subgroup B' C' U hB' hC' hinter' hcomm'
    (by simpa only [hjoin'] using hself) hU
    (by rw [hjoin', H.normalizer_eq_top]; exact le_top)
  have hn (z : H) (hz : z ∉ center H) :
      (z : K) ∉ centralizer ((B' ⊔ C' : Subgroup K) : Set K) := by
    rw [hjoin']
    intro hh
    apply hz
    exact mem_center_iff.mpr (fun w => Subtype.ext (hh w w.property))
  apply QuaternionIndependentCubics.isConj_of_noncentral_square_eq_one B' C' hB' hC' hinter' hcomm' actors x y
    (by simpa only [hjoin'] using x.property) (by simpa only [hjoin'] using y.property)
    _ _ (hn x hxZ) (hn y hyZ)
  · exact congrArg Subtype.val (hx ▸ pow_orderOf_eq_one x)
  · exact congrArg Subtype.val (hy ▸ pow_orderOf_eq_one y)
end Subgroup

namespace Subgroup

/-- Compatibility constructor for the supplied order-nine actor interface. -/
public theorem exists_independent_cubics_of_order_nine
    {G : Type*} [Group G] [Finite G] (B C A : Subgroup G)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (hcentral : centralizer ((B ⊔ C : Subgroup G) : Set G) ≤ B ⊔ C)
    (hA : Nat.card A = 9)
    (hle : A ≤ normalizer ((B ⊔ C : Subgroup G) : Set G)) :
    Nonempty (QuaternionIndependentCubics B C) := by
  obtain ⟨actors, _⟩ := independent_cubics_of_nine_subgroup B C A hB hC hinter hcomm
    hcentral hA hle
  exact ⟨actors⟩

/-- The supplied-actor involution orbit theorem for an extraspecial group of
order thirty-two presented as a quaternion central product. -/
public theorem quaternion_involution_orbit_of_order_nine
    {K : Type*} [Group K] [Finite K] (H : Subgroup K) [H.Normal]
    (hself : centralizer (H : Set K) ≤ H)
    [IsExtraspecial 2 H] (_hH : Nat.card H = 32)
    (B C : Subgroup H)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hjoin : B ⊔ C = ⊤)
    (hinter : Nat.card (B ⊓ C : Subgroup H) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (U : Subgroup K) (hU : Nat.card U = 9)
    (x y : H) (hx : orderOf x = 2) (hxZ : x ∉ center H)
    (hy : orderOf y = 2) (hyZ : y ∉ center H) : IsConj (x : K) (y : K) :=
  isConj_noncentral_involutions_of_order_nine H hself B C hB hC hjoin hinter hcomm
    U hU x y hx hxZ hy hyZ

end Subgroup
