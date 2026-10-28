module

public import Theory.GroupTheory.QuaternionCentralProductIndependentCubics
public import Theory.GroupTheory.QuaternionCentralProductNineAction.Recognition

/-!
# Independent cubic actions and a fixed cubic element in the outer quotient

An order-nine subgroup normalizing a self-centralizing quaternion central
product already supplies the two independent cubic actors. No exact order of
the full normalizer is needed. The subgroup is retained, so a caller can keep
any additional normalization properties of its chosen actors.

For a normal self-centralizing quaternion product in a group of order 1152,
an elementary sixteen meeting the product in order eight forces a factor
interchange. Its involution image cannot invert the normal elementary subgroup
of order nine in the quotient. Thus it centralizes a nonidentity cubic element.
The final theorem constructs the actors and proves this conclusion from the
Sylow order and index; it assumes neither weak closure nor the conclusion of
the action calculation.

The actor construction restricts the odd-order action to the intrinsic quaternion factors.
The pair of restrictions is faithful, and its two images have order three.
This extends the existing independent-cubics argument to the order-1152
normalizer case without changing that module's interface.

Source: Janko–Thompson (1970), §4, printed pp.390–391; the restriction proof
is adapted from this project's QuaternionCentralProductIndependentCubics.
The outer recognition is Aschbacher–Smith §5.3.7, printed p.661 (PDF p.678
of `refs/quasithin.pdf`).
-/

namespace Subgroup

private theorem independent_cubics_of_faithful_pair
    {A U V : Type*} [Group A] [Finite A] [Group U] [Finite U]
    [Group V] [Finite V] (hA : Nat.card A = 9)
    (hU : Nat.card U = 24) (hV : Nat.card V = 24)
    (f : A →* U) (g : A →* V) (hinj : Function.Injective (f.prod g)) :
    IsElementaryAbelian 3 A ∧ ∃ x y : A,
      orderOf x = 3 ∧ orderOf y = 3 ∧
      f x ≠ 1 ∧ g x = 1 ∧ f y = 1 ∧ g y ≠ 1 ∧
      ∀ a : A, ∃ i j : ℤ, a = x ^ i * y ^ j := by
  classical
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let F : A →* f.range × g.range := f.rangeRestrict.prod g.rangeRestrict
  have hF : Function.Injective F := by
    intro a b h
    apply hinj
    exact congrArg (fun p : f.range × g.range => ((p.1 : U), (p.2 : V))) h
  have hfc : Nat.card f.range ∣ 3 := by
    have h := Nat.dvd_gcd (card_range_dvd f) f.range.card_subgroup_dvd_card
    simpa [hA, hU] using h
  have hgc : Nat.card g.range ∣ 3 := by
    have h := Nat.dvd_gcd (card_range_dvd g) g.range.card_subgroup_dvd_card
    simpa [hA, hV] using h
  have hfle := Nat.le_of_dvd (by decide : 0 < 3) hfc
  have hgle := Nat.le_of_dvd (by decide : 0 < 3) hgc
  have hprod := Nat.card_le_card_of_injective F hF
  rw [hA, Nat.card_prod] at hprod
  have hfc' : Nat.card f.range = 3 := by nlinarith
  have hgc' : Nat.card g.range = 3 := by nlinarith
  have hsurj : Function.Surjective F :=
    (hF.bijective_of_nat_card_le (by rw [Nat.card_prod, hfc', hgc', hA])).2
  have hpow (a : A) : a ^ 3 = 1 := by
    apply hF
    rw [map_pow, map_one]
    apply Prod.ext
    · exact hfc' ▸ pow_card_eq_one' (x := (F a).1)
    · exact hgc' ▸ pow_card_eq_one' (x := (F a).2)
  refine ⟨{
    toIsMulCommutative := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hA
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hpow }, ?_⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := f.range) 3 (hfc' ▸ dvd_rfl)
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' (G := g.range) 3 (hgc' ▸ dvd_rfl)
  have hu1 : u ≠ 1 := by intro h; simp [h] at hu
  have hv1 : v ≠ 1 := by intro h; simp [h] at hv
  obtain ⟨x, hx⟩ := hsurj (u, 1)
  obtain ⟨y, hy⟩ := hsurj (1, v)
  have hfx : f x ≠ 1 := by
    intro h
    apply hu1
    apply Subtype.ext
    exact (congrArg (fun p : f.range × g.range => (p.1 : U)) hx).symm.trans h
  have hgy : g y ≠ 1 := by
    intro h
    apply hv1
    apply Subtype.ext
    exact (congrArg (fun p : f.range × g.range => (p.2 : V)) hy).symm.trans h
  refine ⟨x, y, orderOf_eq_prime (hpow x) (fun h => hfx (h ▸ f.map_one)),
    orderOf_eq_prime (hpow y) (fun h => hgy (h ▸ g.map_one)), hfx,
    congrArg (fun p : f.range × g.range => (p.2 : V)) hx,
    congrArg (fun p : f.range × g.range => (p.1 : U)) hy, hgy, ?_⟩
  intro a
  obtain ⟨i, hi⟩ := mem_zpowers_iff.mp (mem_zpowers_of_prime_card hfc' hu1 (g' := (F a).1))
  obtain ⟨j, hj⟩ := mem_zpowers_iff.mp (mem_zpowers_of_prime_card hgc' hv1 (g' := (F a).2))
  refine ⟨i, j, hF ?_⟩
  rw [map_mul, map_zpow, map_zpow, hx, hy]
  exact Prod.ext (by simpa using hi.symm) (by simpa using hj.symm)

private theorem nine_subgroup_normalizes_quaternion_factors
    {G : Type*} [Group G] [Finite G] (B C A : Subgroup G)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (hA : Nat.card A = 9) (hle : A ≤ normalizer ((B ⊔ C : Subgroup G) : Set G)) :
    A ≤ normalizer (B : Set G) ∧ A ≤ normalizer (C : Set G) := by
  have hfix (a : G) (ha : a ∈ A) :
      B.map (MulAut.conj a).toMonoidHom = B ∧
      C.map (MulAut.conj a).toMonoidHom = C := by
    have ha9 : a ^ 9 = 1 := by
      have h := pow_card_eq_one' (x := (⟨a, ha⟩ : A))
      rw [hA] at h
      exact congrArg Subtype.val h
    have hsq : (a ^ 5) ^ 2 = a := by
      rw [← pow_mul]
      change a ^ (9 + 1) = a
      rw [pow_succ, ha9, one_mul]
    have hcomp : (MulAut.conj (a ^ 5)).toMonoidHom.comp
        (MulAut.conj (a ^ 5)).toMonoidHom = (MulAut.conj a).toMonoidHom := by
      have h : MulAut.conj (a ^ 5) * MulAut.conj (a ^ 5) = MulAut.conj a := by
        rw [← map_mul, ← pow_two, hsq]
      exact congrArg MulEquiv.toMonoidHom h
    have h := quaternion_factors_invariant_of_square B C hB hC hinter hcomm
      (MulAut.conj (a ^ 5)) (mem_normalizer_iff_map_conj_eq.mp (hle (A.pow_mem ha 5)))
    simpa only [map_map, hcomp] using h
  exact ⟨fun a ha => mem_normalizer_iff_map_conj_eq.mpr (hfix a ha).1,
    fun a ha => mem_normalizer_iff_map_conj_eq.mpr (hfix a ha).2⟩

private theorem faithful_quaternion_restrictions
    {G : Type*} [Group G] [Finite G] (B C A : Subgroup G)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (hcentral : centralizer ((B ⊔ C : Subgroup G) : Set G) ≤ B ⊔ C)
    (hA : Nat.card A = 9) (f : A →* MulAut B) (g : A →* MulAut C)
    (hf : ∀ a : A, ∀ b : B, (f a b : G) = a * b * (a : G)⁻¹)
    (hg : ∀ a : A, ∀ c : C, (g a c : G) = a * c * (a : G)⁻¹) :
    Function.Injective (f.prod g) := by
  apply (injective_iff_map_eq_one (f.prod g)).mpr
  intro a ha
  have hfa : f a = 1 := congrArg Prod.fst ha
  have hga : g a = 1 := congrArg Prod.snd ha
  have hfix : B ⊔ C ≤ centralizer {(a : G)} := by
    apply sup_le
    · intro b hb
      apply mem_centralizer_singleton_iff.mpr
      have h := hf a ⟨b, hb⟩
      rw [hfa] at h
      exact eq_mul_inv_iff_mul_eq.mp h
    · intro c hc
      apply mem_centralizer_singleton_iff.mpr
      have h := hg a ⟨c, hc⟩
      rw [hga] at h
      exact eq_mul_inv_iff_mul_eq.mp h
  have hac : (a : G) ∈ centralizer ((B ⊔ C : Subgroup G) : Set G) := by
    intro q hq
    exact mem_centralizer_singleton_iff.mp (hfix hq)
  let z : center (B ⊔ C : Subgroup G) :=
    ⟨⟨a, hcentral hac⟩, mem_center_iff.mpr (fun q => Subtype.ext (hac q q.property))⟩
  have ha2 : (a : G) ^ 2 = 1 := by
    have h := pow_card_eq_one' (x := z)
    rw [quaternion_central_product_center_card B C hB hC hinter hcomm] at h
    exact congrArg (fun z : center (B ⊔ C : Subgroup G) =>
      ((z : (B ⊔ C : Subgroup G)) : G)) h
  have ha9 : (a : G) ^ 9 = 1 := by
    have h := pow_card_eq_one' (x := a)
    rw [hA] at h
    exact congrArg Subtype.val h
  have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one ha2) (orderOf_dvd_of_pow_eq_one ha9)
  have ho : orderOf (a : G) = 1 := Nat.dvd_one.mp (by simpa using hd)
  exact Subtype.ext (orderOf_eq_one_iff.mp ho)

private theorem quaternion_cubic_fixed_center
    {G : Type*} [Group G] [Finite G] (B C A : Subgroup G)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (f : A →* MulAut B)
    (hf : ∀ a : A, ∀ b : B, (f a b : G) = a * b * (a : G)⁻¹)
    (x : A) (hx3 : x ^ 3 = 1) (hne : f x ≠ 1)
    (hxC : (x : G) ∈ centralizer (C : Set G)) :
    B ⊓ centralizer {(x : G)} = (center B).map B.subtype := by
  apply le_antisymm
  · intro b hb
    refine ⟨⟨b, hb.1⟩, ?_, rfl⟩
    obtain ⟨eB⟩ := hB
    apply QuaternionGroup.fixed_mem_center_of_cube_eq_one_ne_one_of_equiv eB (f x)
      (by rw [← map_pow, hx3, map_one]) hne
    apply Subtype.ext
    rw [hf]
    exact mul_inv_eq_of_eq_mul (mem_centralizer_singleton_iff.mp hb.2).symm
  · rw [← intersection_eq_factor_center B C hB hinter hcomm]
    intro b hb
    exact ⟨hb.1, mem_centralizer_singleton_iff.mpr (hxC b hb.2)⟩

/-- A prescribed order-nine subgroup supplies independent cubic actions,
while retaining its identity and hence any additional normalizer conditions. -/
public theorem independent_cubics_of_nine_subgroup
    {G : Type*} [Group G] [Finite G] (B C A : Subgroup G)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (hcentral : centralizer ((B ⊔ C : Subgroup G) : Set G) ≤ B ⊔ C)
    (hA : Nat.card A = 9)
    (hle : A ≤ normalizer ((B ⊔ C : Subgroup G) : Set G)) :
    ∃ actors : QuaternionIndependentCubics B C, actors.A = A := by
  classical
  have hnorm := nine_subgroup_normalizes_quaternion_factors B C A hB hC hinter hcomm hA hle
  let f : A →* MulAut B := B.normalizerMonoidHom.comp (inclusion hnorm.1)
  let g : A →* MulAut C := C.normalizerMonoidHom.comp (inclusion hnorm.2)
  have hf (a : A) (b : B) : (f a b : G) = a * b * (a : G)⁻¹ := rfl
  have hg (a : A) (c : C) : (g a c : G) = a * c * (a : G)⁻¹ := rfl
  have hinj := faithful_quaternion_restrictions B C A hB hC hinter hcomm hcentral hA f g hf hg
  have hBaut : Nat.card (MulAut B) = 24 := by
    obtain ⟨eB⟩ := hB
    rw [Nat.card_congr (MulAut.congr eB).toEquiv, QuaternionGroup.card_mulAut_two]
  have hCaut : Nat.card (MulAut C) = 24 := by
    obtain ⟨eC⟩ := hC
    rw [Nat.card_congr (MulAut.congr eC).toEquiv, QuaternionGroup.card_mulAut_two]
  obtain ⟨hEA, x, y, hx, hy, hfx, hgx, hfy, hgy, hgen⟩ :=
    independent_cubics_of_faithful_pair hA hBaut hCaut f g hinj
  have hxC : (x : G) ∈ centralizer (C : Set G) := by
    intro c hc
    have h := hg x ⟨c, hc⟩
    rw [hgx] at h
    exact eq_mul_inv_iff_mul_eq.mp h
  have hyB : (y : G) ∈ centralizer (B : Set G) := by
    intro b hb
    have h := hf y ⟨b, hb⟩
    rw [hfy] at h
    exact eq_mul_inv_iff_mul_eq.mp h
  refine ⟨{
    A := A
    le_normalizer := hle
    card := hA
    elementary := hEA
    normalizes_left := hnorm.1
    normalizes_right := hnorm.2
    x := x
    y := y
    x_order := (orderOf_injective A.subtype A.subtype_injective x).trans hx
    y_order := (orderOf_injective A.subtype A.subtype_injective y).trans hy
    commute := congrArg Subtype.val (hEA.toIsMulCommutative.is_comm.comm x y)
    generated := ?_
    actionB := f
    actionC := g
    actionB_apply := hf
    actionC_apply := hg
    faithful := hinj
    x_actionB_ne_one := hfx
    x_actionC_eq_one := hgx
    y_actionB_eq_one := hfy
    y_actionC_ne_one := hgy
    x_centralizes := hxC
    y_centralizes := hyB
    fixed_left := quaternion_cubic_fixed_center B C A hB hinter hcomm f hf x
      ((orderOf_eq_prime_iff.mp hx).1) hfx hxC
    fixed_right := quaternion_cubic_fixed_center C B A hC (by simpa [inf_comm] using hinter)
      (fun c hc b hb => (hcomm b hb c hc).symm) g hg y
      ((orderOf_eq_prime_iff.mp hy).1) hgy hyB }, rfl⟩
  apply le_antisymm
  · exact sup_le (zpowers_le.mpr x.property) (zpowers_le.mpr y.property)
  · intro a ha
    obtain ⟨i, j, hij⟩ := hgen ⟨a, ha⟩
    have heq : a = (x : G) ^ i * (y : G) ^ j := congrArg Subtype.val hij
    rw [heq]
    exact (zpowers (x : G) ⊔ zpowers (y : G)).mul_mem
      (mem_sup_left (zpow_mem_zpowers _ _)) (mem_sup_right (zpow_mem_zpowers _ _))

/-- An elementary sixteen meeting a self-centralizing quaternion product in
order eight has a nonidentity fixed cubic element in the quotient of an
ambient group of order 1152. The order-nine subgroup is constructed here. -/
public theorem exists_fixed_cubic_of_quaternion_product_order_1152
    {G : Type*} [Group G] [Finite G]
    (Q : Subgroup G) [Q.Normal] (hG : Nat.card G = 1152)
    (hQ : Nat.card Q = 32) (hself : centralizer (Q : Set G) ≤ Q)
    (B C : Subgroup G) (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hjoin : B ⊔ C = Q) (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (V : Subgroup G) [IsElementaryAbelian 2 V]
    (hV : Nat.card V = 16) (hVQ : Nat.card (V ⊓ Q : Subgroup G) = 8) :
    ∃ r : G ⧸ Q, r ∈ centralizer (V.map (QuotientGroup.mk' Q) : Set (G ⧸ Q)) ∧
      r ≠ 1 ∧ r ^ 3 = 1 := by
  classical
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let P : Sylow 3 G := Classical.choice inferInstance
  let A : Subgroup G := P
  have hA : Nat.card A = 9 := by
    change Nat.card P = 9
    rw [P.card_eq_multiplicity, hG]
    decide +kernel
  obtain ⟨actors, _⟩ := independent_cubics_of_nine_subgroup B C A hB hC hinter hcomm
    (by rwa [hjoin]) hA (by rw [hjoin, Q.normalizer_eq_top]; exact le_top)
  exact actors.exists_fixed_cubic_of_order_1152 Q hG hQ hself B C hB hC
    hjoin hinter hcomm V hV hVQ

/-- Order-nine outer-action recognition for a normal self-centralizing
quaternion central product, with a Sylow two-subgroup of order 128 and index
nine. The elementary sixteen forces factor interchange and hence a nontrivial
fixed cubic element modulo the core. -/
public theorem exists_fixed_cubic_of_quaternion_core_sylow_index_nine
    {H : Type*} [Group H] [Finite H]
    (Q : Subgroup H) [Q.Normal] (hQ : Nat.card Q = 32)
    (hself : centralizer (Q : Set H) ≤ Q)
    (B C : Subgroup Q) (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hjoin : B ⊔ C = ⊤) (hinter : Nat.card (B ⊓ C : Subgroup Q) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (T : Sylow 2 H) (hT : Nat.card T = 128) (hindex : (T : Subgroup H).index = 9)
    (V : Subgroup H) [IsElementaryAbelian 2 V]
    (hV : Nat.card V = 16) (hVQ : Nat.card (V ⊓ Q : Subgroup H) = 8) :
    ∃ r : H ⧸ Q, r ∈ centralizer (V.map (QuotientGroup.mk' Q) : Set (H ⧸ Q)) ∧
      r ≠ 1 ∧ r ^ 3 = 1 := by
  have hH : Nat.card H = 1152 := by
    have h := (T : Subgroup H).card_mul_index
    rw [hT, hindex] at h
    exact h.symm
  let B' := B.map Q.subtype
  let C' := C.map Q.subtype
  have hB' : Nonempty (B' ≃* QuaternionGroup 2) :=
    ⟨(B.equivMapOfInjective Q.subtype Q.subtype_injective).symm.trans hB.some⟩
  have hC' : Nonempty (C' ≃* QuaternionGroup 2) :=
    ⟨(C.equivMapOfInjective Q.subtype Q.subtype_injective).symm.trans hC.some⟩
  have hjoin' : B' ⊔ C' = Q := by
    rw [← map_sup, hjoin]
    ext z
    exact ⟨fun ⟨w, _, hw⟩ => hw ▸ w.property, fun hz => ⟨⟨z, hz⟩, mem_top _, rfl⟩⟩
  have hinter' : Nat.card (B' ⊓ C' : Subgroup H) = 2 := by
    rw [← map_inf B C Q.subtype Q.subtype_injective, card_map_of_injective Q.subtype_injective, hinter]
  have hcomm' : ∀ b ∈ B', ∀ c ∈ C', b * c = c * b := by
    rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩
    exact congrArg Subtype.val (hcomm b hb c hc)
  exact exists_fixed_cubic_of_quaternion_product_order_1152 Q hH hQ hself
    B' C' hB' hC' hjoin' hinter' hcomm' V hV hVQ

end Subgroup
