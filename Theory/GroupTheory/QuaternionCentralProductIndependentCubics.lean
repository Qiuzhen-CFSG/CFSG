module

public import Theory.GroupTheory.QuaternionCentralProductAutomorphisms
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.Sylow

/-!
# Independent cubic actions on a quaternion central product

For two commuting quaternion factors with intersection of order two, a
self-centralizing join whose normalizer has order 576 admits independent
cubic actions on the two factors. A Sylow 3-subgroup has order nine. Its
elements are squares, so they preserve both intrinsic factors. Restriction
to the factors is faithful, and each image has order dividing both nine and
24. Thus restriction identifies the Sylow subgroup with the product of two
groups of order three.

This is the local quaternion-product argument used in Stellmacher (8.6)(a),
`refs/latex/stellmacher-n-group.tex`.
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

/-- Independent order-three conjugation actions on two actual quaternion factors.
The generators belong to an elementary abelian subgroup of order nine; the
restriction maps record their ambient conjugation action, not merely its order. -/
public structure QuaternionIndependentCubics
    {G : Type*} [Group G] (B C : Subgroup G) where
  A : Subgroup G
  le_normalizer : A ≤ normalizer ((B ⊔ C : Subgroup G) : Set G)
  card : Nat.card A = 9
  elementary : IsElementaryAbelian 3 A
  normalizes_left : A ≤ normalizer (B : Set G)
  normalizes_right : A ≤ normalizer (C : Set G)
  x : A
  y : A
  x_order : orderOf (x : G) = 3
  y_order : orderOf (y : G) = 3
  commute : Commute (x : G) (y : G)
  generated : zpowers (x : G) ⊔ zpowers (y : G) = A
  actionB : A →* MulAut B
  actionC : A →* MulAut C
  actionB_apply : ∀ a : A, ∀ b : B, (actionB a b : G) = a * b * (a : G)⁻¹
  actionC_apply : ∀ a : A, ∀ c : C, (actionC a c : G) = a * c * (a : G)⁻¹
  faithful : Function.Injective (actionB.prod actionC)
  x_actionB_ne_one : actionB x ≠ 1
  x_actionC_eq_one : actionC x = 1
  y_actionB_eq_one : actionB y = 1
  y_actionC_ne_one : actionC y ≠ 1
  x_centralizes : (x : G) ∈ centralizer (C : Set G)
  y_centralizes : (y : G) ∈ centralizer (B : Set G)
  fixed_left : B ⊓ centralizer {(x : G)} = (center B).map B.subtype
  fixed_right : C ⊓ centralizer {(y : G)} = (center C).map C.subtype

/-- A self-centralizing quaternion central product with normalizer of order 576
admits independent cubic actors on its two factors. -/
public theorem exists_independent_cubics_of_quaternion_central_product
    {G : Type*} [Group G] [Finite G] (B C : Subgroup G)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (hcentral : centralizer ((B ⊔ C : Subgroup G) : Set G) ≤ B ⊔ C)
    (hN : Nat.card (normalizer ((B ⊔ C : Subgroup G) : Set G)) = 576) :
    Nonempty (QuaternionIndependentCubics B C) := by
  classical
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let N := normalizer ((B ⊔ C : Subgroup G) : Set G)
  let P : Sylow 3 N := Classical.choice inferInstance
  let A : Subgroup G := (P : Subgroup N).map N.subtype
  have hA : Nat.card A = 9 := by
    rw [card_map_of_injective N.subtype_injective]
    rw [P.card_eq_multiplicity, hN]
    decide +kernel
  have hle : A ≤ N := by
    rintro a ⟨n, _, rfl⟩
    exact n.property
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
      ((orderOf_eq_prime_iff.mp hy).1) hgy hyB }⟩
  apply le_antisymm
  · exact sup_le (zpowers_le.mpr x.property) (zpowers_le.mpr y.property)
  · intro a ha
    obtain ⟨i, j, hij⟩ := hgen ⟨a, ha⟩
    have heq : a = (x : G) ^ i * (y : G) ^ j := congrArg Subtype.val hij
    rw [heq]
    exact (zpowers (x : G) ⊔ zpowers (y : G)).mul_mem
      (mem_sup_left (zpow_mem_zpowers _ _)) (mem_sup_right (zpow_mem_zpowers _ _))

end Subgroup
