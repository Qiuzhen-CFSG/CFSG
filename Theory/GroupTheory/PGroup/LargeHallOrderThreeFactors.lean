module

public import Theory.GroupTheory.PGroup.BinaryHallFactorAutomorphisms
public import Theory.GroupTheory.PGroup.LargeHallCharacteristicQuaternion
public import Theory.GroupTheory.PGroup.LargeHallQuaternionCentralizer
public import Theory.GroupTheory.SpecificGroups.QuaternionEightCubicNormalizer

/-!
# Fixed Hall factors for cubic automorphisms

A characteristic quaternion-eight subgroup and its large Hall centralizer
form factors adapted to every automorphism of order three, provided they
generate the ambient group. The Hall centralizer has a two-group of
automorphisms, so the cubic action fixes it pointwise. The action on the
quaternion factor is then nontrivial and fixes only its center. Factoring
an arbitrary fixed element proves the exact fixed-subgroup identity.

The supplement criterion uses the conjugation image on the quaternion group:
a two-subgroup normalized by a nontrivial cubic automorphism consists of
inner automorphisms. Removing an inner representative from each ambient
element leaves an element of the centralizer.

The characteristic rotation product supplies the quaternion subgroup, and
the cyclic index-two recognition criterion identifies its centralizer as a
large Hall factor. Together these give an intrinsic factor choice without
requiring either supplied factor to be invariant.

This proves the factor choice of Janko–Thompson,
Math. Z. 113 (1970), §4, printed p.392 (PDF page 8).
-/

namespace Subgroup

/-- A cube-one automorphism fixes a characteristic large binary Hall factor
pointwise. -/
public theorem fixed_of_characteristic_large_hall_of_cube_eq_one
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (D : Subgroup P) [D.Characteristic]
    (hD : IsBinaryHallFactor D) (hlarge : 16 ≤ Nat.card D)
    (a : MulAut P) (ha : a ^ 3 = 1) :
    ∀ x ∈ D, a x = x := by
  let b := MulAut.characteristic D a
  have hb3 : b ^ 3 = 1 := by
    change (MulAut.characteristic D a) ^ 3 = 1
    rw [← map_pow, ha, map_one]
  have hcop := (hD.isPGroup_mulAut_of_sixteen_le (hP.to_subgroup D) hlarge).orderOf_coprime
    (by decide : Nat.Coprime 2 3) b
  have hb : b = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes hcop (dvd_refl _) (orderOf_dvd_of_pow_eq_one hb3))
  intro x hx
  exact congrArg Subtype.val (DFunLike.congr_fun hb (⟨x, hx⟩ : D))

/-- When a characteristic quaternion subgroup and its large Hall centralizer
generate a two-group, the centralizer is exactly the fixed subgroup of every
order-three automorphism. -/
public theorem mem_centralizer_iff_fixed_of_characteristic_quaternion_hall
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (Q : Subgroup P) [Q.Characteristic]
    (hQ : Nonempty (Q ≃* QuaternionGroup 2))
    (hD : IsBinaryHallFactor (centralizer (Q : Set P)))
    (hlarge : 16 ≤ Nat.card (centralizer (Q : Set P)))
    (hgen : Q ⊔ centralizer (Q : Set P) = ⊤)
    (a : MulAut P) (ha : orderOf a = 3) :
    ∀ x : P, x ∈ centralizer (Q : Set P) ↔ a x = x := by
  let D := centralizer (Q : Set P)
  have ha3 : a ^ 3 = 1 := ha ▸ pow_orderOf_eq_one a
  have hfix := fixed_of_characteristic_large_hall_of_cube_eq_one hP D hD hlarge a ha3
  let b := MulAut.characteristic Q a
  have hb3 : b ^ 3 = 1 := by
    change (MulAut.characteristic Q a) ^ 3 = 1
    rw [← map_pow, ha3, map_one]
  have hbne : b ≠ 1 := by
    intro hb
    have ha1 : a = 1 := by
      ext x
      obtain ⟨q, hq, d, hd, rfl⟩ := mem_sup_of_normal_right.mp
        (show x ∈ Q ⊔ D from hgen.symm ▸ mem_top x)
      have hqfix : a q = q :=
        congrArg Subtype.val (DFunLike.congr_fun hb (⟨q, hq⟩ : Q))
      change a (q * d) = q * d
      rw [map_mul, hqfix, hfix d hd]
    simp [ha1] at ha
  obtain ⟨eQ⟩ := hQ
  intro x
  constructor
  · exact hfix x
  · intro hx
    obtain ⟨q, hq, d, hd, rfl⟩ := mem_sup_of_normal_right.mp
      (show x ∈ Q ⊔ D from hgen.symm ▸ mem_top x)
    have hqfix : a q = q := by
      rw [map_mul, hfix d hd] at hx
      exact mul_right_cancel hx
    have hqZ : (⟨q, hq⟩ : Q) ∈ center Q :=
      QuaternionGroup.fixed_mem_center_of_cube_eq_one_ne_one_of_equiv eQ b hb3 hbne
        (Subtype.ext hqfix)
    have hqD : q ∈ D := by
      intro y hy
      exact congrArg Subtype.val (mem_center_iff.mp hqZ (⟨y, hy⟩ : Q))
    exact D.mul_mem hqD hd

/-- A characteristic quaternion subgroup with a nontrivial cubic action
supplements its centralizer in an ambient two-group. The ambient conjugation
image is a two-subgroup normalized by the cubic action and is therefore inner. -/
public theorem sup_centralizer_eq_top_of_characteristic_quaternion_cubic
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (Q : Subgroup P) [Q.Characteristic] (eQ : Q ≃* QuaternionGroup 2)
    (a : MulAut P) (ha : a ^ 3 = 1) (hne : MulAut.characteristic Q a ≠ 1) :
    Q ⊔ centralizer (Q : Set P) = ⊤ := by
  let f : P →* MulAut Q := MulAut.conjNormal
  let b := MulAut.characteristic Q a
  have hb3 : b ^ 3 = 1 := by
    change (MulAut.characteristic Q a) ^ 3 = 1
    rw [← map_pow, ha, map_one]
  have hconj (c : MulAut P) (g : P) :
      MulAut.characteristic Q c * f g * (MulAut.characteristic Q c)⁻¹ = f (c g) := by
    ext q
    change c (g * c.symm q * g⁻¹) = c g * q * (c g)⁻¹
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
  have hnorm : b ∈ normalizer (f.range : Set (MulAut Q)) := by
    apply mem_normalizer_iff.mpr
    intro t
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨a g, (hconj a g).symm⟩
    · rintro ⟨g, hg⟩
      refine ⟨a.symm g, ?_⟩
      have hh := hconj a.symm g
      have he : MulAut.characteristic Q a.symm = b⁻¹ := by
        change MulAut.characteristic Q a⁻¹ = (MulAut.characteristic Q a)⁻¹
        exact map_inv _ _
      rw [he, hg] at hh
      simpa only [inv_inv, inv_mul_cancel_left, mul_inv_cancel_right, mul_assoc, inv_mul_cancel, mul_one] using hh.symm
  have hinner := QuaternionGroup.le_inner_of_isPGroup_two_of_normalized_by_cubic_of_equiv
    eQ f.range (hP.of_surjective f.rangeRestrict f.rangeRestrict_surjective)
    b hb3 hne hnorm
  apply top_unique
  intro g _
  obtain ⟨q, hq⟩ := hinner (show f g ∈ f.range from ⟨g, rfl⟩)
  have hc : (q : P)⁻¹ * g ∈ centralizer (Q : Set P) := by
    intro x hx
    have hh := congrArg Subtype.val (DFunLike.congr_fun hq (⟨x, hx⟩ : Q))
    change (q : P) * x * (q : P)⁻¹ = g * x * g⁻¹ at hh
    have hh' := congrArg (fun y : P => (q : P)⁻¹ * y * g) hh
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hh'
  have hm := (Q ⊔ centralizer (Q : Set P)).mul_mem
    (mem_sup_left q.property) (mem_sup_right hc)
  simpa only [mul_inv_cancel_left] using hm

/-- Intrinsic factors adapted to an automorphism of order three. The new
quaternion factor is characteristic, and its large Hall centralizer is exactly
the fixed subgroup; the original factors need not be invariant. -/
public theorem exists_quaternion_large_hall_factors_fixed_by_order_three
    {P : Type*} [Group P] [Finite P] [IsCyclic (center P)]
    (hP : IsPGroup 2 P) (B D : Subgroup P) [B.Normal] [D.Normal]
    [IsExtraspecial 2 B] (hB : Nat.card B = 8)
    (hD : IsBinaryHallFactor D) (hnc : ¬ IsCyclic D) (hlarge : 16 ≤ Nat.card D)
    (hc : D ≤ centralizer (B : Set P)) (hg : B ⊔ D = ⊤)
    (a : MulAut P) (ha : orderOf a = 3) :
    ∃ B₀ D₀ : Subgroup P, B₀.Normal ∧ D₀.Normal ∧
      Nonempty (B₀ ≃* QuaternionGroup 2) ∧ IsBinaryHallFactor D₀ ∧
      ¬ IsCyclic D₀ ∧ 16 ≤ Nat.card D₀ ∧
      D₀ ≤ centralizer (B₀ : Set P) ∧ B₀ ⊔ D₀ = ⊤ ∧
      ∀ x : P, x ∈ D₀ ↔ a x = x := by
  obtain ⟨R, Q, hRn, hRc, hR, hRD, hRi, hQchar, ⟨eQ⟩, hQR, q, hq, hqa⟩ :=
    exists_characteristic_quaternion_detecting_order_three_of_large_hall
      hP B D hB hD hnc hlarge hc hg a ha
  let : R.Normal := hRn
  let : IsCyclic R := hRc
  let : Q.Characteristic := hQchar
  have ha3 : a ^ 3 = 1 := ha ▸ pow_orderOf_eq_one a
  have hne : MulAut.characteristic Q a ≠ 1 := by
    intro h
    exact hqa (congrArg Subtype.val (DFunLike.congr_fun h (⟨q, hq⟩ : Q)))
  have hgen := sup_centralizer_eq_top_of_characteristic_quaternion_cubic hP Q eQ a ha3 hne
  obtain ⟨hHall, hnoncyclic, hcard⟩ := isBinaryHallFactor_centralizer_of_large_hall_quaternion hP B D hB hD hnc hlarge hc hg
    R Q hR hRD hRi eQ hQR hgen
  refine ⟨Q, centralizer (Q : Set P), inferInstance, inferInstance, ⟨eQ⟩,
    hHall, hnoncyclic, hcard, le_rfl, hgen, ?_⟩
  exact mem_centralizer_iff_fixed_of_characteristic_quaternion_hall
    hP Q ⟨eQ⟩ hHall hcard hgen a ha

end Subgroup
