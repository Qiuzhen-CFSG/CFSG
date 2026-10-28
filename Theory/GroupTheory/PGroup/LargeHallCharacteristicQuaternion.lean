module
public import Theory.GroupTheory.PGroup.LargeHallRotationStructure
public import Theory.GroupTheory.PGroup.ExtraspecialCyclicQuaternion
public import Theory.ElementaryAbelian.ExtraspecialEquiv
public import Theory.GroupTheory.IndexTwoCoprimeAutomorphism

/-!
# A characteristic quaternion subgroup detecting an order-three automorphism

Let a finite two-group with cyclic center be the commuting product of an
extraspecial subgroup of order eight and a noncyclic binary Hall factor of
order at least sixteen. There are normal cyclic rotations of index two in
the Hall factor and a characteristic quaternion-eight subgroup supplementing
those rotations in the extraspecial rotation product. Every automorphism of
order three moves an element of this quaternion subgroup; neither original
factor is assumed invariant under that automorphism.

The rotations come from the Hall models. Fourth powers make their product
with the extraspecial factor characteristic. The central-product intersection
identifies the center of this product with the rotations, so the characteristic
quaternion supplement theorem applies internally. Characteristicity then
passes to the ambient group. A cube-one automorphism fixing the quaternion
subgroup also fixes the cyclic center, hence the whole product. Its index is
two, so the coprime index-two restriction lemma forces the automorphism to be
the identity, contradicting its order.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, printed p.392, Case 1;
`refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf`.
-/

open Subgroup

namespace Subgroup

private theorem center_rotation_product
    {P : Type*} [Group P] (B R : Subgroup P) [R.Normal] [IsCyclic R]
    (hc : R ≤ centralizer (B : Set P))
    (hZ : (center B).map B.subtype ≤ R) :
    center (B ⊔ R : Subgroup P) = R.subgroupOf (B ⊔ R) := by
  let M := B ⊔ R
  apply le_antisymm
  · intro x hx
    obtain ⟨b, hb, r, hr, he⟩ := mem_sup_of_normal_right.mp x.property
    have hbZ : (⟨b, hb⟩ : B) ∈ center B := by
      apply mem_center_iff.mpr
      intro y
      apply Subtype.ext
      apply mul_right_cancel (b := r)
      calc
        (y : P) * b * r = y * (b * r) := mul_assoc _ _ _
        _ = y * (x : P) := by rw [he]
        _ = (x : P) * y := congrArg Subtype.val
          (mem_center_iff.mp hx (⟨y, mem_sup_left y.property⟩ : M))
        _ = b * y * r := by rw [← he, mul_assoc, ← hc hr y y.property, ← mul_assoc]
    change (x : P) ∈ R
    rw [← he]
    exact R.mul_mem (hZ (mem_map_of_mem B.subtype hbZ)) hr
  · intro x hx
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    obtain ⟨b, hb, r, hr, he⟩ := mem_sup_of_normal_right.mp y.property
    change (y : P) * x = x * y
    rw [← he]
    have hrx : r * (x : P) = x * r := R.le_centralizer hx r hr
    have hbx : b * (x : P) = x * b := hc hx b hb
    rw [mul_assoc, hrx, ← mul_assoc, hbx, mul_assoc]

/-- A characteristic quaternion subgroup detects every automorphism of order three
in a central product with a large noncyclic binary Hall factor. -/
public theorem exists_characteristic_quaternion_detecting_order_three_of_large_hall
    {P : Type*} [Group P] [Finite P] [IsCyclic (center P)]
    (hP : IsPGroup 2 P) (B D : Subgroup P) [B.Normal] [D.Normal]
    [IsExtraspecial 2 B] (hB : Nat.card B = 8)
    (hD : IsBinaryHallFactor D) (hnc : ¬ IsCyclic D) (hlarge : 16 ≤ Nat.card D)
    (hc : D ≤ centralizer (B : Set P)) (hg : B ⊔ D = ⊤)
    (a : MulAut P) (ha : orderOf a = 3) :
    ∃ R Q : Subgroup P, R.Normal ∧ IsCyclic R ∧ 8 ≤ Nat.card R ∧ R ≤ D ∧
      R.relIndex D = 2 ∧ Q.Characteristic ∧ Nonempty (Q ≃* QuaternionGroup 2) ∧
      Q ⊔ R = B ⊔ R ∧ ∃ q ∈ Q, a q ≠ q := by
  obtain ⟨T, hTc, hTcyc, hTi, hTcard, hout, _⟩ :=
    hD.exists_characteristic_large_rotation_index_two (hP.to_subgroup D) hnc hlarge
  let : T.Characteristic := hTc
  let : IsCyclic T := hTcyc
  let R := T.map D.subtype
  let eR : T ≃* R := T.equivMapOfInjective D.subtype D.subtype_injective
  let : IsCyclic R := eR.isCyclic.mp inferInstance
  have hRD : R ≤ D := map_subtype_le T
  have hRcard : Nat.card R = Nat.card T := (Nat.card_congr eR.toEquiv).symm
  have hRlarge : 8 ≤ Nat.card R := hRcard ▸ hTcard
  have hRi : R.relIndex D = 2 := by
    change (T.map D.subtype).relIndex D = 2
    have hh := relIndex_map_map_of_injective T ⊤ D.subtype_injective
    simpa only [← MonoidHom.range_eq_map, D.range_subtype, relIndex_top_right, hTi] using hh
  have houtR : ∀ d ∈ D, d ∉ R → d ^ 4 = (1 : P) := by
    intro d hd hn
    exact congrArg Subtype.val (hout ⟨d, hd⟩ (fun hh => hn ⟨⟨d, hd⟩, hh, rfl⟩))
  let M := B ⊔ R
  let : M.Characteristic := characteristic_sup_of_fourth_power_rotation B D R
    (fun b hb => congrArg Subtype.val (IsExtraspecial.pow_four_eq_one (⟨b, hb⟩ : B)))
    hc hg hRD hRlarge houtR
  have hRc : R ≤ centralizer (B : Set P) := hRD.trans hc
  have hRne : R ≠ ⊥ := by intro h; simp [h] at hRlarge
  have hi : Nat.card (B ⊓ R : Subgroup P) = 2 :=
    card_inf_eq_two_of_extraspecial_of_cyclic_center hP B R hRne hRc
  have hBR : B ⊓ R = (center B).map B.subtype := by
    apply eq_of_le_of_card_ge
    · rintro x ⟨hb, hr⟩
      exact ⟨⟨x, hb⟩, mem_center_iff.mpr
        (fun b => Subtype.ext (hRc hr b b.property)), rfl⟩
    · rw [card_map_of_injective B.subtype_injective, IsExtraspecial.center_order_p 2 B, hi]
  have hZM : center M = R.subgroupOf M :=
    center_rotation_product B R hRc (hBR ▸ inf_le_right)
  let BM := B.subgroupOf M
  let RM := R.subgroupOf M
  let eB : BM ≃* B := subgroupOfEquivOfLe (show B ≤ M from le_sup_left)
  let eRM : RM ≃* R := subgroupOfEquivOfLe (show R ≤ M from le_sup_right)
  let : IsExtraspecial 2 BM := IsExtraspecial.of_mulEquiv eB.symm inferInstance
  let : IsCyclic RM := eRM.isCyclic.mpr inferInstance
  let : IsCyclic (center M) := hZM ▸ (inferInstance : IsCyclic RM)
  have hBM : Nat.card BM = 8 := (Nat.card_congr eB.toEquiv).trans hB
  have hRM : 8 ≤ Nat.card RM := by rw [Nat.card_congr eRM.toEquiv]; exact hRlarge
  have hcomm : RM ≤ centralizer (BM : Set M) := by
    intro r hr b hb
    exact Subtype.ext (hRc hr b hb)
  have hsup : BM ⊔ RM = ⊤ := (codisjoint_subgroupOf_sup B R).eq_top
  obtain ⟨Q₀, hQ₀c, ⟨eQ₀⟩, hQ₀sup⟩ :=
    exists_characteristic_quaternion_of_extraspecial_cyclic_product
      (hP.to_subgroup M) BM RM hBM hRM hcomm hsup
  let : Q₀.Characteristic := hQ₀c
  let Q := Q₀.map M.subtype
  let eQ : Q₀ ≃* Q := Q₀.equivMapOfInjective M.subtype M.subtype_injective
  have hQsup : Q ⊔ R = M := by
    have hh := congrArg (fun U : Subgroup M => U.map M.subtype) hQ₀sup
    simpa only [RM, map_sup, map_subgroupOf_eq_of_le (show R ≤ M from le_sup_right),
      ← MonoidHom.range_eq_map, M.range_subtype] using hh
  have hMi : M.index = 2 := by
    have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes B R
      (hRc.trans (centralizer_le_normalizer _))
    rw [hB, hi] at hprod
    have hDne : D ≠ ⊥ := by intro h; simp [h] at hlarge
    have hPcard := card_mul_two_eq_of_extraspecial_of_cyclic_center hP B D hDne hc hg
    rw [hB] at hPcard
    have hTcount := T.index_mul_card
    rw [hTi, ← hRcard] at hTcount
    have hMcount := M.index_mul_card
    have hMpos : 0 < Nat.card M := Nat.card_pos
    change 8 * Nat.card R = 2 * Nat.card M at hprod
    nlinarith
  refine ⟨R, Q, inferInstance, inferInstance, hRlarge, hRD, hRi,
    inferInstance, ⟨eQ.symm.trans eQ₀⟩, hQsup, ?_⟩
  by_contra hnot
  push Not at hnot
  have ha3 : a ^ 3 = 1 := ha ▸ pow_orderOf_eq_one a
  let aM := MulAut.characteristic M a
  let aZ := MulAut.characteristic (center M) aM
  have haM3 : aM ^ 3 = 1 := by
    change (MulAut.characteristic M a) ^ 3 = 1
    rw [← map_pow, ha3, map_one]
  have haZ3 : aZ ^ 3 = 1 := by
    change (MulAut.characteristic (center M) aM) ^ 3 = 1
    rw [← map_pow, haM3, map_one]
  have haZone : aZ = 1 := by
    have hpZ := ((hP.to_subgroup M).to_subgroup (center M)).mulAut_of_isCyclic_two
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
      (hpZ.orderOf_coprime (n := 3) (by decide) aZ)
      (dvd_refl _) (orderOf_dvd_of_pow_eq_one haZ3))
  have hfixedR : ∀ r ∈ R, a r = r := by
    intro r hr
    let rM : M := ⟨r, mem_sup_right hr⟩
    have hrZ : rM ∈ center M := hZM.symm ▸ hr
    have hh := DFunLike.congr_fun haZone (⟨rM, hrZ⟩ : center M)
    exact congrArg (fun z : center M => ((z : M) : P)) hh
  have hfixedM : ∀ x ∈ M, a x = x := by
    intro x hx
    rw [← hQsup] at hx
    obtain ⟨q, hq, r, hr, rfl⟩ := mem_sup_of_normal_right.mp hx
    rw [map_mul, hnot q hq, hfixedR r hr]
  have haone := eq_one_of_cube_eq_one_of_fixed_index_two M hMi
    (hP.to_subgroup M) a ha3 hfixedM
  rw [haone, orderOf_one] at ha
  norm_num at ha

end Subgroup
