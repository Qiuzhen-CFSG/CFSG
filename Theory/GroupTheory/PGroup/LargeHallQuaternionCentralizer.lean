module

public import Theory.GroupTheory.PGroup.BinaryHallNoNormalFour
public import Theory.GroupTheory.PGroup.LargeHallRotationAction
public import Theory.GroupTheory.PGroup.LargeHallRotationStructure
public import Theory.GroupTheory.PGroup.ExtraspecialCentralProductOrder

/-!
# Recognition of the quaternion centralizer

A quaternion subgroup supplementing the original cyclic rotations has a
centralizer of the same order as the original Hall factor. Its rotations
still have index two and order at least eight. Its center embeds in the
ambient center, which has exponent two by the original central product.

The recognition criterion excludes normal elementary four-groups directly:
such a group centralizes the squared rotations, and one of its elements lies
outside the cyclic rotation subgroup. Thus the squared rotations are central,
forcing every rotation to have fourth power one, a contradiction.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, printed p.392 (PDF page 8),
`refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf`.
-/

open Subgroup
open scoped commutatorElement

namespace IsPGroup

/-- A finite two-group with no normal elementary four-group is a binary Hall
factor.  This is the recognition step used for the quaternion centralizer. -/
public theorem isBinaryHallFactor_of_no_normal_four_for_quaternion_centralizer
    {C : Type*} [Group C] [Finite C]
    (hC : IsPGroup 2 C)
    (hno : ¬ ∃ E : Subgroup C, E.Normal ∧ IsElementaryAbelian 2 E ∧ Nat.card E = 4) :
    IsBinaryHallFactor C :=
  hC.isBinaryHallFactor_of_no_normal_four hno

/-- Recognition of the large centralizer once the central-product calculation
has supplied its cyclic index-two rotations and the exponent-two centre.
The hypotheses are intrinsic to the centralizer and are independent of the
choice of quaternion model. -/
public theorem isBinaryHallFactor_and_not_cyclic_of_cyclic_index_two
    {C : Type*} [Group C] [Finite C]
    (hC : IsPGroup 2 C)
    (R : Subgroup C) [IsCyclic R]
    (_hidx : R.index = 2) (_hR : 8 ≤ Nat.card R)
    (_hZ : ∀ z ∈ center C, z ^ 2 = (1 : C))
    (hno : ¬ ∃ E : Subgroup C, E.Normal ∧ IsElementaryAbelian 2 E ∧ Nat.card E = 4)
    (hnc : ¬ IsCyclic C) (hlarge : 16 ≤ Nat.card C) :
    IsBinaryHallFactor C ∧ ¬ IsCyclic C ∧ 16 ≤ Nat.card C := by
  exact ⟨hC.isBinaryHallFactor_of_no_normal_four_for_quaternion_centralizer hno,
    hnc, hlarge⟩

/-- A large cyclic subgroup of index two and an exponent-two center force a
finite two-group to be a binary Hall factor. A normal elementary four-group
would centralize all squared rotations, making every rotation have fourth
power one. -/
public theorem isBinaryHallFactor_of_large_cyclic_index_two
    {G : Type*} [Group G] [Finite G] (hG : IsPGroup 2 G)
    (R : Subgroup G) [IsCyclic R] (hi : R.index = 2) (hR : 8 ≤ Nat.card R)
    (hZ : ∀ z ∈ center G, z ^ 2 = (1 : G)) :
    IsBinaryHallFactor G := by
  apply hG.isBinaryHallFactor_of_no_normal_four
  rintro ⟨U, hUn, hUe, hU⟩
  let : U.Normal := hUn
  let : IsElementaryAbelian 2 U := hUe
  let : R.Normal := normal_of_index_eq_two hi
  have hnot : ¬ U ≤ R := by
    intro h
    let : IsCyclic U := isCyclic_of_le h
    have hh : Nat.card U ∣ 2 := by
      rw [← IsCyclic.exponent_eq_card]
      exact IsElementaryAbelian.exponent_dvd_p 2 U
    norm_num [hU] at hh
  obtain ⟨e, heU, heR⟩ := SetLike.not_le_iff_exists.mp hnot
  have hpow (r : R) : r ^ 4 = 1 := by
    have hc : ⁅e, (r : G)⁆ ∈ U ⊓ R := commutator_le_inf U R
      (commutator_mem_commutator heU r.property)
    have hc2 : ⁅e, (r : G)⁆ ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian _ hc.1
    have hcr : Commute ⁅e, (r : G)⁆ (r : G) :=
      (R.le_centralizer hc.2 r r.property).symm
    have heq : e * (r : G) ^ 2 * e⁻¹ = (r : G) ^ 2 := by
      change MulAut.conj e ((r : G) ^ 2) = _
      rw [map_pow, conj_eq_commutatorElement_mul, hcr.mul_pow, hc2, one_mul]
    have hz := central_of_commute_outside_cyclic_index_two R hi heR
      (R.pow_mem r.property 2) (show Commute ((r : G) ^ 2) e from
        (mul_inv_eq_iff_eq_mul.mp heq).symm)
    apply Subtype.ext
    simpa only [coe_pow, coe_one, ← pow_mul] using hZ _ hz
  have hcard : Nat.card R ∣ 4 := by
    rw [← IsCyclic.exponent_eq_card]
    exact Monoid.exponent_dvd_of_forall_pow_eq_one hpow
  have := Nat.le_of_dvd (by decide : 0 < 4) hcard
  omega



end IsPGroup

namespace Subgroup

private theorem factor_center_in_ambient {G : Type*} [Group G]
    (A D : Subgroup G) (hc : D ≤ centralizer (A : Set G)) (hg : A ⊔ D = ⊤)
    (z : A) (hz : z ∈ center A) : (z : G) ∈ center G := by
  have ht : (⊤ : Subgroup G) ≤ centralizer ({(z : G)} : Set G) := by
    rw [← hg]
    apply sup_le
    · intro a ha
      exact mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_center_iff.mp hz (⟨a, ha⟩ : A)))
    · intro d hd
      exact mem_centralizer_singleton_iff.mpr (hc hd z z.property).symm
  exact mem_center_iff.mpr (fun g => mem_centralizer_singleton_iff.mp (ht (mem_top g)))

/-- Replacing the extraspecial factor by a characteristic quaternion supplement
to the same rotations preserves the large Hall centralizer. -/
public theorem isBinaryHallFactor_centralizer_of_large_hall_quaternion
    {P : Type*} [Group P] [Finite P] [IsCyclic (center P)]
    (hP : IsPGroup 2 P) (B D : Subgroup P) [B.Normal] [D.Normal]
    [IsExtraspecial 2 B] (hB : Nat.card B = 8)
    (hD : IsBinaryHallFactor D) (hnc : ¬ IsCyclic D) (hlarge : 16 ≤ Nat.card D)
    (hc : D ≤ centralizer (B : Set P)) (hg : B ⊔ D = ⊤)
    (R Q : Subgroup P) [R.Normal] [IsCyclic R] (hR : 8 ≤ Nat.card R)
    (hRD : R ≤ D) (hRi : R.relIndex D = 2) [Q.Characteristic]
    (eQ : Q ≃* QuaternionGroup 2) (hQR : Q ⊔ R = B ⊔ R)
    (hQC : Q ⊔ centralizer (Q : Set P) = ⊤) :
    IsBinaryHallFactor (centralizer (Q : Set P)) ∧
      ¬ IsCyclic (centralizer (Q : Set P)) ∧
      16 ≤ Nat.card (centralizer (Q : Set P)) := by
  let C := centralizer (Q : Set P)
  have hMR : B ⊔ R ≤ centralizer (R : Set P) :=
    sup_le (le_centralizer_iff.mp (hRD.trans hc)) R.le_centralizer
  have hRC : R ≤ C := le_centralizer_iff.mp
    (le_sup_left.trans (hQR.le.trans hMR))
  have hQcard : Nat.card Q = 8 := by
    rw [Nat.card_congr eQ.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hQZ : Nat.card (center Q) = 2 := by
    rw [Nat.card_congr (centerCongr eQ).toEquiv]
    let predicate : QuaternionGroup 2 → Prop := fun x => ∀ y, y * x = x * y
    have ht : Fintype.card {x // predicate x} = 2 := by decide
    rw [Nat.card_congr (Equiv.subtypeEquivRight (fun _ => mem_center_iff)),
      Nat.card_eq_fintype_card]
    exact ht
  have hQI : Q ⊓ C = (center Q).map Q.subtype := by
    ext x
    constructor
    · rintro ⟨hx, hc⟩
      exact ⟨⟨x, hx⟩, mem_center_iff.mpr
        (fun q => Subtype.ext (hc q q.property)), rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.property, fun q hq =>
        congrArg Subtype.val (mem_center_iff.mp hx (⟨q, hq⟩ : Q))⟩
  have hQinf : Nat.card (Q ⊓ C : Subgroup P) = 2 := by
    rw [hQI, card_map_of_injective Q.subtype_injective]
    exact hQZ
  have hcountQ := card_mul_eq_card_inf_mul_card_sup_of_normalizes Q C
    (centralizer_le_normalizer _)
  rw [hQcard, hQinf, hQC, Nat.card_congr Subgroup.topEquiv.toEquiv] at hcountQ
  have hDne : D ≠ ⊥ := by intro h; simp [h] at hlarge
  have hcountB := card_mul_two_eq_of_extraspecial_of_cyclic_center hP B D hDne hc hg
  rw [hB] at hcountB
  have hCcard : Nat.card C = Nat.card D := by omega
  have hClarge : 16 ≤ Nat.card C := hCcard.symm ▸ hlarge
  let RC := R.subgroupOf C
  let eRC : RC ≃* R := subgroupOfEquivOfLe hRC
  let : IsCyclic RC := eRC.isCyclic.mpr inferInstance
  have hRCcard : Nat.card RC = Nat.card R := Nat.card_congr eRC.toEquiv
  have hRCi : RC.index = 2 := by
    have h1 := (R.subgroupOf D).index_mul_card
    have h2 := RC.index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hRD).toEquiv] at h1
    rw [hRCcard, hCcard] at h2
    change R.relIndex D * Nat.card R = Nat.card D at h1
    rw [hRi] at h1
    have hp : 0 < Nat.card R := Nat.card_pos
    nlinarith
  obtain ⟨_, _, _, _, _, hZD⟩ := hD.exists_characteristic_cyclic_index_two hnc hlarge
  have hBD : B ⊓ D = (center B).map B.subtype := by
    apply eq_of_le_of_card_ge
    · rintro b ⟨hb, hd⟩
      exact ⟨⟨b, hb⟩, mem_center_iff.mpr
        (fun x => Subtype.ext (hc hd x x.property)), rfl⟩
    · rw [card_map_of_injective B.subtype_injective,
        IsExtraspecial.center_order_p 2 B,
        card_inf_eq_two_of_extraspecial_of_cyclic_center hP B D hDne hc]
  have hZP (z : P) (hz : z ∈ center P) : z ^ 2 = 1 := by
    obtain ⟨b, hb, d, hd, hbd⟩ := mem_sup_of_normal_right.mp
      (show z ∈ B ⊔ D from hg.symm ▸ mem_top z)
    have hbZ : (⟨b, hb⟩ : B) ∈ center B := by
      apply mem_center_iff.mpr
      intro x
      apply Subtype.ext
      apply mul_right_cancel (b := d)
      calc
        (x : P) * b * d = x * (b * d) := mul_assoc _ _ _
        _ = x * z := by rw [hbd]
        _ = z * x := mem_center_iff.mp hz x
        _ = b * x * d := by rw [← hbd, mul_assoc, ← hc hd x x.property, ← mul_assoc]
    have hbD : b ∈ D := (hBD.symm ▸ mem_map_of_mem B.subtype hbZ : b ∈ B ⊓ D).2
    have hzD : z ∈ D := hbd ▸ D.mul_mem hbD hd
    have hzZD : (⟨z, hzD⟩ : D) ∈ center D := mem_center_iff.mpr
      (fun x => Subtype.ext (mem_center_iff.mp hz x))
    exact congrArg Subtype.val (hZD _ hzZD)
  have hZC (z : C) (hz : z ∈ center C) : z ^ 2 = 1 := by
    apply Subtype.ext
    exact hZP z (factor_center_in_ambient C Q (le_centralizer_iff.mp le_rfl)
      (sup_comm Q C ▸ hQC) z hz)
  have hCnc : ¬ IsCyclic C := by
    intro hh
    let : IsCyclic C := hh
    have hdiv : Nat.card C ∣ 2 := by
      rw [← IsCyclic.exponent_eq_card]
      apply Monoid.exponent_dvd_of_forall_pow_eq_one
      intro x
      exact hZC x (by rw [center_eq_top]; trivial)
    have := Nat.le_of_dvd (by decide : 0 < 2) hdiv
    omega
  exact ⟨(hP.to_subgroup C).isBinaryHallFactor_of_large_cyclic_index_two RC hRCi (hRCcard.symm ▸ hR) hZC,
    hCnc, hClarge⟩


end Subgroup
