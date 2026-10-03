module

public import Theory.GroupTheory.PGroup.CyclicCenterIndexFourElementary
public import Theory.GroupTheory.PGroup.MaximalElementaryCentralizer
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
/-!
# Elementary fours in a quaternion–cyclic core

Let a subgroup of index two be the central product of a quaternion group of
order eight and its cyclic center. Every elementary four in the core is
normal in the core: its centralizer has index at most two and its first omega
subgroup is the four. Hence the intersection with a crossing elementary eight
is normal in the full group, and equals its unique normal elementary four.

An outside element acting innerly on the quaternion factor would preserve
every elementary four in the core. A noncentral involution in one four has
quaternion–central coordinates; replacing its quaternion coordinate by a
noncommuting axis with the same square constructs a distinct four. Both fours
would then be normal in the full group, contradicting uniqueness.

Source: Janko–Thompson (1970), §4, Case 2, printed p.393 (PDF page 9),
`refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf`.
The argument proves the needed elementary rank bound from the cyclic center
of index four. It needs neither an ambient rank assumption nor the prohibition
on normal elementary eights. The existence of the crossing elementary eight
also makes a separate lower bound on the cyclic factor unnecessary.
-/

open Subgroup
open scoped IsMulCommutative

namespace Subgroup

private theorem elementary_four_normal_of_cyclic_center_index_four {H : Type*} [Group H] [Finite H] [IsCyclic (center H)]
    (hn : ¬ IsMulCommutative H) (hi : (center H).index = 4)
    (E : Subgroup H) [IsElementaryAbelian 2 E] (hE : Nat.card E = 4) : E.Normal := by
  let D := centralizer (E : Set H)
  have hED : E ≤ D := E.le_centralizer
  have hZD : center H ≤ D := center_le_centralizer _
  have hEnZ : ¬ E ≤ center H := by
    intro h
    let : IsCyclic E := isCyclic_of_le h
    have hh := IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq
      (A := E) (p := 2) (by simpa using hE)
    exact hh inferInstance
  have hrel : 2 ≤ (center H).relIndex D := by
    have hp := (center H).subgroupOf D |>.index_ne_zero_of_finite
    change (center H).relIndex D ≠ 0 at hp
    have hne : (center H).relIndex D ≠ 1 := fun h => hEnZ (hED.trans (relIndex_eq_one.mp h))
    omega
  have hmul := relIndex_mul_index hZD
  rw [hi] at hmul
  have hidx : D.index = 1 ∨ D.index = 2 := by
    have hp := D.index_ne_zero_of_finite
    have : D.index ≤ 2 := by nlinarith
    omega
  let : D.Normal := hidx.elim D.normal_of_index_eq_one D.normal_of_index_eq_two
  let : (omega₁ D (p := 2)).Characteristic := omega₁_characteristic _
  have heq : (omega₁ D (p := 2)).map D.subtype = E :=
    omega_one_centralizer_map_eq_of_elementary_card_le E (by
      intro A hA
      let := hA
      simpa only [hE] using card_elementary_le_four_of_cyclic_center_index_four hn hi A)
  rw [← heq]
  exact ConjAct.normal_of_characteristic_of_normal


private theorem quaternion_cyclic_center_data {P : Type*} [Group P] [Finite P]
    (R Q C : Subgroup P) [Q.Normal] [C.Normal] [IsCyclic C]
    (e : Q ≃* QuaternionGroup 2) (hgen : Q ⊔ C = R)
    (hcap : Nat.card (Q ⊓ C : Subgroup P) = 2)
    (hC : C = (center R).map R.subtype) :
    IsCyclic (center R) ∧ ¬ IsMulCommutative R ∧ (center R).index = 4 := by
  have hQc : Nat.card Q = 8 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hcard := card_mul_eq_card_inf_mul_card_sup_of_normalizes Q C
    le_normalizer_of_normal
  rw [hQc, hcap, hgen] at hcard
  have hZcard : Nat.card (center R) = Nat.card C := by
    rw [hC, card_map_of_injective R.subtype_injective]
  have hZcyc : IsCyclic (center R) := by
    have : IsCyclic ((center R).map R.subtype) := hC ▸ inferInstance
    let eZ := (center R).equivMapOfInjective R.subtype R.subtype_injective
    exact isCyclic_of_injective eZ.toMonoidHom eZ.injective
  refine ⟨hZcyc, ?_, ?_⟩
  · intro hR
    let := hR
    have hQR : Q ≤ R := hgen ▸ le_sup_left
    have hcomm (x y : Q) : x * y = y * x := by
      apply Subtype.ext
      change (x : P) * (y : P) = (y : P) * (x : P)
      exact congrArg (fun r : R => (r : P)) (mul_comm (⟨x, hQR x.property⟩ : R) ⟨y, hQR y.property⟩)
    have hh := congrArg e (hcomm (e.symm (QuaternionGroup.a 1)) (e.symm (QuaternionGroup.xa 0)))
    simp only [map_mul, e.apply_symm_apply] at hh
    exact (by decide : (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.xa 0 ≠
      QuaternionGroup.xa 0 * QuaternionGroup.a 1) hh
  · have hh := (center R).card_mul_index
    rw [hZcard] at hh
    have hp := Nat.card_pos (α := C)
    nlinarith

private theorem sup_eq_top_of_index_two_not_le {P : Type*} [Group P] (R A : Subgroup P)
    (hi : R.index = 2) (hout : ¬ A ≤ R) : R ⊔ A = ⊤ := by
  obtain ⟨t, ht, htr⟩ := SetLike.not_le_iff_exists.mp hout
  apply top_unique
  intro x _
  by_cases hx : x ∈ R
  · exact (show R ≤ R ⊔ A from le_sup_left) hx
  · have hxt : x * t⁻¹ ∈ R := by
      rw [R.mul_mem_iff_of_index_two hi, R.inv_mem_iff]
      exact iff_of_false hx htr
    have hh := (R ⊔ A).mul_mem ((show R ≤ R ⊔ A from le_sup_left) hxt) ((show A ≤ R ⊔ A from le_sup_right) ht)
    simpa using hh

private theorem inf_eq_unique_four_of_cyclic_center_index_four {P : Type*} [Group P] [Finite P]
    (R W F : Subgroup P) (hi : R.index = 2)
    [IsCyclic (center R)] (hn : ¬ IsMulCommutative R) (hZ : (center R).index = 4)
    [IsElementaryAbelian 2 F] (hout : ¬ F ≤ R)
    (hcap : Nat.card (R.subgroupOf F) = 4)
    (hunique : ∀ U : Subgroup P, U.Normal → IsElementaryAbelian 2 U → Nat.card U = 4 → U = W) :
    R ⊓ F = W := by
  let E := R ⊓ F
  have hmap : (R.subgroupOf F).map F.subtype = E := by
    rw [← inf_subgroupOf_right R F, map_subgroupOf_eq_of_le inf_le_right]
  let : IsElementaryAbelian 2 (R.subgroupOf F) := by
    refine { toIsMulCommutative := inferInstance, exponent_dvd_p := ?_ }
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    exact Subtype.ext (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 F) x.val)
  let : IsElementaryAbelian 2 E := hmap ▸ IsElementaryAbelian.map F.subtype
  have hE : Nat.card E = 4 := by
    rw [← hmap, card_map_of_injective F.subtype_injective, hcap]
  have hER : E ≤ R := inf_le_left
  let : IsElementaryAbelian 2 (E.subgroupOf R) := IsElementaryAbelian.subgroupOf hER
  have hEn := elementary_four_normal_of_cyclic_center_index_four hn hZ (E.subgroupOf R)
    ((Nat.card_congr (subgroupOfEquivOfLe hER).toEquiv).trans hE)
  have hRN : R ≤ normalizer (E : Set P) := (normal_subgroupOf_iff_le_normalizer hER).mp hEn
  have hFN : F ≤ normalizer (E : Set P) := by
    apply (le_centralizer_iff.mpr ((show E ≤ F from inf_le_right).trans F.le_centralizer)).trans
    exact centralizer_le_normalizer _
  have hEnP : E.Normal := normalizer_eq_top_iff.mp
    (top_unique ((sup_eq_top_of_index_two_not_le R F hi hout) ▸ sup_le hRN hFN))
  exact hunique E hEnP inferInstance hE

private theorem normalizes_four_of_inner_on_quaternion_supplement {P : Type*} [Group P] [Finite P]
    (R Q C E : Subgroup P) [R.Normal] [C.Normal]
    [IsCyclic (center R)] (hn : ¬ IsMulCommutative R) (hZ : (center R).index = 4)
    (hgen : Q ⊔ C = R) (hC : C = (center R).map R.subtype)
    [IsElementaryAbelian 2 E] (hE : Nat.card E = 4) (hER : E ≤ R)
    (t : P) (q₀ : Q)
    (hinner : ∀ q : Q, t * (q : P) * t⁻¹ = (q₀ : P) * (q : P) * (q₀ : P)⁻¹) :
    t ∈ normalizer (E : Set P) := by
  let E' := E.subgroupOf R
  let : IsElementaryAbelian 2 E' := IsElementaryAbelian.subgroupOf hER
  have hE' : Nat.card E' = 4 := (Nat.card_congr (subgroupOfEquivOfLe hER).toEquiv).trans hE
  have hRN : R ≤ normalizer (E : Set P) := (normal_subgroupOf_iff_le_normalizer hER).mp
    (elementary_four_normal_of_cyclic_center_index_four hn hZ E' hE')
  have hCD : C ≤ centralizer (E : Set P) := by
    rw [hC]
    rintro _ ⟨c, hc, rfl⟩ x hx
    exact congrArg (fun r : R => (r : P)) (mem_center_iff.mp hc ⟨x, hER hx⟩)
  have hQR : Q ≤ R := hgen ▸ le_sup_left
  apply mem_normalizer_fintype
  intro x hx
  have hxR := hER hx
  obtain ⟨q, hq, c, hc, hqc⟩ := mem_sup_of_normal_right.mp (hgen ▸ hxR)
  have hqD : q ∈ centralizer (E : Set P) := by
    have hh := (centralizer (E : Set P)).mul_mem (E.le_centralizer hx)
      ((centralizer (E : Set P)).inv_mem (hCD hc))
    simpa only [← hqc, mul_inv_cancel_right] using hh
  have htqD : t * q * t⁻¹ ∈ centralizer (E : Set P) := by
    rw [hinner ⟨q, hq⟩]
    exact (mem_normalizer_iff.mp
      (normalizer_le_normalizer_centralizer E (hRN (hQR q₀.property))) q).mp hqD
  have htcD : t * c * t⁻¹ ∈ centralizer (E : Set P) :=
    hCD ((inferInstance : C.Normal).conj_mem c hc t)
  have htxD : t * x * t⁻¹ ∈ centralizer (E : Set P) := by
    have hh := (centralizer (E : Set P)).mul_mem htqD htcD
    simpa only [← hqc, mul_assoc, inv_mul_cancel_left] using hh
  have htxR : t * x * t⁻¹ ∈ R := (inferInstance : R.Normal).conj_mem x hxR t
  exact mem_of_pow_eq_one_of_elementary_card_le (p := 2) E' (by
      intro A hA
      let := hA
      simpa only [hE'] using card_elementary_le_four_of_cyclic_center_index_four hn hZ A)
    (x := ⟨t * x * t⁻¹, htxR⟩) (by
      apply Subtype.ext
      change (t * x * t⁻¹) ^ 2 = 1
      have hp := congrArg (MulAut.conj t) (elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx)
      simpa only [map_pow, map_one, MulAut.conj_apply] using hp) (by
      intro e he
      exact Subtype.ext (htxD e he))

private theorem quaternion_axis_table : ∀ a : QuaternionGroup 2,
    (∃ b, b * a ≠ a * b) →
    ∃ b, b ^ 2 = a ^ 2 ∧ b * a ≠ a * b ∧ (a ^ 2) ^ 2 = 1 ∧ a ^ 2 ≠ 1 := by
  decide

private theorem exists_distinct_four_of_quaternion_cyclic_supplement {P : Type*} [Group P] [Finite P]
    (R Q C E : Subgroup P) [C.Normal] [IsCyclic C]
    (e : Q ≃* QuaternionGroup 2) (hgen : Q ⊔ C = R)
    (hC : C = (center R).map R.subtype)
    [IsElementaryAbelian 2 E] (hE : Nat.card E = 4) (hER : E ≤ R) :
    ∃ U : Subgroup P, U ≤ R ∧ IsElementaryAbelian 2 U ∧ Nat.card U = 4 ∧ U ≠ E := by
  have hCR : C ≤ R := hgen ▸ le_sup_right
  have hQR : Q ≤ R := hgen ▸ le_sup_left
  have hcentral (c : P) (hc : c ∈ C) (r : P) (hr : r ∈ R) : Commute r c := by
    rw [hC] at hc
    obtain ⟨c', hc', rfl⟩ := hc
    exact congrArg (fun r : R => (r : P)) (mem_center_iff.mp hc' ⟨r, hr⟩)
  have hEnC : ¬ E ≤ C := by
    intro h
    let : IsCyclic E := isCyclic_of_le h
    exact IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq
      (A := E) (p := 2) (by simpa using hE) inferInstance
  obtain ⟨w, hw, hwC⟩ := SetLike.not_le_iff_exists.mp hEnC
  obtain ⟨q, hq, c, hc, hqc⟩ := mem_sup_of_normal_right.mp (hgen ▸ hER hw)
  let a : Q := ⟨q, hq⟩
  have ha : ∃ b : QuaternionGroup 2, b * e a ≠ e a * b := by
    by_contra! hh
    have hqcent : q ∈ (center R).map R.subtype := by
      refine ⟨⟨q, hQR hq⟩, mem_center_iff.mpr ?_, rfl⟩
      intro r
      obtain ⟨u, hu, d, hd, hud⟩ := mem_sup_of_normal_right.mp (show (r : P) ∈ Q ⊔ C by rw [hgen]; exact r.property)
      apply Subtype.ext
      change (r : P) * q = q * (r : P)
      have huq : Commute u q := by
        have h : (⟨u, hu⟩ : Q) * a = a * ⟨u, hu⟩ := e.injective
          (by simpa only [map_mul] using hh (e ⟨u, hu⟩))
        exact congrArg (fun x : Q => (x : P)) h
      rw [← hud]
      exact (huq.mul_left (hcentral d hd q (hQR hq)).symm).eq
    have hqC : q ∈ C := hC ▸ hqcent
    exact hwC (hqc ▸ C.mul_mem hqC hc)
  obtain ⟨b, hb, hba, ha4, ha2⟩ := quaternion_axis_table (e a) ha
  let b' : Q := e.symm b
  have hbsq : b' ^ 2 = a ^ 2 := e.injective (by simpa [b'] using hb)
  have hnoncomm : (b' : P) * q ≠ q * (b' : P) := by
    intro hh
    apply hba
    have hh' : b' * a = a * b' := Subtype.ext hh
    simpa [b'] using congrArg e hh'
  have hq4 : (q ^ 2) ^ 2 = 1 := by
    have hh : (a ^ 2) ^ 2 = 1 := e.injective (by simpa only [map_pow, map_one] using ha4)
    exact congrArg (fun x : Q => (x : P)) hh
  have hq2 : q ^ 2 ≠ 1 := by
    intro hh
    apply ha2
    have hh' : a ^ 2 = 1 := Subtype.ext hh
    simpa only [map_pow, map_one] using congrArg e hh'
  have hw2 : (q * c) ^ 2 = 1 := hqc ▸ elemPow_eq_one_of_isElementaryAbelian (p := 2) w hw
  have hqC : q ^ 2 ∈ C := by
    have hh : q ^ 2 = (c ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left (by
      rw [← (hcentral c hc q (hQR hq)).mul_pow]
      exact hw2)
    rw [hh]
    exact C.inv_mem (C.pow_mem hc 2)
  let v : P := (b' : P) * c
  have hvR : v ∈ R := R.mul_mem (hQR b'.property) (hCR hc)
  have hv2 : v ^ 2 = 1 := by
    dsimp [v]
    rw [(hcentral c hc b' (hQR b'.property)).mul_pow]
    have hs : (b' : P) ^ 2 = q ^ 2 := congrArg (fun x : Q => (x : P)) hbsq
    rw [hs, ← (hcentral c hc q (hQR hq)).mul_pow]
    exact hw2
  have hvw : ¬ Commute v w := by
    intro hh
    apply hnoncomm
    have he := hh.eq
    rw [← hqc] at he
    dsimp [v] at he
    rw [(hcentral c hc q (hQR hq)).symm.mul_mul_mul_comm,
      (hcentral c hc b' (hQR b'.property)).symm.mul_mul_mul_comm] at he
    exact mul_right_cancel he
  have hv1 : v ≠ 1 := by
    intro hh
    apply hvw
    rw [hh]
    exact Commute.one_left _
  have hvz : v ≠ q ^ 2 := by
    intro hh
    apply hvw
    rw [hh]
    exact (hcentral (q ^ 2) hqC w (hER hw)).symm
  let U := closure ({v, q ^ 2} : Set P)
  let : IsKleinFour U := isKleinFour_closure_pair v (q ^ 2)
    (by simpa only [pow_two] using hv2) (by simpa only [pow_two] using hq4)
    hv1 hq2 hvz (hcentral (q ^ 2) hqC v hvR)
  have hUe : IsElementaryAbelian 2 U := {
    toIsMulCommutative := IsKleinFour.isMulCommutative
    exponent_dvd_p := by rw [IsKleinFour.exponent_two] }
  refine ⟨U, ?_, hUe, IsKleinFour.card_four, ?_⟩
  · apply (closure_le _).mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact hvR
    · have : x = q ^ 2 := Set.mem_singleton_iff.mp hx
      exact this ▸ hCR hqC
  · intro hh
    have hvE : v ∈ E := hh ▸ (show v ∈ U from subset_closure (by simp))
    apply hvw
    change v * w = w * v
    exact congrArg (fun x : E => (x : P)) (mul_comm (⟨v, hvE⟩ : E) ⟨w, hw⟩)

private theorem not_inner_of_unique_four_in_quaternion_cyclic_core {P : Type*} [Group P] [Finite P]
    (R Q C W : Subgroup P) (hi : R.index = 2) [Q.Normal] [C.Normal]
    [IsCyclic C] (e : Q ≃* QuaternionGroup 2) (hgen : Q ⊔ C = R)
    (hcap : Nat.card (Q ⊓ C : Subgroup P) = 2)
    (hC : C = (center R).map R.subtype)
    [IsElementaryAbelian 2 W] (hW : Nat.card W = 4) (hWR : W ≤ R)
    (hunique : ∀ U : Subgroup P, U.Normal → IsElementaryAbelian 2 U → Nat.card U = 4 → U = W)
    (t : P) (ht : t ∉ R) :
    ¬ ∃ q₀ : Q, ∀ q : Q, t * (q : P) * t⁻¹ = (q₀ : P) * (q : P) * (q₀ : P)⁻¹ := by
  rintro ⟨q₀, hinner⟩
  obtain ⟨hZcyc, hn, hZ⟩ := quaternion_cyclic_center_data R Q C e hgen hcap hC
  let := hZcyc
  let : R.Normal := R.normal_of_index_eq_two hi
  obtain ⟨U, hUR, hUe, hU, hne⟩ := exists_distinct_four_of_quaternion_cyclic_supplement R Q C W e hgen hC hW hWR
  let := hUe
  let : IsElementaryAbelian 2 (U.subgroupOf R) := IsElementaryAbelian.subgroupOf hUR
  have hRN : R ≤ normalizer (U : Set P) := (normal_subgroupOf_iff_le_normalizer hUR).mp
    (elementary_four_normal_of_cyclic_center_index_four hn hZ (U.subgroupOf R)
      ((Nat.card_congr (subgroupOfEquivOfLe hUR).toEquiv).trans hU))
  have htN := normalizes_four_of_inner_on_quaternion_supplement R Q C U hn hZ hgen hC hU hUR t q₀ hinner
  have hgenP := sup_eq_top_of_index_two_not_le R (zpowers t) hi (fun h => ht (h (mem_zpowers t)))
  have hUn : U.Normal := normalizer_eq_top_iff.mp
    (top_unique (hgenP ▸ sup_le hRN (zpowers_le.mpr htN)))
  exact hne (hunique U hUn hUe hU)

/-- A crossing elementary eight meets a quaternion–cyclic core in the unique
normal elementary four of the ambient group. -/
public theorem inf_eq_unique_normal_four_of_quaternion_cyclic_core
    {P : Type*} [Group P] [Finite P]
    (R Q C W : Subgroup P) (hi : R.index = 2) [Q.Normal] [C.Normal]
    [IsCyclic C] (hQ : Nonempty (Q ≃* QuaternionGroup 2))
    (hgen : Q ⊔ C = R) (hcap : Nat.card (Q ⊓ C : Subgroup P) = 2)
    (hC : C = (center R).map R.subtype)
    (hunique : ∀ U : Subgroup P, U.Normal → IsElementaryAbelian 2 U →
      Nat.card U = 4 → U = W)
    (F : Subgroup P) [IsElementaryAbelian 2 F] (hF : Nat.card F = 8)
    (hout : ¬ F ≤ R) : R ⊓ F = W := by
  obtain ⟨e⟩ := hQ
  obtain ⟨hZcyc, hn, hZ⟩ := quaternion_cyclic_center_data R Q C e hgen hcap hC
  let := hZcyc
  exact inf_eq_unique_four_of_cyclic_center_index_four R W F hi hn hZ hout
    (card_intersection_four_of_elementary_eight_not_le R F hi hF hout) hunique

/-- The intersection is the unique normal four, and every outside element of
the elementary eight induces an outer action on the quaternion factor. -/
public theorem quaternion_cyclic_core_four_and_outer_action
    {P : Type*} [Group P] [Finite P]
    (R Q C W : Subgroup P) (hi : R.index = 2) [Q.Normal] [C.Normal]
    [IsCyclic C] (hQ : Nonempty (Q ≃* QuaternionGroup 2))
    (hgen : Q ⊔ C = R) (hcap : Nat.card (Q ⊓ C : Subgroup P) = 2)
    (hC : C = (center R).map R.subtype)
    [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ U : Subgroup P, U.Normal → IsElementaryAbelian 2 U →
      Nat.card U = 4 → U = W)
    (F : Subgroup P) [IsElementaryAbelian 2 F] (hF : Nat.card F = 8)
    (hout : ¬ F ≤ R) :
    R ⊓ F = W ∧ ∀ t : P, t ∈ F → t ∉ R →
      ¬ ∃ q₀ : Q, ∀ q : Q,
        t * (q : P) * t⁻¹ = (q₀ : P) * (q : P) * (q₀ : P)⁻¹ := by
  have hRF := inf_eq_unique_normal_four_of_quaternion_cyclic_core
    R Q C W hi hQ hgen hcap hC hunique F hF hout
  refine ⟨hRF, ?_⟩
  intro t _ ht
  obtain ⟨e⟩ := hQ
  exact not_inner_of_unique_four_in_quaternion_cyclic_core R Q C W hi e hgen hcap hC hW
    (hRF ▸ inf_le_left) hunique t ht

end Subgroup
