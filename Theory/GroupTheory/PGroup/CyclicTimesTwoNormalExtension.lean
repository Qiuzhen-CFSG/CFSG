module

public import Theory.GroupTheory.PGroup.OmegaAction
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.Tactic.Group

/-!
# Normal cyclic-times-two extensions

An index-two extension centralizing the fourth roots of an abelian two-group
has binary conjugation displacements. When the first omega of the base is
central, its second omega is abelian. For a cyclic-times-two base with a long
factor of order at least eight, a nontrivial action supplies an outside fourth
root. The first omega then supplies a normal elementary eight, or the second
omega contains a square root of the specified short-factor involution.

The proof uses power descent for inverted elements, followed by cyclic
coordinates and correction of an outside representative by a base element.
Source: MacWilliams, Trans. AMS 150 (1970), §3(iv), 1.2.2, printed p.368.
-/

open scoped IsMulCommutative

namespace Subgroup

private theorem binary_of_inverted_of_fixed_fourth
    {G : Type*} [Group G] (hG : IsPGroup 2 G) (f : MulAut G)
    (hfix : ∀ x : G, x ^ 4 = 1 → f x = x)
    (x : G) (hinv : f x = x⁻¹) : x ^ 2 = 1 := by
  have aux : ∀ k (y : G), y ^ (2 ^ k) = 1 → f y = y⁻¹ → y ^ 2 = 1 := by
    intro k
    induction k with
    | zero =>
      intro y hy _
      simp only [pow_zero, pow_one] at hy
      simp [hy]
    | succ k ih =>
      intro y hy hi
      have hfour : y ^ 4 = 1 := by
        have hsq : (y ^ 2) ^ (2 ^ k) = 1 := by
          rw [← pow_mul, Nat.mul_comm 2, ← pow_succ]
          exact hy
        simpa only [← pow_mul, Nat.reduceMul] using
          ih (y ^ 2) hsq (by rw [map_pow, hi, inv_pow])
      have hyinv : y = y⁻¹ := (hfix y hfour).symm.trans hi
      calc
        y ^ 2 = y * y := pow_two y
        _ = y * y⁻¹ := congrArg (y * ·) hyinv
        _ = 1 := mul_inv_cancel y
  obtain ⟨k, hk⟩ := hG x
  exact aux k x hk hinv

private theorem commute_fourth_of_le_centralizer_omega_two
    {P : Type*} [Group P] (B R : Subgroup P)
    (hcent : R ≤ centralizer (((omega B (p := 2) 2).map B.subtype : Subgroup P) : Set P))
    {r x : P} (hr : r ∈ R) (hx : x ∈ B) (hx4 : x ^ 4 = 1) : Commute r x := by
  exact (hcent hr x ⟨⟨x, hx⟩, subset_closure (Subtype.ext hx4), rfl⟩).symm

/-- The conjugation displacement in an index-two abelian base has square one
when the extension centralizes the fourth roots of the base. -/
public theorem displacement_sq_eq_one_of_index_two_fourth_centralizer
    {P : Type*} [Group P] (hP : IsPGroup 2 P)
    (B R : Subgroup P) [B.Normal] [IsMulCommutative B]
    (hi : B.relIndex R = 2)
    (hcent : R ≤ centralizer (((omega B (p := 2) 2).map B.subtype : Subgroup P) : Set P))
    {r : P} (hr : r ∈ R) (d : B) :
    (MulAut.conjNormal r d * d⁻¹) ^ 2 = 1 := by
  have hr2 : r ^ 2 ∈ B :=
    (B.subgroupOf R).sq_mem_of_index_two hi (⟨r, hr⟩ : R)
  let f : MulAut B := MulAut.conjNormal r
  have hff (x : B) : f (f x) = x := by
    apply Subtype.ext
    change r * (r * (x : P) * r⁻¹) * r⁻¹ = x
    calc
      r * (r * (x : P) * r⁻¹) * r⁻¹ = r ^ 2 * (x : P) * (r ^ 2)⁻¹ := by simp only [pow_two]; group
      _ = x := by rw [← B.le_centralizer hr2 x x.property, mul_inv_cancel_right]
  apply binary_of_inverted_of_fixed_fourth (hP.to_subgroup B) f
    (fun x hx => Subtype.ext (by
      change r * (x : P) * r⁻¹ = x
      rw [(commute_fourth_of_le_centralizer_omega_two B R hcent hr x.property
        (congrArg Subtype.val hx)).eq, mul_inv_cancel_right]))
  change f (f d * d⁻¹) = (f d * d⁻¹)⁻¹
  simp only [map_mul, map_inv, hff, mul_inv_rev, inv_inv]

private theorem fourth_mul_base
    {P : Type*} [Group P] (hP : IsPGroup 2 P)
    (B R : Subgroup P) [B.Normal] [IsMulCommutative B]
    (hi : B.relIndex R = 2)
    (hcent : R ≤ centralizer (((omega B (p := 2) 2).map B.subtype : Subgroup P) : Set P))
    (hWcentral : (omega₁ B (p := 2)).map B.subtype ≤ center P)
    {r d : P} (hr : r ∈ R) (hd : d ∈ B) : (d * r) ^ 4 = d ^ 4 * r ^ 4 := by
  let w : B := MulAut.conjNormal r ⟨d, hd⟩ * (⟨d, hd⟩ : B)⁻¹
  have hw2 : w ^ 2 = 1 :=
    displacement_sq_eq_one_of_index_two_fourth_centralizer hP B R hi hcent hr _
  have hwc : (w : P) ∈ center P :=
    hWcentral ⟨w, subset_closure hw2, rfl⟩
  have hrel : r * d = (w : P) * d * r := by
    change r * d = (r * d * r⁻¹ * d⁻¹) * d * r
    group
  have hd2 : Commute r (d ^ 2) := by
    have hh : MulAut.conjNormal r (⟨d, hd⟩ : B) = w * ⟨d, hd⟩ := by
      dsimp [w]; simp
    have hsq : r * d ^ 2 * r⁻¹ = d ^ 2 := by
      have ht := congrArg (fun x : B => (x : P)) (congrArg (fun x : B => x ^ 2) hh)
      rw [mul_pow, hw2, one_mul] at ht
      change (r * d * r⁻¹) ^ 2 = d ^ 2 at ht
      calc
        r * d ^ 2 * r⁻¹ = (r * d * r⁻¹) ^ 2 := by simp only [pow_two]; group
        _ = d ^ 2 := ht
    exact mul_inv_eq_iff_eq_mul.mp hsq
  have hs : (d * r) ^ 2 = (w : P) * d ^ 2 * r ^ 2 := by
    calc
      (d * r) ^ 2 = d * (r * d) * r := by simp only [pow_two]; group
      _ = d * ((w : P) * d * r) * r := by rw [hrel]
      _ = (w : P) * d ^ 2 * r ^ 2 := by
        simp only [pow_two, ← mul_assoc]
        rw [← mem_center_iff.mp hwc d]
  calc
    (d * r) ^ 4 = ((d * r) ^ 2) ^ 2 := by rw [← pow_mul]
    _ = ((w : P) * (d ^ 2 * r ^ 2)) ^ 2 := by rw [hs, mul_assoc]
    _ = (w : P) ^ 2 * (d ^ 2 * r ^ 2) ^ 2 :=
      (show Commute (w : P) (d ^ 2 * r ^ 2) from
        (mem_center_iff.mp hwc _).symm).mul_pow 2
    _ = d ^ 4 * r ^ 4 := by
      rw [show (w : P) ^ 2 = 1 from congrArg Subtype.val hw2, one_mul,
        (hd2.symm.pow_right 2).mul_pow, ← pow_mul, ← pow_mul]

/-- Fourth roots in the extension commute. The cyclic-times-two decomposition
is not needed for this part of the obstruction. -/
public theorem isMulCommutative_omega_two_of_index_two_fourth_centralizer
    {P : Type*} [Group P] (hP : IsPGroup 2 P)
    (B R : Subgroup P) [B.Normal] [IsMulCommutative B]
    (hi : B.relIndex R = 2)
    (hcent : R ≤ centralizer (((omega B (p := 2) 2).map B.subtype : Subgroup P) : Set P))
    (hWcentral : (omega₁ B (p := 2)).map B.subtype ≤ center P) :
    IsMulCommutative (omega R (p := 2) 2) := by
  apply isMulCommutative_closure
  intro x hx y hy
  have hx4 : (x : P) ^ 4 = 1 := congrArg Subtype.val (show x ^ 4 = 1 from hx)
  have hy4 : (y : P) ^ 4 = 1 := congrArg Subtype.val (show y ^ 4 = 1 from hy)
  apply Subtype.ext
  by_cases hxB : (x : P) ∈ B
  · exact (commute_fourth_of_le_centralizer_omega_two B R hcent y.property hxB hx4).eq.symm
  by_cases hyB : (y : P) ∈ B
  · exact (commute_fourth_of_le_centralizer_omega_two B R hcent x.property hyB hy4).eq
  have hdB : (y : P) * (x : P)⁻¹ ∈ B :=
    (B.subgroupOf R).mul_mem_iff_of_index_two hi |>.mpr (by
      change ((y : P) ∈ B ↔ (x⁻¹ : R) ∈ B.subgroupOf R)
      simp only [mem_subgroupOf, inv_mem_iff, hxB, hyB])
  have hd4 : ((y : P) * (x : P)⁻¹) ^ 4 = 1 := by
    have hh := fourth_mul_base hP B R hi hcent hWcentral x.property hdB
    simpa only [inv_mul_cancel_right, hx4, hy4, mul_one] using hh.symm
  have hc := commute_fourth_of_le_centralizer_omega_two B R hcent x.property hdB hd4
  have hh := congrArg (fun a : P => a * x) hc.eq
  simpa only [coe_mul, mul_assoc, inv_mul_cancel, mul_one, inv_mul_cancel_right] using hh

/-- An outside involution yields a normal elementary eight, using the
characteristic first omega of the extension for ambient normality. -/
public theorem normal_elementary_eight_of_outside_involution_of_fourth_centralizer
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (B R : Subgroup P) [B.Normal] [R.Normal] [IsMulCommutative B]
    (hBR : B ≤ R) (hi : B.relIndex R = 2)
    (hcent : R ≤ centralizer (((omega B (p := 2) 2).map B.subtype : Subgroup P) : Set P))
    (hWcentral : (omega₁ B (p := 2)).map B.subtype ≤ center P)
    (hWcard : Nat.card (omega₁ B (p := 2)) = 4)
    {r : P} (hr : r ∈ R) (hrB : r ∉ B) (hr2 : r ^ 2 = 1) :
    ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E := by
  let O := omega R (p := 2) 2
  let V := omega₁ R (p := 2)
  let : IsMulCommutative O :=
    isMulCommutative_omega_two_of_index_two_fourth_centralizer hP B R hi hcent hWcentral
  have hVO : V ≤ O := by
    apply (closure_le _).mpr
    intro x hx
    apply subset_closure
    change x ^ 4 = 1
    rw [show 4 = 2 * 2 by decide, pow_mul, show x ^ 2 = 1 from hx, one_pow]
  let : IsMulCommutative V := IsMulCommutative.of_setLike_mul_comm fun x hx y hy =>
    O.le_centralizer (hVO hy) x (hVO hx)
  let : IsElementaryAbelian 2 V := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x => by
      apply Subtype.ext
      exact closure_induction (k := {y : R | y ^ (2 ^ 1) = 1})
        (p := fun y _ => y ^ 2 = 1)
        (fun _ hy => by simpa using hy) (by simp)
        (fun y z hy hz hy2 hz2 => by
          rw [(show Commute y z from (V.le_centralizer hz y hy)).mul_pow, hy2, hz2, one_mul])
        (fun y _ hy => by rw [inv_pow, hy, inv_one]) x.property }
  let E := V.map R.subtype
  let : V.Characteristic := omega₁_characteristic R
  let : E.Normal := ConjAct.normal_of_characteristic_of_normal
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map_subtype
  let W := (omega₁ B (p := 2)).map B.subtype
  let : IsElementaryAbelian 2 (omega₁ B (p := 2)) :=
    IsElementaryAbelian.omega₁_of_isMulCommutative B
  have hWE : W ≤ E := by
    rintro x ⟨d, hd, rfl⟩
    refine ⟨⟨d, hBR d.property⟩, subset_closure ?_, rfl⟩
    apply Subtype.ext
    change (d : P) ^ 2 = 1
    exact congrArg (fun a : B => (a : P))
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) d hd)
  have hrE : r ∈ E := ⟨⟨r, hr⟩, subset_closure (Subtype.ext hr2), rfl⟩
  have hcW : Nat.card W = 4 := (card_map_of_injective B.subtype_injective).trans hWcard
  have hlt : 4 < Nat.card E := by
    by_contra! hh
    have he : W = E := eq_of_le_of_card_ge hWE (hcW ▸ hh)
    exact hrB (map_subtype_le _ (he ▸ hrE))
  have hdiv : 4 ∣ Nat.card E := hcW ▸ card_dvd_of_le hWE
  obtain ⟨k, hk⟩ := hdiv
  refine ⟨E, inferInstance, inferInstance, ?_⟩
  omega

private theorem cyclic_two_coordinates
    {P : Type*} [Group P] [Finite P]
    (B : Subgroup P) (b z : P)
    (hz : orderOf z = 2) (hgen : zpowers b ⊔ zpowers z = B)
    (hWcentral : (omega₁ B (p := 2)).map B.subtype ≤ center P) :
    ∀ x ∈ B, ∃ k : ℕ, x = b ^ k ∨ x = b ^ k * z := by
  classical
  have hzB : z ∈ B := hgen ▸ (le_sup_right : zpowers z ≤ zpowers b ⊔ zpowers z) (mem_zpowers z)
  have hz2 : z ^ 2 = 1 := hz ▸ pow_orderOf_eq_one z
  have hzC : z ∈ center P := hWcentral ⟨⟨z, hzB⟩, subset_closure (Subtype.ext hz2), rfl⟩
  have hZC : zpowers z ≤ center P := zpowers_le.mpr hzC
  let : (zpowers z).Normal := ⟨fun x hx g => by
    rw [mem_center_iff.mp (hZC hx) g, mul_inv_cancel_right]
    exact hx⟩
  intro x hx
  obtain ⟨a, ha, c, hc, rfl⟩ := mem_sup_of_normal_right.mp (hgen ▸ hx)
  obtain ⟨k, rfl⟩ := mem_powers_iff_mem_zpowers.mpr ha
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hc)
  have hi2 : i < 2 := by simpa only [hz] using Finset.mem_range.mp hi
  refine ⟨k, ?_⟩
  have hii : i = 0 ∨ i = 1 := by omega
  rcases hii with rfl | rfl <;> simp

/-- The nontrivial coset of a self-centralizing cyclic-times-two base has a
representative of order dividing four. -/
public theorem exists_outside_fourth_root_of_cyclic_two_base
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (B R : Subgroup P) [B.Normal] [IsMulCommutative B]
    (b z : P) (hz : orderOf z = 2)
    (hgen : zpowers b ⊔ zpowers z = B)
    (hBR : B ≤ R) (hi : B.relIndex R = 2)
    (hcent : R ≤ centralizer (((omega B (p := 2) 2).map B.subtype : Subgroup P) : Set P))
    (hself : R ⊓ centralizer (B : Set P) ≤ B)
    (hWcentral : (omega₁ B (p := 2)).map B.subtype ≤ center P) :
    ∃ r ∈ R, r ∉ B ∧ r ^ 4 = 1 := by
  classical
  have hRB : ¬ R ≤ B := by
    intro hh
    have := relIndex_eq_one.mpr hh
    omega
  obtain ⟨r, hrR, hrB⟩ := SetLike.not_le_iff_exists.mp hRB
  have hr2 : r ^ 2 ∈ B :=
    (B.subgroupOf R).sq_mem_of_index_two hi (⟨r, hrR⟩ : R)
  have hbB : b ∈ B := hgen ▸ (le_sup_left : zpowers b ≤ zpowers b ⊔ zpowers z) (mem_zpowers b)
  have hzB : z ∈ B := hgen ▸ (le_sup_right : zpowers z ≤ zpowers b ⊔ zpowers z) (mem_zpowers z)
  have hz2 : z ^ 2 = 1 := hz ▸ pow_orderOf_eq_one z
  have hzC : z ∈ center P := hWcentral ⟨⟨z, hzB⟩, subset_closure (Subtype.ext hz2), rfl⟩
  obtain ⟨k, hk⟩ := cyclic_two_coordinates B b z hz hgen hWcentral _ hr2
  have hfix : MulAut.conj r (b ^ k) = b ^ k := by
    have hrfix : MulAut.conj r (r ^ 2) = r ^ 2 := by
      change r * r ^ 2 * r⁻¹ = r ^ 2
      simp only [pow_two]; group
    rcases hk with hk | hk
    · simpa only [hk] using hrfix
    · rw [hk, map_mul] at hrfix
      have hzfix : MulAut.conj r z = z := by
        change r * z * r⁻¹ = z
        rw [mem_center_iff.mp hzC r, mul_inv_cancel_right]
      rw [hzfix] at hrfix
      exact mul_right_cancel hrfix
  have hkeven : Even k := by
    rcases Nat.even_or_odd k with he | ho
    · exact he
    exfalso
    apply hrB
    apply hself ⟨hrR, ?_⟩
    have hcb : Commute r b := by
      have hh : MulAut.conj r b = b := by
        apply (hP.powEquiv (Nat.coprime_two_left.mpr ho)).injective
        simpa only [IsPGroup.powEquiv_apply, ← map_pow] using hfix
      exact mul_inv_eq_iff_eq_mul.mp hh
    have hle : B ≤ centralizer ({r} : Set P) := by
      rw [← hgen]
      apply sup_le
      · exact zpowers_le.mpr (by
          intro y hy
          have : y = r := hy
          subst y
          exact hcb.eq)
      · exact zpowers_le.mpr (by
          intro y hy
          have : y = r := hy
          subst y
          exact mem_center_iff.mp hzC r)
    intro x hx
    exact (hle hx r (Set.mem_singleton r)).symm
  obtain ⟨j, hj⟩ := hkeven
  let d := (b ^ j)⁻¹
  have hdB : d ∈ B := B.inv_mem (B.pow_mem hbB j)
  have hr4 : r ^ 4 = (b ^ j) ^ 4 := by
    calc
      r ^ 4 = (r ^ 2) ^ 2 := by rw [← pow_mul]
      _ = (b ^ k) ^ 2 := by
        rcases hk with hk | hk
        · rw [hk]
        · rw [hk, (show Commute (b ^ k) z from mem_center_iff.mp hzC _).mul_pow,
            hz2, mul_one]
      _ = (b ^ j) ^ 4 := by rw [← pow_mul, ← pow_mul, hj]; congr 1; omega
  refine ⟨d * r, R.mul_mem (hBR hdB) hrR, ?_, ?_⟩
  · intro hm
    exact hrB ((B.mul_mem_cancel_left hdB).mp hm)
  · rw [fourth_mul_base hP B R hi hcent hWcentral hrR hdB, hr4]
    exact inv_pow (b ^ j) 4 ▸ inv_mul_cancel ((b ^ j) ^ 4)

private theorem root_of_binary_cyclic_power
    {P : Type*} [Group P] (hP : IsPGroup 2 P) (b : P)
    (hb4 : b ^ 4 ≠ 1) (k : ℕ) (hk : (b ^ k) ^ 2 = 1) :
    ∃ t ∈ zpowers b, t ^ 2 = b ^ k ∧ t ^ 4 = 1 := by
  obtain ⟨n, hn⟩ := hP.exists_orderOf_eq_pow b
  have hn3 : 3 ≤ n := by
    by_contra! hsmall
    apply hb4
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [hn]
    exact pow_dvd_pow 2 (by omega : n ≤ 2)
  have h4 : 4 ∣ orderOf b := by
    rw [hn]
    exact pow_dvd_pow 2 (by omega : 2 ≤ n)
  have hdiv : 4 ∣ k * 2 := h4.trans (orderOf_dvd_of_pow_eq_one (by
    simpa only [pow_mul] using hk))
  have heven : Even k := even_iff_two_dvd.mpr (by omega)
  obtain ⟨j, hj⟩ := heven
  have ht : (b ^ j) ^ 2 = b ^ k := by
    rw [← pow_mul, hj]
    congr 1
    omega
  refine ⟨b ^ j, pow_mem (mem_zpowers b) j, ht, ?_⟩
  rw [show 4 = 2 * 2 by decide, pow_mul, ht, hk]

/-- A normal index-two extension of a cyclic-times-two abelian base,
centralizing its second omega and self-centralizing over the base, either
contains a normal elementary eight or a normal abelian subgroup in which the
short-factor involution is a square. Normality is in the ambient group.

The explicit disjointness of the cyclic factors is unnecessary when the
first omega of the base is already given to have order four. -/
public theorem normal_cyclic_times_two_extension_obstruction
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (B R : Subgroup P) [B.Normal] [R.Normal] [IsMulCommutative B]
    (b z : P) (hz : orderOf z = 2)
    (hgenB : zpowers b ⊔ zpowers z = B) (hb4 : b ^ 4 ≠ 1)
    (hBR : B ≤ R) (hi : B.relIndex R = 2)
    (hcent : R ≤ centralizer (((omega B (p := 2) 2).map B.subtype : Subgroup P) : Set P))
    (hself : R ⊓ centralizer (B : Set P) ≤ B)
    (hWcentral : (omega₁ B (p := 2)).map B.subtype ≤ center P)
    (hWcard : Nat.card (omega₁ B (p := 2)) = 4) :
    (∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E) ∨
      (∃ H : Subgroup P, H.Normal ∧ IsMulCommutative H ∧ H ≤ R ∧
        ∃ h : H, (h : P) ^ 2 = z) := by
  obtain ⟨r, hrR, hrB, hr4⟩ := exists_outside_fourth_root_of_cyclic_two_base
    hP B R b z hz hgenB hBR hi hcent hself hWcentral
  have hr2 : r ^ 2 ∈ B :=
    (B.subgroupOf R).sq_mem_of_index_two hi (⟨r, hrR⟩ : R)
  obtain ⟨k, hk⟩ := cyclic_two_coordinates B b z hz hgenB hWcentral _ hr2
  have hz2 : z ^ 2 = 1 := hz ▸ pow_orderOf_eq_one z
  have hbB : b ∈ B := hgenB ▸ (le_sup_left : zpowers b ≤ zpowers b ⊔ zpowers z) (mem_zpowers b)
  have hzB : z ∈ B := hgenB ▸ (le_sup_right : zpowers z ≤ zpowers b ⊔ zpowers z) (mem_zpowers z)
  have hzC : z ∈ center P := hWcentral ⟨⟨z, hzB⟩, subset_closure (Subtype.ext hz2), rfl⟩
  have hk2 : (b ^ k) ^ 2 = 1 := by
    have hrr : (r ^ 2) ^ 2 = 1 := by simpa only [← pow_mul] using hr4
    rcases hk with hk | hk
    · simpa only [hk] using hrr
    · rw [hk, (show Commute (b ^ k) z from mem_center_iff.mp hzC _).mul_pow,
        hz2, mul_one] at hrr
      exact hrr
  obtain ⟨t, ht, ht2, ht4⟩ := root_of_binary_cyclic_power hP b hb4 k hk2
  have htB : t ∈ B := zpowers_le.mpr hbB ht
  have htr : Commute t r :=
    (commute_fourth_of_le_centralizer_omega_two B R hcent hrR htB ht4).symm
  let s := t⁻¹ * r
  have hsR : s ∈ R := R.mul_mem (R.inv_mem (hBR htB)) hrR
  have hsB : s ∉ B := by
    intro hs
    exact hrB ((B.mul_mem_cancel_left (B.inv_mem htB)).mp hs)
  have hs2 : s ^ 2 = (b ^ k)⁻¹ * r ^ 2 := by
    exact (htr.inv_left.mul_pow 2).trans (by rw [inv_pow, ht2])
  rcases hk with hk | hk
  · left
    have hs1 : s ^ 2 = 1 := by rw [hs2, hk, inv_mul_cancel]
    exact normal_elementary_eight_of_outside_involution_of_fourth_centralizer
      hP B R hBR hi hcent hWcentral hWcard hsR hsB hs1
  · right
    have hsz : s ^ 2 = z := by rw [hs2, hk, inv_mul_cancel_left]
    have hs4 : s ^ 4 = 1 := by
      rw [show 4 = 2 * 2 by decide, pow_mul, hsz, hz2]
    let O := omega R (p := 2) 2
    let H := O.map R.subtype
    let : O.Characteristic := omega_characteristic R 2
    let : IsMulCommutative O :=
      isMulCommutative_omega_two_of_index_two_fourth_centralizer hP B R hi hcent hWcentral
    have hsH : s ∈ H := ⟨⟨s, hsR⟩, subset_closure (Subtype.ext hs4), rfl⟩
    exact ⟨H, ConjAct.normal_of_characteristic_of_normal,
      map_isMulCommutative O R.subtype, map_subtype_le O, ⟨s, hsH⟩, hsz⟩

end Subgroup
