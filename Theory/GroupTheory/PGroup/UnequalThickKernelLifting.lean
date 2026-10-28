module

public import Theory.GroupTheory.PGroup.NormalEightInvolutionLift
public import Mathlib.Data.ZMod.Basic

/-!
# Involution lifting in the fourth-root action kernel

Let `D` be normal, abelian and self-centralizing in a finite two-group with
central omega of order four and no normal elementary subgroup of order at
least eight. Suppose every involution of `D` has a square root in `D`.
Then every coset modulo `D` represented in the first omega of the kernel of
conjugation on fourth roots has an involution representative in that kernel.
In particular, this applies to two cyclic factors both of order at least four.

An involution fixing fourth roots inverts each of its displacements on `D`.
Such displacements have square one, hence lie in the central omega subgroup.
Consequently the actions of two kernel involutions commute, so their product
has square in `D`. This square is again inverted by either involution and has
square one. A square root in `D` commutes with both involutions and corrects
the product to an involution in the same coset. Closure induction finishes.
The ambient conjugation image need not be abelian.

Source: the fourth-root and cyclic lifting arguments in MacWilliams,
*On 2-groups with no normal abelian subgroups of rank 3*, Trans. AMS 150 (1970),
§1.2, DOI 10.1090/S0002-9947-1970-0276324-3. The product correction above
extends the central-coset argument of `NormalEightInvolutionLift`.
-/

open Subgroup

namespace IsPGroup

private theorem square_of_inverted
    {H : Type*} [Group H] (hH : IsPGroup 2 H) (f : MulAut H)
    (hfix : ∀ x : H, x ^ 4 = 1 → f x = x)
    (x : H) (hinv : f x = x⁻¹) : x ^ 2 = 1 := by
  have aux : ∀ k (y : H), y ^ (2 ^ k) = 1 → f y = y⁻¹ → y ^ 2 = 1 := by
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
  obtain ⟨k, hk⟩ := hH x
  exact aux k x hk hinv

private theorem root_zmod (n : ℕ) (hn : 2 ≤ n)
    (x : Multiplicative (ZMod (2 ^ n))) (hx : x ^ 2 = 1) :
    ∃ y : Multiplicative (ZMod (2 ^ n)), y ^ 2 = x := by
  have hxx : x.toAdd + x.toAdd = 0 := by simpa [pow_two] using congrArg Multiplicative.toAdd hx
  have hxneg : -x.toAdd = x.toAdd := neg_eq_iff_add_eq_zero.mpr hxx
  rcases (ZMod.neg_eq_self_iff x.toAdd).mp hxneg with hz | hv
  · exact ⟨1, by simpa using congrArg Multiplicative.ofAdd hz.symm⟩
  have hn4 : 2 ^ n = 4 * 2 ^ (n - 2) := by
    rw [show n = 2 + (n - 2) from by omega, pow_add]
    congr 2
    omega
  have hv' : x.toAdd.val = 2 * 2 ^ (n - 2) := by omega
  refine ⟨Multiplicative.ofAdd (2 ^ (n - 2) : ZMod (2 ^ n)), ?_⟩
  rw [pow_two]
  change (2 ^ (n - 2) : ZMod (2 ^ n)) + 2 ^ (n - 2) = x.toAdd
  rw [← two_mul, ← ZMod.natCast_zmod_val x.toAdd, hv']
  simp

private theorem kernel_fix {P : Type*} [Group P]
    (D : Subgroup P) [D.Normal] {a : P}
    (ha : a ∈ (omegaTwoConjugation D).ker) (d : D) (hd : d ^ 4 = 1) :
    Commute a (d : P) := by
  have hdO : d ∈ omega D (p := 2) 2 := subset_closure (by simpa using hd)
  have he := congrArg (fun t : MulAut (omega D (p := 2) 2) =>
    ((t ⟨d, hdO⟩ : D) : P)) (MonoidHom.mem_ker.mp ha)
  change a * (d : P) * a⁻¹ = (d : P) at he
  exact mul_inv_eq_iff_eq_mul.mp he

private theorem displacement_sq {P : Type*} [Group P]
    (hP : IsPGroup 2 P) (D : Subgroup P) [D.Normal]
    {a : P} (haK : a ∈ (omegaTwoConjugation D).ker) (ha : a ^ 2 = 1)
    (d : D) : (MulAut.conjNormal a d * d⁻¹) ^ 2 = 1 := by
  have haa : a * a = 1 := by simpa only [pow_two] using ha
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_left haa
  apply square_of_inverted (hP.to_subgroup D) (MulAut.conjNormal a)
    (fun x hx => Subtype.ext (by
      change a * (x : P) * a⁻¹ = x
      rw [(kernel_fix D haK x hx).eq, mul_inv_cancel_right]))
  apply Subtype.ext
  change a * (a * (d : P) * a⁻¹ * (d : P)⁻¹) * a⁻¹ =
    (a * (d : P) * a⁻¹ * (d : P)⁻¹)⁻¹
  simp only [mul_inv_rev, inv_inv, hai]
  simp only [← mul_assoc, haa, one_mul]

private theorem displacement_central {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P)
    (hno : ¬ ∃ U : Subgroup P, U.Normal ∧ IsElementaryAbelian 2 U ∧ 8 ≤ Nat.card U)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    {a : P} (haK : a ∈ (omegaTwoConjugation D).ker) (ha : a ^ 2 = 1)
    (d : D) : a * (d : P) * a⁻¹ * (d : P)⁻¹ ∈ center P := by
  let O := omega₁ D (p := 2)
  let : O.Characteristic := omega₁_characteristic _
  let : IsElementaryAbelian 2 O := IsElementaryAbelian.omega₁_of_isMulCommutative _
  let ZD := O.map D.subtype
  let : ZD.Normal := ConjAct.normal_of_characteristic_of_normal
  let : IsElementaryAbelian 2 ZD := IsElementaryAbelian.map_subtype
  apply map_subtype_le (omega₁ (center P) (p := 2))
  apply normal_elementary_le_omega_center_of_no_normal_eight hno hZ ZD
  exact ⟨MulAut.conjNormal a d * d⁻¹,
    subset_closure (by simpa using displacement_sq hP D haK ha d), rfl⟩

private theorem involution_actions_commute {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P)
    (hno : ¬ ∃ U : Subgroup P, U.Normal ∧ IsElementaryAbelian 2 U ∧ 8 ≤ Nat.card U)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    {a b : P} (haK : a ∈ (omegaTwoConjugation D).ker) (ha : a ^ 2 = 1)
    (hbK : b ∈ (omegaTwoConjugation D).ker) (hb : b ^ 2 = 1) :
    Commute (MulAut.conjNormal (H := D) a) (MulAut.conjNormal b) := by
  apply MulEquiv.ext
  intro d
  apply Subtype.ext
  let da := a * (d : P) * a⁻¹ * (d : P)⁻¹
  let db := b * (d : P) * b⁻¹ * (d : P)⁻¹
  have hda : da ∈ center P := displacement_central hP hno hZ D haK ha d
  have hdb : db ∈ center P := displacement_central hP hno hZ D hbK hb d
  have hea : a * (d : P) * a⁻¹ = da * d := by dsimp [da]; group
  have heb : b * (d : P) * b⁻¹ = db * d := by dsimp [db]; group
  change a * (b * (d : P) * b⁻¹) * a⁻¹ = b * (a * (d : P) * a⁻¹) * b⁻¹
  calc
    a * (b * (d : P) * b⁻¹) * a⁻¹ = db * (a * (d : P) * a⁻¹) := by
      rw [heb, ← mul_assoc a, mem_center_iff.mp hdb a]
      group
    _ = db * (da * d) := by rw [hea]
    _ = da * (db * d) := by rw [← mul_assoc, mem_center_iff.mp hda db, mul_assoc]
    _ = da * (b * (d : P) * b⁻¹) := by rw [heb]
    _ = b * (a * (d : P) * a⁻¹) * b⁻¹ := by
      rw [hea, ← mul_assoc b, mem_center_iff.mp hda b]
      group

private theorem product_square_mem {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P)
    (hno : ¬ ∃ U : Subgroup P, U.Normal ∧ IsElementaryAbelian 2 U ∧ 8 ≤ Nat.card U)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hD : centralizer (D : Set P) ≤ D)
    {a b : P} (haK : a ∈ (omegaTwoConjugation D).ker) (ha : a ^ 2 = 1)
    (hbK : b ∈ (omegaTwoConjugation D).ker) (hb : b ^ 2 = 1) :
    (a * b) ^ 2 ∈ D := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using ha)
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hb)
  have hc : MulAut.conjNormal (H := D) ((a * b) ^ 2) = 1 := by
    have he : (a * b) ^ 2 = a * b * a⁻¹ * b⁻¹ := by simp only [hai, hbi, pow_two, mul_assoc]
    rw [he, map_mul, map_mul, map_mul, map_inv, map_inv,
      (involution_actions_commute hP hno hZ D haK ha hbK hb).eq,
      mul_inv_cancel_right, mul_inv_cancel]
  apply hD
  intro d hd
  have he := congrArg (fun t : MulAut D => (t ⟨d, hd⟩ : P)) hc
  change (a * b) ^ 2 * d * ((a * b) ^ 2)⁻¹ = d at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

private theorem product_fourth {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P)
    (hno : ¬ ∃ U : Subgroup P, U.Normal ∧ IsElementaryAbelian 2 U ∧ 8 ≤ Nat.card U)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hD : centralizer (D : Set P) ≤ D)
    {a b : P} (haK : a ∈ (omegaTwoConjugation D).ker) (ha : a ^ 2 = 1)
    (hbK : b ∈ (omegaTwoConjugation D).ker) (hb : b ^ 2 = 1) :
    ((a * b) ^ 2) ^ 2 = 1 := by
  let c : D := ⟨(a * b) ^ 2, product_square_mem hP hno hZ D hD haK ha hbK hb⟩
  have haa : a * a = 1 := by simpa only [pow_two] using ha
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_left haa
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hb)
  have hc : c ^ 2 = 1 := by
    apply square_of_inverted (hP.to_subgroup D) (MulAut.conjNormal a)
      (fun x hx => Subtype.ext (by
        change a * (x : P) * a⁻¹ = x
        rw [(kernel_fix D haK x hx).eq, mul_inv_cancel_right]))
    apply Subtype.ext
    change a * (a * b) ^ 2 * a⁻¹ = ((a * b) ^ 2)⁻¹
    simp only [pow_two, mul_inv_rev, hai, hbi]
    simp only [← mul_assoc, haa, one_mul]
  exact congrArg Subtype.val hc

private theorem D_le_kernel {P : Type*} [Group P]
    (D : Subgroup P) [D.Normal] [IsMulCommutative D] : D ≤ (omegaTwoConjugation D).ker := by
  intro d hd
  apply MonoidHom.mem_ker.mpr
  ext x
  change d * (x : P) * d⁻¹ = (x : P)
  rw [← D.le_centralizer hd (x : P) x.val.property, mul_inv_cancel_right]

private theorem correct_product {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P)
    (hno : ¬ ∃ U : Subgroup P, U.Normal ∧ IsElementaryAbelian 2 U ∧ 8 ≤ Nat.card U)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hD : centralizer (D : Set P) ≤ D)
    (hroot : ∀ d : D, d ^ 2 = 1 → ∃ t : D, t ^ 2 = d)
    {a b : P} (haK : a ∈ (omegaTwoConjugation D).ker) (ha : a ^ 2 = 1)
    (hbK : b ∈ (omegaTwoConjugation D).ker) (hb : b ^ 2 = 1) :
    ∃ c ∈ (omegaTwoConjugation D).ker, c ^ 2 = 1 ∧
      QuotientGroup.mk' D c = QuotientGroup.mk' D a * QuotientGroup.mk' D b := by
  let d : D := ⟨(a * b) ^ 2, product_square_mem hP hno hZ D hD haK ha hbK hb⟩
  have hd : d ^ 2 = 1 := Subtype.ext (product_fourth hP hno hZ D hD haK ha hbK hb)
  obtain ⟨t, ht⟩ := hroot d hd
  have ht4 : t ^ 4 = 1 := by
    calc
      t ^ 4 = (t ^ 2) ^ 2 := by rw [← pow_mul]
      _ = 1 := by rw [ht, hd]
  have hct : Commute (a * b) (t : P) :=
    (kernel_fix D haK t ht4).mul_left (kernel_fix D hbK t ht4)
  refine ⟨a * b * (t : P)⁻¹, (omegaTwoConjugation D).ker.mul_mem
    ((omegaTwoConjugation D).ker.mul_mem haK hbK)
    ((omegaTwoConjugation D).ker.inv_mem (D_le_kernel D t.property)), ?_, ?_⟩
  · rw [hct.inv_right.mul_pow, inv_pow]
    have htP : (t : P) ^ 2 = (a * b) ^ 2 := congrArg Subtype.val ht
    rw [htP, mul_inv_cancel]
  · have htq : QuotientGroup.mk' D (t : P) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr t.property
    simp only [map_mul, map_inv, htq, inv_one, mul_one]

/-- If every involution of a normal abelian self-centralizing subgroup has a
square root there, first omega of the fourth-root action kernel has involution
representatives modulo that subgroup. -/
public theorem kernel_involution_cosets_of_square_roots {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P)
    (hno : ¬ ∃ U : Subgroup P, U.Normal ∧ IsElementaryAbelian 2 U ∧ 8 ≤ Nat.card U)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hD : centralizer (D : Set P) ≤ D)
    (hroot : ∀ d : D, d ^ 2 = 1 → ∃ t : D, t ^ 2 = d) :
    ∀ x ∈ (omega₁ (omegaTwoConjugation D).ker (p := 2)).map
        (omegaTwoConjugation D).ker.subtype,
      ∃ a ∈ (omegaTwoConjugation D).ker, a ^ 2 = 1 ∧ x * a⁻¹ ∈ D := by
  let K := (omegaTwoConjugation D).ker
  let q := QuotientGroup.mk' D
  have hlift : ∀ y ∈ omega₁ K (p := 2),
      ∃ a ∈ K, a ^ 2 = 1 ∧ q (y : P) = q a := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      exact ⟨y, y.property, congrArg Subtype.val hy, rfl⟩
    | one => exact ⟨1, K.one_mem, by simp, by simp⟩
    | mul y z _ _ hy hz =>
      obtain ⟨a, haK, ha, hya⟩ := hy
      obtain ⟨b, hbK, hb, hzb⟩ := hz
      obtain ⟨c, hcK, hc, hqc⟩ := correct_product hP hno hZ D hD hroot haK ha hbK hb
      refine ⟨c, hcK, hc, ?_⟩
      change q ((y : P) * (z : P)) = q c
      rw [map_mul, hya, hzb]
      exact hqc.symm
    | inv y _ hy =>
      obtain ⟨a, haK, ha, hya⟩ := hy
      refine ⟨a⁻¹, K.inv_mem haK, by rw [inv_pow, ha, inv_one], ?_⟩
      change q (y : P)⁻¹ = q a⁻¹
      rw [map_inv, map_inv, hya]
  rintro x ⟨y, hy, rfl⟩
  obtain ⟨a, haK, ha, hya⟩ := hlift y hy
  refine ⟨a, haK, ha, (QuotientGroup.eq_one_iff _).mp ?_⟩
  change q ((y : P) * a⁻¹) = 1
  rw [map_mul, map_inv, hya, mul_inv_cancel]

/-- Fourth-root kernel cosets lift to involutions when the abelian subgroup is
a product of unequal cyclic two-groups, both of order at least four. -/
public theorem kernel_involution_cosets_of_unequal_thick_factors {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P)
    (hno : ¬ ∃ U : Subgroup P, U.Normal ∧ IsElementaryAbelian 2 U ∧ 8 ≤ Nat.card U)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hD : centralizer (D : Set P) ≤ D)
    (n m : ℕ) (hm : 2 ≤ m) (hmn : m < n)
    (e : D ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ m)))) :
    ∀ x ∈ (omega₁ (omegaTwoConjugation D).ker (p := 2)).map
        (omegaTwoConjugation D).ker.subtype,
      ∃ a ∈ (omegaTwoConjugation D).ker, a ^ 2 = 1 ∧ x * a⁻¹ ∈ D := by
  apply kernel_involution_cosets_of_square_roots hP hno hZ D hD
  intro d hd
  have he : (e d) ^ 2 = 1 := by rw [← map_pow, hd, map_one]
  obtain ⟨u, hu⟩ := root_zmod n (by omega) (e d).1 (congrArg Prod.fst he)
  obtain ⟨v, hv⟩ := root_zmod m hm (e d).2 (congrArg Prod.snd he)
  refine ⟨e.symm (u, v), ?_⟩
  apply e.injective
  rw [map_pow, e.apply_symm_apply]
  exact Prod.ext hu hv

end IsPGroup
