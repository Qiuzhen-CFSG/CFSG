module

public import Theory.GroupTheory.PGroup.NormalEightInvolutionLift
public import Theory.GroupTheory.PGroup.NormalSubgroups
public import Mathlib.Data.ZMod.Basic

/-!
# Fourth-root detection with a normal omega four

The fourth-root kernel's involutions have commuting actions on the abelian
base: their displacements are involutions, hence are fixed by every kernel
element. If involutions of the base have square roots there, products can be
corrected by fourth roots to lift first-omega cosets to involutions.

This adapts the proof in `UnequalThickKernelLifting` without assuming the omega
four is central in the ambient group. A central coset represented by an
involution fixing fourth roots gives a normal elementary overgroup of the
normal four. The absence of normal elementary eights then excludes that coset.

Source: MacWilliams, *On 2-groups with no normal abelian subgroups of rank 3*,
Trans. AMS 150 (1970), §1.2, DOI 10.1090/S0002-9947-1970-0276324-3;
Janko–Thompson, Math. Z. 113 (1970), Theorem 1.1, printed p.385.
-/

open Subgroup

namespace NormalFourFourthRoot

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

private theorem involution_actions_commute {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    {a b : P} (haK : a ∈ (omegaTwoConjugation D).ker) (ha : a ^ 2 = 1)
    (hbK : b ∈ (omegaTwoConjugation D).ker) (hb : b ^ 2 = 1) :
    Commute (MulAut.conjNormal (H := D) a) (MulAut.conjNormal b) := by
  have hfix (c : P) (hc : c ∈ (omegaTwoConjugation D).ker)
      (d : D) (hd : d ^ 2 = 1) : MulAut.conjNormal c d = d := by
    apply Subtype.ext
    change c * (d : P) * c⁻¹ = d
    rw [(kernel_fix D hc d (by rw [show 4 = 2 * 2 from rfl, pow_mul, hd, one_pow])).eq,
      mul_inv_cancel_right]
  apply MulEquiv.ext
  intro d
  let da : D := MulAut.conjNormal a d * d⁻¹
  let db : D := MulAut.conjNormal b d * d⁻¹
  have hea : MulAut.conjNormal a d = da * d := by simp [da]
  have heb : MulAut.conjNormal b d = db * d := by simp [db]
  have hda : MulAut.conjNormal b da = da := hfix b hbK da (displacement_sq hP D haK ha d)
  have hdb : MulAut.conjNormal a db = db := hfix a haK db (displacement_sq hP D hbK hb d)
  change MulAut.conjNormal a (MulAut.conjNormal b d) =
    MulAut.conjNormal b (MulAut.conjNormal a d)
  calc
    _ = db * (da * d) := by rw [heb, map_mul, hdb, hea]
    _ = da * (db * d) := by
      rw [← mul_assoc, IsMulCommutative.is_comm.comm db da, mul_assoc]
    _ = _ := by rw [hea, map_mul, hda, heb]

private theorem product_square_mem {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P)
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
      (involution_actions_commute hP D haK ha hbK hb).eq,
      mul_inv_cancel_right, mul_inv_cancel]
  apply hD
  intro d hd
  have he := congrArg (fun t : MulAut D => (t ⟨d, hd⟩ : P)) hc
  change (a * b) ^ 2 * d * ((a * b) ^ 2)⁻¹ = d at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

private theorem product_fourth {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hD : centralizer (D : Set P) ≤ D)
    {a b : P} (haK : a ∈ (omegaTwoConjugation D).ker) (ha : a ^ 2 = 1)
    (hbK : b ∈ (omegaTwoConjugation D).ker) (hb : b ^ 2 = 1) :
    ((a * b) ^ 2) ^ 2 = 1 := by
  let c : D := ⟨(a * b) ^ 2, product_square_mem hP D hD haK ha hbK hb⟩
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
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hD : centralizer (D : Set P) ≤ D)
    (hroot : ∀ d : D, d ^ 2 = 1 → ∃ t : D, t ^ 2 = d)
    {a b : P} (haK : a ∈ (omegaTwoConjugation D).ker) (ha : a ^ 2 = 1)
    (hbK : b ∈ (omegaTwoConjugation D).ker) (hb : b ^ 2 = 1) :
    ∃ c ∈ (omegaTwoConjugation D).ker, c ^ 2 = 1 ∧
      QuotientGroup.mk' D c = QuotientGroup.mk' D a * QuotientGroup.mk' D b := by
  let d : D := ⟨(a * b) ^ 2, product_square_mem hP D hD haK ha hbK hb⟩
  have hd : d ^ 2 = 1 := Subtype.ext (product_fourth hP D hD haK ha hbK hb)
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

/-- If involutions of a normal abelian self-centralizing subgroup have square
roots there, first omega of the fourth-root action kernel has involution
representatives modulo that subgroup. No normal-eight exclusion is needed. -/
public theorem kernel_involution_cosets_of_square_roots {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P)
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
      obtain ⟨c, hcK, hc, hqc⟩ := correct_product hP D hD hroot haK ha hbK hb
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


/-- An involution centralizing a normal four and having all conjugation
displacements in it belongs to the four when normal eights are absent. -/
public theorem mem_four_of_involution_displacements
    {P : Type*} [Group P] [Finite P]
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (a : P) (ha : a ^ 2 = 1) (hac : a ∈ centralizer (W : Set P))
    (hc : ∀ g : P, g * a * g⁻¹ * a⁻¹ ∈ W) : a ∈ W := by
  let : IsElementaryAbelian 2 (zpowers a) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one ha
  let E := W ⊔ zpowers a
  let : IsElementaryAbelian 2 E :=
    IsElementaryAbelian.sup_of_le_centralizer (zpowers_le.mpr hac)
  let : E.Normal := ⟨by
    intro x hx g
    have hle : E ≤ E.comap (MulAut.conj g).toMonoidHom := by
      apply sup_le
      · intro w hw
        exact (le_sup_left : W ≤ E) ((inferInstance : W.Normal).conj_mem w hw g)
      · apply zpowers_le.mpr
        change g * a * g⁻¹ ∈ E
        have hm := E.mul_mem ((le_sup_left : W ≤ E) (hc g))
          ((le_sup_right : zpowers a ≤ E) (mem_zpowers a))
        simpa only [inv_mul_cancel_right] using hm
    exact hle hx⟩
  have hlt : Nat.card E < 8 := by
    by_contra! h
    exact hno ⟨E, inferInstance, inferInstance, h⟩
  have hdiv : 4 ∣ Nat.card E := hW ▸ card_dvd_of_le (show W ≤ E from le_sup_left)
  have heq : W = E := eq_of_le_of_card_ge le_sup_left (by omega)
  exact heq ▸ (le_sup_right : zpowers a ≤ E) (mem_zpowers a)

/-- A central coset involution fixing fourth roots lies in the normal omega
four. No centrality of that four in the ambient group is required. -/
public theorem mem_four_of_central_coset_fixing_fourth_roots
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hO : (omega₁ D (p := 2)).map D.subtype = W)
    (a : P) (ha : a ^ 2 = 1)
    (hmod : ∀ g : P, g * a * g⁻¹ * a⁻¹ ∈ D)
    (hfix : ∀ d : D, d ^ 4 = 1 → Commute a (d : P)) : a ∈ W := by
  have hWD : W ≤ D := hO ▸ map_subtype_le _
  apply mem_four_of_involution_displacements hno W hW a ha
  · intro w hw
    have hw2 : w ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian w hw
    exact (hfix ⟨w, hWD hw⟩ (Subtype.ext (by
      change w ^ 4 = 1
      rw [show 4 = 2 * 2 from rfl, pow_mul, hw2, one_pow]))).eq.symm
  · intro g
    let d : D := ⟨g * a * g⁻¹ * a⁻¹, hmod g⟩
    have haa : a * a = 1 := by simpa only [pow_two] using ha
    have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_left haa
    have hinv : MulAut.conjNormal a d = d⁻¹ := by
      apply Subtype.ext
      change a * (g * a * g⁻¹ * a⁻¹) * a⁻¹ = (g * a * g⁻¹ * a⁻¹)⁻¹
      simp only [mul_inv_rev, inv_inv, hai]
      simp only [mul_assoc, haa, mul_one]
    have hd : d ^ 2 = 1 := square_of_inverted (hP.to_subgroup D)
      (MulAut.conjNormal a) (fun x hx => Subtype.ext (by
        change a * (x : P) * a⁻¹ = x
        rw [(hfix x hx).eq, mul_inv_cancel_right])) d hinv
    rw [← hO]
    exact ⟨d, subset_closure (by simpa using hd), rfl⟩

/-- An elementary conjugation image contains no nonidentity automorphism
which is central in the full automorphism group and fixes fourth roots. -/
public theorem conj_image_central_fourth_root_kernel_trivial
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hDC : centralizer (D : Set P) ≤ D)
    (hO : (omega₁ D (p := 2)).map D.subtype = W)
    (B : Subgroup P) [IsElementaryAbelian 2 B]
    (f : MulAut D)
    (hf : f ∈ ((MulAut.conjNormal : P →* MulAut D).comp B.subtype).range)
    (hc : f ∈ center (MulAut D)) (hfix : ∀ d : D, d ^ 4 = 1 → f d = d) :
    f = 1 := by
  obtain ⟨a, rfl⟩ := hf
  change MulAut.conjNormal (H := D) (a : P) ∈ center (MulAut D) at hc
  have haW : (a : P) ∈ W := by
    apply mem_four_of_central_coset_fixing_fourth_roots hP hno W hW D hO a
      (elemPow_eq_one_of_isElementaryAbelian (a : P) a.property)
    · intro g
      apply hDC
      have he : MulAut.conjNormal (H := D) (g * (a : P) * g⁻¹ * (a : P)⁻¹) = 1 := by
        simp only [map_mul, map_inv]
        rw [mem_center_iff.mp hc (MulAut.conjNormal g), mul_inv_cancel_right, mul_inv_cancel]
      intro d hd
      have hh := congrArg (fun t : MulAut D => (t ⟨d, hd⟩ : P)) he
      change (g * (a : P) * g⁻¹ * (a : P)⁻¹) * d *
        (g * (a : P) * g⁻¹ * (a : P)⁻¹)⁻¹ = d at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    · intro d hd
      have he := congrArg Subtype.val (hfix d hd)
      change (a : P) * (d : P) * (a : P)⁻¹ = (d : P) at he
      exact mul_inv_eq_iff_eq_mul.mp he
  have haD : (a : P) ∈ D := (hO ▸ map_subtype_le _) haW
  ext d
  change (a : P) * (d : P) * (a : P)⁻¹ = d
  rw [(D.le_centralizer haD d d.property).symm, mul_inv_cancel_right]

private theorem normal_le_of_involution_cosets
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hO : (omega₁ D (p := 2)).map D.subtype = W)
    (N : Subgroup P) [N.Normal]
    (hlift : ∀ x ∈ N, ∃ a : P, a ^ 2 = 1 ∧
      x * a⁻¹ ∈ D ∧ ∀ d : D, d ^ 4 = 1 → Commute a (d : P)) : N ≤ D := by
  classical
  by_contra hND
  let q := QuotientGroup.mk' D
  let U := N.map q
  let : U.Normal := inferInstance
  have hUne : U ≠ ⊥ := by
    intro h
    apply hND
    simpa [q] using (map_eq_bot_iff (f := q) N).mp h
  let : Nontrivial U := (nontrivial_iff_ne_bot U).mpr hUne
  let : Fact (IsPGroup 2 (P ⧸ D)) := ⟨hP.to_quotient D⟩
  obtain ⟨b, hbne, hbcenter⟩ := exists_nontrivial_center_mem_normal U (p := 2)
  obtain ⟨x, hx, hxb⟩ := b.property
  obtain ⟨a, ha, hxa, hfix⟩ := hlift x hx
  have hqa : q a = q x := by
    have he : q (x * a⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr hxa
    exact (mul_inv_eq_one.mp (by simpa only [map_mul, map_inv] using he)).symm
  have haW : a ∈ W := by
    apply mem_four_of_central_coset_fixing_fourth_roots hP hno W hW D hO a ha _ hfix
    intro g
    apply (QuotientGroup.eq_one_iff _).mp
    change q (g * a * g⁻¹ * a⁻¹) = 1
    simp only [map_mul, map_inv, hqa, hxb]
    rw [mem_center_iff.mp hbcenter (q g), mul_inv_cancel_right, mul_inv_cancel]
  have haD : a ∈ D := (hO ▸ map_subtype_le _) haW
  apply hbne
  apply Subtype.ext
  exact hxb.symm.trans (hqa.symm.trans ((QuotientGroup.eq_one_iff _).mpr haD))

/-- When involutions of a self-centralizing abelian base have square roots,
fourth-root restriction detects elementary actions, assuming only a normal
omega four and absence of normal elementary eights. -/
public theorem card_conj_image_le_fourth_root_image_of_square_roots
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hDC : centralizer (D : Set P) ≤ D)
    (hO : (omega₁ D (p := 2)).map D.subtype = W)
    (hroot : ∀ d : D, d ^ 2 = 1 → ∃ t : D, t ^ 2 = d)
    (B : Subgroup P) [IsElementaryAbelian 2 B] :
    Nat.card ((MulAut.conjNormal : P →* MulAut D).comp B.subtype).range ≤
      Nat.card ((omegaTwoConjugation D).comp B.subtype).range := by
  let K := (omegaTwoConjugation D).ker
  let O := omega₁ K (p := 2)
  let : O.Characteristic := omega₁_characteristic K
  let N := O.map K.subtype
  let : N.Normal := ConjAct.normal_of_characteristic_of_normal
  have hND : N ≤ D := by
    apply normal_le_of_involution_cosets hP hno W hW D hO N
    intro x hx
    obtain ⟨a, haK, ha, hxa⟩ := kernel_involution_cosets_of_square_roots hP D hDC hroot x hx
    exact ⟨a, ha, hxa, kernel_fix D haK⟩
  let f := (MulAut.conjNormal : P →* MulAut D).comp B.subtype
  let r := (omegaTwoConjugation D).comp B.subtype
  have hker : r.ker ≤ f.ker := by
    intro a ha
    have haK : (a : P) ∈ K := ha
    have haN : (a : P) ∈ N := by
      refine ⟨⟨a, haK⟩, subset_closure ?_, rfl⟩
      change (⟨(a : P), haK⟩ : K) ^ (2 ^ 1) = 1
      apply Subtype.ext
      exact elemPow_eq_one_of_isElementaryAbelian (a : P) a.property
    apply MonoidHom.mem_ker.mpr
    ext d
    change (a : P) * (d : P) * (a : P)⁻¹ = (d : P)
    rw [(D.le_centralizer (hND haN) d d.property).symm, mul_inv_cancel_right]
  simpa only [index_ker] using Subgroup.index_antitone hker

/-- Thick rank-two bases satisfy the square-root premise of fourth-root
detection. This also covers equal factors. -/
public theorem card_conj_image_le_fourth_root_image_of_thick_factors
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hDC : centralizer (D : Set P) ≤ D)
    (hO : (omega₁ D (p := 2)).map D.subtype = W)
    (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (e : D ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ m))))
    (B : Subgroup P) [IsElementaryAbelian 2 B] :
    Nat.card ((MulAut.conjNormal : P →* MulAut D).comp B.subtype).range ≤
      Nat.card ((omegaTwoConjugation D).comp B.subtype).range := by
  apply card_conj_image_le_fourth_root_image_of_square_roots hP hno W hW D hDC hO _ B
  intro d hd
  have he : (e d) ^ 2 = 1 := by rw [← map_pow, hd, map_one]
  obtain ⟨u, hu⟩ := root_zmod n hn (e d).1 (congrArg Prod.fst he)
  obtain ⟨v, hv⟩ := root_zmod m hm (e d).2 (congrArg Prod.snd he)
  refine ⟨e.symm (u, v), ?_⟩
  apply e.injective
  rw [map_pow, e.apply_symm_apply]
  exact Prod.ext hu hv

end NormalFourFourthRoot
