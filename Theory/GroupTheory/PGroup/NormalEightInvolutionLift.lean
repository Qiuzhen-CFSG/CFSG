module

public import Theory.GroupTheory.PGroup.NormalEightAbelianReduction

/-!
# Detecting elementary actions on fourth roots

An involution whose conjugates differ from it by central involutions lies in
an elementary normal subgroup. In the absence of normal elementary eights,
with a central omega four, that involution is central.

More generally, suppose an involution is central modulo a normal abelian
subgroup and fixes its fourth roots of unity. It inverts each conjugation
displacement. In a two-group, an inverted element whose fourth roots are
fixed has square one. Thus all displacements lie in the central omega four,
and the first observation applies.

Consequently, if a self-centralizing normal abelian subgroup has abelian
conjugation image, restriction to its second omega detects the full action
of every elementary binary subgroup. This is useful for a cyclic factor
with a direct factor of order two. The abelian-image hypothesis is essential
to the argument; no assertion about arbitrary unequal factors is made here.

Source: the cyclic-subgroup lifting arguments in MacWilliams, *On 2-groups
with no normal abelian subgroups of rank 3*, Trans. AMS 150 (1970), §1.2,
especially (v) and (xvii), DOI 10.1090/S0002-9947-1970-0276324-3.
-/

open Subgroup

private theorem square_eq_one_of_inverted_of_fixed_fourth_roots
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

/-- An involution with central elementary conjugation displacements is central
when all normal elementary subgroups lie in the central omega four. -/
public theorem Subgroup.mem_center_of_square_eq_one_of_displacement_in_omega_center {P : Type*} [Group P] [Finite P]
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4)
    (a : P) (ha : a ^ 2 = 1)
    (hc : ∀ g : P, g * a * g⁻¹ * a⁻¹ ∈
      (omega₁ (center P) (p := 2)).map (center P).subtype) : a ∈ center P := by
  let Z := (omega₁ (center P) (p := 2)).map (center P).subtype
  let : IsElementaryAbelian 2 (omega₁ (center P) (p := 2)) :=
    IsElementaryAbelian.omega₁_of_isMulCommutative _
  let : IsElementaryAbelian 2 Z := IsElementaryAbelian.map_subtype
  let : IsElementaryAbelian 2 (zpowers a) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one ha
  have hZc : Z ≤ center P := map_subtype_le _
  let E := Z ⊔ zpowers a
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.sup_of_le_centralizer
    (show zpowers a ≤ centralizer (Z : Set P) from fun x _ z hz =>
      (mem_center_iff.mp (hZc hz) x).symm)
  let : E.Normal := ⟨by
    intro x hx g
    have hle : E ≤ E.comap (MulAut.conj g).toMonoidHom := by
      apply sup_le
      · intro z hz
        change g * z * g⁻¹ ∈ E
        rw [mem_center_iff.mp (hZc hz) g, mul_inv_cancel_right]
        exact (le_sup_left : Z ≤ E) hz
      · apply zpowers_le.mpr
        change g * a * g⁻¹ ∈ E
        have hm := E.mul_mem ((le_sup_left : Z ≤ E) (hc g))
          ((le_sup_right : zpowers a ≤ E) (mem_zpowers a))
        simpa only [inv_mul_cancel_right] using hm
    exact hle hx⟩
  have haE : a ∈ E := (le_sup_right : zpowers a ≤ E) (mem_zpowers a)
  exact hZc (normal_elementary_le_omega_center_of_no_normal_eight hno hZ E haE)


/-- A central coset represented by an involution fixing fourth roots lifts to
a central involution under the no-normal-eight hypothesis. -/
public theorem IsPGroup.mem_center_of_square_eq_one_of_central_mod_abelian_of_fourth_roots
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (a : P) (ha : a ^ 2 = 1)
    (hmod : ∀ g : P, g * a * g⁻¹ * a⁻¹ ∈ D)
    (hfix : ∀ d : D, d ^ 4 = 1 → Commute a (d : P)) : a ∈ center P := by
  let O := omega₁ D (p := 2)
  let : O.Characteristic := omega₁_characteristic _
  let : IsElementaryAbelian 2 O := IsElementaryAbelian.omega₁_of_isMulCommutative _
  let ZD := O.map D.subtype
  let : ZD.Normal := ConjAct.normal_of_characteristic_of_normal
  let : IsElementaryAbelian 2 ZD := IsElementaryAbelian.map_subtype
  have hle := normal_elementary_le_omega_center_of_no_normal_eight hno hZ ZD
  apply Subgroup.mem_center_of_square_eq_one_of_displacement_in_omega_center hno hZ a ha
  intro g
  let d : D := ⟨g * a * g⁻¹ * a⁻¹, hmod g⟩
  have haa : a * a = 1 := by simpa only [pow_two] using ha
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_left haa
  have hinv : MulAut.conjNormal a d = d⁻¹ := by
    apply Subtype.ext
    change a * (g * a * g⁻¹ * a⁻¹) * a⁻¹ = (g * a * g⁻¹ * a⁻¹)⁻¹
    simp only [mul_inv_rev, inv_inv, hai]
    simp only [mul_assoc, haa, mul_one]
  have hd : d ^ 2 = 1 := square_eq_one_of_inverted_of_fixed_fourth_roots
    (hP.to_subgroup D) (MulAut.conjNormal a)
    (fun x hx => Subtype.ext (by
      change a * (x : P) * a⁻¹ = x
      rw [(hfix x hx).eq, mul_inv_cancel_right])) d hinv
  apply hle
  exact ⟨d, subset_closure (by simpa using hd), rfl⟩

/-- Ambient conjugation restricted to the second binary omega subgroup. -/
@[expose] public noncomputable def Subgroup.omegaTwoConjugation {P : Type*} [Group P]
    (D : Subgroup P) [D.Normal] : P →* MulAut (omega D (p := 2) 2) := by
  letI : (omega D (p := 2) 2).Characteristic := omega_characteristic D 2
  exact (MulAut.characteristic (omega D (p := 2) 2)).comp MulAut.conjNormal

/-- For an abelian conjugation image, fourth roots detect the action of every
elementary binary subgroup, without an ambient elementary rank assumption. -/
public theorem IsPGroup.card_conj_image_le_omega_two_image_of_abelian_action {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hD : centralizer (D : Set P) ≤ D)
    (hcomm : ∀ g a : P, Commute (MulAut.conjNormal (H := D) g) (MulAut.conjNormal a))
    (A : Subgroup P) [IsElementaryAbelian 2 A] :
    Nat.card ((MulAut.conjNormal : P →* MulAut D).comp A.subtype).range ≤
      Nat.card ((omegaTwoConjugation D).comp A.subtype).range := by
  let f := (MulAut.conjNormal : P →* MulAut D).comp A.subtype
  let r := (omegaTwoConjugation D).comp A.subtype
  have hker : r.ker ≤ f.ker := by
    intro a ha
    have hac : (a : P) ∈ center P := by
      apply IsPGroup.mem_center_of_square_eq_one_of_central_mod_abelian_of_fourth_roots hP hno hZ D a
        (elemPow_eq_one_of_isElementaryAbelian (a : P) a.property)
      · intro g
        apply hD
        have hc : MulAut.conjNormal (H := D) (g * (a : P) * g⁻¹ * (a : P)⁻¹) = 1 := by
          simp only [map_mul, map_inv]
          rw [(hcomm g a).eq, mul_inv_cancel_right, mul_inv_cancel]
        intro d hd
        have he := congrArg (fun t : MulAut D => (t ⟨d, hd⟩ : P)) hc
        change (g * (a : P) * g⁻¹ * (a : P)⁻¹) * d *
          (g * (a : P) * g⁻¹ * (a : P)⁻¹)⁻¹ = d at he
        exact (mul_inv_eq_iff_eq_mul.mp he).symm
      · intro d hd
        have hdO : d ∈ omega D (p := 2) 2 := subset_closure (by simpa using hd)
        have he := congrArg (fun t : MulAut (omega D (p := 2) 2) =>
          ((t ⟨d, hdO⟩ : D) : P)) (MonoidHom.mem_ker.mp ha)
        change (a : P) * (d : P) * (a : P)⁻¹ = (d : P) at he
        exact mul_inv_eq_iff_eq_mul.mp he
    apply MonoidHom.mem_ker.mpr
    ext d
    change (a : P) * (d : P) * (a : P)⁻¹ = (d : P)
    rw [← mem_center_iff.mp hac (d : P), mul_inv_cancel_right]
  have hi := Subgroup.index_antitone hker
  simpa only [index_ker] using hi
