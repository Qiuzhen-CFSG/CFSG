module

public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Tactic.Group
/-!
# Transport between three involution-bearing cosets

For an equivariant homomorphism with elementary binary kernel, the square-one
lifts of a square-one image form a torsor for a centralizer in the kernel.
Their cardinality is therefore prime to three. A fixed image under a
three-group has a fixed square-one lift. Consequently, if all fixed
square-one elements belong to the kernel, an order-three actor is transitive
on any nonempty set of at most five nonidentity square-one images. Their number is a positive
multiple of three, and hence is exactly three.
-/

open Subgroup MulAction

namespace Theory.GroupAction

private theorem square_one_fiber_card
    {P R : Type*} [Group P] [Finite P] [Group R]
    (f : P →* R) [IsElementaryAbelian 2 f.ker]
    (x : P) (hx : x ^ 2 = 1) :
    Nat.card {u : P // u ^ 2 = 1 ∧ f u = f x} =
      Nat.card (f.ker ⊓ centralizer ({x} : Set P) : Subgroup P) := by
  let C := f.ker ⊓ centralizer ({x} : Set P)
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hx)
  let e : C ≃ {u : P // u ^ 2 = 1 ∧ f u = f x} := {
    toFun c := ⟨c * x, by
      constructor
      · rw [(show Commute (c : P) x from mem_centralizer_singleton_iff.mp c.property.2).mul_pow,
          elemPow_eq_one_of_isElementaryAbelian (c : P) c.property.1, hx, one_mul]
      · rw [map_mul, (show f (c : P) = 1 from c.property.1), one_mul]⟩
    invFun u := ⟨u * x⁻¹, by
      have hk : (u : P) * x⁻¹ ∈ f.ker := by
        change f ((u : P) * x⁻¹) = 1
        rw [map_mul, map_inv, u.property.2, mul_inv_cancel]
      refine ⟨hk, mem_centralizer_singleton_iff.mpr ?_⟩
      have hc2 : ((u : P) * x⁻¹) ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian _ hk
      have hui : (u : P)⁻¹ = u := inv_eq_of_mul_eq_one_right
        (by simpa [pow_two] using u.property.1)
      have hci := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hc2)
      rw [mul_inv_rev, inv_inv, hui, hxi] at hci
      change (u : P) * x⁻¹ * x = x * ((u : P) * x⁻¹)
      simp only [hxi, ← mul_assoc, hci]⟩
    left_inv c := Subtype.ext (by group)
    right_inv u := Subtype.ext (by group) }
  exact (Nat.card_congr e).symm

private theorem exists_fixed_square_one_of_fixed_image
    {A P R : Type*} [Group A] [Group P] [Finite P] [Group R]
    [MulDistribMulAction A P] [MulDistribMulAction A R]
    (f : P →* R) [IsElementaryAbelian 2 f.ker]
    (hA : IsPGroup 3 A) (hker : ¬ 3 ∣ Nat.card f.ker)
    (hequiv : ∀ a : A, ∀ u : P, f (a • u) = a • f u)
    (x : P) (hx : x ^ 2 = 1) (hfixed : ∀ a : A, a • f x = f x) :
    ∃ u : P, u ^ 2 = 1 ∧ f u = f x ∧ ∀ a : A, a • u = u := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let T := {u : P // u ^ 2 = 1 ∧ f u = f x}
  let : MulAction A T := {
    smul a u := ⟨a • (u : P), by
      constructor
      · rw [← smul_pow', u.property.1, smul_one]
      · rw [hequiv, u.property.2, hfixed]⟩
    one_smul u := Subtype.ext (one_smul A (u : P))
    mul_smul a b u := Subtype.ext (mul_smul a b (u : P)) }
  have hc : ¬ 3 ∣ Nat.card T := by
    rw [show Nat.card T = Nat.card (f.ker ⊓ centralizer ({x} : Set P) : Subgroup P) from
      square_one_fiber_card f x hx]
    exact fun hd => hker (hd.trans (card_dvd_of_le (show
      f.ker ⊓ centralizer ({x} : Set P) ≤ f.ker from inf_le_left)))
  obtain ⟨u, hu⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card T hc
  exact ⟨u, u.property.1, u.property.2, fun a => congrArg Subtype.val (hu a)⟩

/-- An order-three actor transports any two nonidentity square-one images
when there are at most five such images and no fixed square-one lift survives. -/
public theorem three_involution_cosets_transitive
    {A P R : Type*} [Group A] [Finite A] [Group P] [Finite P]
    [Group R] [Finite R] [MulDistribMulAction A P] [MulDistribMulAction A R]
    (f : P →* R) [IsElementaryAbelian 2 f.ker]
    (hA : Nat.card A = 3) (hker : ¬ 3 ∣ Nat.card f.ker)
    (hequiv : ∀ a : A, ∀ u : P, f (a • u) = a • f u)
    (hfixed : ∀ u : P, u ^ 2 = 1 → (∀ a : A, a • u = u) → f u = 1)
    (hcount : Nat.card {r : R // r ≠ 1 ∧ ∃ u : P, u ^ 2 = 1 ∧ f u = r} ≤ 5)
    (x y : P) (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) (hfx : f x ≠ 1) (hfy : f y ≠ 1) :
    ∃ a : A, f (a • x) = f y := by
  classical
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 A := IsPGroup.of_card (n := 1) (by simpa using hA)
  let S := {r : R // r ≠ 1 ∧ ∃ u : P, u ^ 2 = 1 ∧ f u = r}
  let : MulAction A S := {
    smul a r := ⟨a • (r : R), by
      refine ⟨?_, ?_⟩
      · intro hh
        apply r.property.1
        have he := congrArg (a⁻¹ • ·) hh
        simpa only [inv_smul_smul, smul_one] using he
      · obtain ⟨u, hu, hur⟩ := r.property.2
        exact ⟨a • u, by rw [← smul_pow', hu, smul_one], by rw [hequiv, hur]⟩⟩
    one_smul r := Subtype.ext (one_smul A (r : R))
    mul_smul a b r := Subtype.ext (mul_smul a b (r : R)) }
  let sx : S := ⟨f x, hfx, x, hx, rfl⟩
  let sy : S := ⟨f y, hfy, y, hy, rfl⟩
  have hnfix (s : S) : s ∉ fixedPoints A S := by
    intro hh
    obtain ⟨u, hu, hus⟩ := s.property.2
    have hfix : ∀ a : A, a • f u = f u := by
      intro a
      rw [hus]
      exact congrArg Subtype.val (hh a)
    obtain ⟨t, ht, htu, htfix⟩ := exists_fixed_square_one_of_fixed_image f hp hker hequiv u hu hfix
    exact s.property.1 (hus.symm.trans (htu.symm.trans (hfixed t ht htfix)))
  have hthree : Nat.card S ≤ 3 := by
    have he : fixedPoints A S = ∅ := Set.eq_empty_iff_forall_notMem.mpr hnfix
    have hh := hp.card_modEq_card_fixedPoints S
    have hz : Nat.card (fixedPoints A S) = 0 := by simp [he]
    rw [hz] at hh
    change Nat.card S % 3 = 0 % 3 at hh
    change Nat.card S ≤ 5 at hcount
    omega
  let : Fintype S := Fintype.ofFinite S
  let : Fintype (orbit A sx) := Fintype.ofFinite _
  have hone : Nat.card (orbit A sx) ≠ 1 := by
    rw [Nat.card_eq_fintype_card]
    exact fun hc => hnfix sx (mem_fixedPoints_iff_card_orbit_eq_one.mpr hc)
  have horb : 3 ≤ Nat.card (orbit A sx) := by
    obtain ⟨n, hn⟩ := hp.card_orbit sx
    rw [hn] at hone ⊢
    cases n with
    | zero => simp at hone
    | succ n =>
      have hh : 0 < 3 ^ n := pow_pos (by decide) n
      rw [pow_succ]
      omega
  have hsurj : Function.Surjective (fun t : orbit A sx => (t : S)) := by
    apply (Nat.bijective_iff_injective_and_card _).mpr ?_ |>.2
    refine ⟨Subtype.val_injective, le_antisymm ?_ ?_⟩
    · exact Nat.card_le_card_of_injective _ Subtype.val_injective
    · exact hthree.trans horb
  obtain ⟨t, ht⟩ := hsurj sy
  obtain ⟨a, ha⟩ := t.property
  refine ⟨a, ?_⟩
  exact (hequiv a x).trans (congrArg Subtype.val (ha.trans ht))

/-- In an eight-element image, a subgroup image of order at least four
whose involutions lie in a subgroup image of order at most two leaves at
most five nonidentity images of square-one elements. -/
public theorem square_one_images_le_five
    {P R : Type*} [Group P] [Finite P] [Group R] [Finite R]
    (f : P →* R) (B C : Subgroup P) (hFB : f.ker ≤ B)
    (hR : Nat.card R = 8) (hB : 4 ≤ Nat.card (B.map f))
    (hC : Nat.card (C.map f) ≤ 2)
    (hBC : ∀ u ∈ B, u ^ 2 = 1 → u ∈ C) :
    Nat.card {r : R // r ≠ 1 ∧ ∃ u : P, u ^ 2 = 1 ∧ f u = r} ≤ 5 := by
  classical
  let S : Set R := {r | r ≠ 1 ∧ ∃ u : P, u ^ 2 = 1 ∧ f u = r}
  have hsub : S ⊆ ((Set.univ \ (B.map f : Set R)) ∪ ((C.map f : Set R) \ {1})) := by
    rintro r ⟨hr, u, hu, rfl⟩
    by_cases hb : f u ∈ B.map f
    · right
      refine ⟨mem_map_of_mem f (hBC u ?_ hu), hr⟩
      obtain ⟨b, hb, hbu⟩ := hb
      have hk : b⁻¹ * u ∈ f.ker := by
        change f (b⁻¹ * u) = 1
        rw [map_mul, map_inv, hbu, inv_mul_cancel]
      simpa only [mul_inv_cancel_left] using B.mul_mem hb (hFB hk)
    · exact Or.inl ⟨Set.mem_univ _, hb⟩
  have hc := (Set.ncard_le_ncard hsub).trans (Set.ncard_union_le _ _)
  rw [Set.ncard_sdiff (Set.subset_univ _), Set.ncard_univ,
    Set.ncard_sdiff_singleton_of_mem (C.map f).one_mem] at hc
  change Nat.card S ≤ Nat.card R - Nat.card (B.map f) + (Nat.card (C.map f) - 1) at hc
  change Nat.card S ≤ 5
  rw [hR] at hc
  omega

end Theory.GroupAction
