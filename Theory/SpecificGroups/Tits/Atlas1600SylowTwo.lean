module

public import Theory.SpecificGroups.Tits.Atlas1600R5
public import Theory.SpecificGroups.Tits.Atlas1600SylowTwoEnumeration
public import Theory.SpecificGroups.Tits.Atlas1600SylowTwoCenterCertificate
public import Theory.SpecificGroups.Tits.Atlas1600Order
public import Theory.GroupTheory.SylowCenterNormal

/-!
# The Parrott Sylow-two subgroup and even-order normal subgroups

The eight `s` generators span a subgroup of order 2048 and index 8775, hence
a Sylow 2-subgroup. Its center consists of the identity and `r5 = s1 * s5²`:
the complete normal-form enumeration and a kernel-checked point test exclude
all other elements, and pointwise certificates show that `r5` is central.

An even-order normal subgroup intersects this Sylow subgroup nontrivially.
The intersection is normal in the 2-group, so it meets the center nontrivially
and contains `r5`.

Source: Parrott (1972), p. 683, transcribed in
`refs/original/n-group-global/parrott-tits-presentation.md`, and the supplied
Atlas degree-1600 permutations.
-/

namespace Tits

open Atlas1600ParrottData
open Atlas1600SylowTwoCenterCertificate

local notation "S" => atlas1600SylowTwoSubgroup
local notation "s1" => atlas1600ParrottAssignment ParrottGenerator.s1
local notation "s2" => atlas1600ParrottAssignment ParrottGenerator.s2
local notation "s3" => atlas1600ParrottAssignment ParrottGenerator.s3
local notation "s4" => atlas1600ParrottAssignment ParrottGenerator.s4
local notation "s5" => atlas1600ParrottAssignment ParrottGenerator.s5
local notation "s6" => atlas1600ParrottAssignment ParrottGenerator.s6
local notation "s7" => atlas1600ParrottAssignment ParrottGenerator.s7
local notation "s8" => atlas1600ParrottAssignment ParrottGenerator.s8

private theorem val_mul (a b : Atlas1600Group) : (a * b).val = a.val * b.val := rfl
private theorem val_pow (a : Atlas1600Group) (n : Nat) : (a ^ n).val = a.val ^ n := rfl
private theorem val_one : (1 : Atlas1600Group).val = 1 := rfl

private theorem r5_val : atlas1600R5.val = s1Perm * s5Perm ^ 2 := by
  simp only [atlas1600R5_eq, val_mul, val_pow, atlas1600ParrottAssignment_val, permutation]

private theorem normalForm_zero : atlas1600SylowTwoNormalForm 0 = 1 := by
  norm_num [atlas1600SylowTwoNormalForm_eq]

private theorem normalForm_sixty_five : atlas1600SylowTwoNormalForm 65 = atlas1600R5 := by
  norm_num [atlas1600SylowTwoNormalForm_eq, atlas1600R5_eq]

/-- The distinguished word belongs to the eight-generator subgroup. -/
public theorem atlas1600R5_mem_sylowTwo : atlas1600R5 ∈ S := by
  rw [← normalForm_sixty_five]
  exact atlas1600SylowTwoNormalForm_mem 65

/-- The distinguished word is nonidentity. -/
public theorem atlas1600R5_ne_one : atlas1600R5 ≠ 1 := by
  intro h
  apply central_word_ne_one
  simpa only [r5_val, val_one] using congrArg (fun x : Atlas1600Group => x.val) h

private theorem central_test (x : S) (hx : x ∈ Subgroup.center S) :
    testCentral x.val.val = true := by
  have hpoint (i : ParrottGenerator)
      (hi : atlas1600ParrottAssignment i ∈ ({s8, s7, s6, s5, s4, s3, s2, s1} : Set Atlas1600Group)) :
      x.val.val (permutation i 0) = permutation i (x.val.val 0) := by
    have hmem : atlas1600ParrottAssignment i ∈ S := by
      rw [atlas1600SylowTwoSubgroup_eq]
      exact Subgroup.subset_closure hi
    have h := Subgroup.mem_center_iff.mp hx ⟨atlas1600ParrottAssignment i, hmem⟩
    have hval := congrArg (fun y : S => y.val.val) h
    change (atlas1600ParrottAssignment i * x.val).val =
      (x.val * atlas1600ParrottAssignment i).val at hval
    simp only [val_mul, atlas1600ParrottAssignment_val] at hval
    exact (congrArg (fun g : Equiv.Perm (Fin 1600) => g 0) hval).symm
  simp only [testCentral, Bool.and_eq_true, beq_iff_eq]
  repeat' apply And.intro
  · simpa only [permutation] using hpoint .s1 (by simp)
  · simpa only [permutation] using hpoint .s2 (by simp)
  · simpa only [permutation] using hpoint .s3 (by simp)
  · simpa only [permutation] using hpoint .s4 (by simp)
  · simpa only [permutation] using hpoint .s5 (by simp)
  · simpa only [permutation] using hpoint .s6 (by simp)
  · simpa only [permutation] using hpoint .s7 (by simp)
  · simpa only [permutation] using hpoint .s8 (by simp)

private theorem central_eq (x : S) (hx : x ∈ Subgroup.center S) :
    x.val = 1 ∨ x.val = atlas1600R5 := by
  obtain ⟨n, hn⟩ := atlas1600SylowTwoNormalForm_surjective x.property
  have ht := central_test x hx
  rw [← hn, atlas1600SylowTwoNormalForm_val] at ht
  change testCentral (Atlas1600SylowTwoCertificate.normalForm n) = true at ht
  rcases central_candidates n ht with rfl | rfl
  · exact Or.inl (hn.symm.trans normalForm_zero)
  · exact Or.inr (hn.symm.trans normalForm_sixty_five)

/-- The distinguished word is central in the eight-generator subgroup. -/
public theorem atlas1600R5_mem_center_sylowTwo :
    (⟨atlas1600R5, atlas1600R5_mem_sylowTwo⟩ : S) ∈ Subgroup.center S := by
  have hle : S ≤ Subgroup.centralizer {atlas1600R5} := by
    rw [atlas1600SylowTwoSubgroup_eq]
    apply (Subgroup.closure_le _).mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    change x ∈ Subgroup.centralizer {atlas1600R5}
    rw [Subgroup.mem_centralizer_singleton_iff]
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · apply Subtype.ext
      simpa only [val_mul, r5_val, atlas1600ParrottAssignment_val, permutation, generator]
        using (central_word_commutes (7 : Fin 8)).symm
    · apply Subtype.ext
      simpa only [val_mul, r5_val, atlas1600ParrottAssignment_val, permutation, generator]
        using (central_word_commutes (6 : Fin 8)).symm
    · apply Subtype.ext
      simpa only [val_mul, r5_val, atlas1600ParrottAssignment_val, permutation, generator]
        using (central_word_commutes (5 : Fin 8)).symm
    · apply Subtype.ext
      simpa only [val_mul, r5_val, atlas1600ParrottAssignment_val, permutation, generator]
        using (central_word_commutes (4 : Fin 8)).symm
    · apply Subtype.ext
      simpa only [val_mul, r5_val, atlas1600ParrottAssignment_val, permutation, generator]
        using (central_word_commutes (3 : Fin 8)).symm
    · apply Subtype.ext
      simpa only [val_mul, r5_val, atlas1600ParrottAssignment_val, permutation, generator]
        using (central_word_commutes (2 : Fin 8)).symm
    · apply Subtype.ext
      simpa only [val_mul, r5_val, atlas1600ParrottAssignment_val, permutation, generator]
        using (central_word_commutes (1 : Fin 8)).symm
    · apply Subtype.ext
      simpa only [val_mul, r5_val, atlas1600ParrottAssignment_val, permutation, generator]
        using (central_word_commutes (0 : Fin 8)).symm
  apply Subgroup.mem_center_iff.mpr
  intro x
  apply Subtype.ext
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle x.property)

/-- The center consists exactly of the identity and the distinguished word. -/
public theorem atlas1600SylowTwo_mem_center_iff (x : S) :
    x ∈ Subgroup.center S ↔ x.val = 1 ∨ x.val = atlas1600R5 := by
  constructor
  · exact central_eq x
  · rintro (h | h)
    · have hx : x = 1 := Subtype.ext h
      rw [hx]
      exact (Subgroup.center S).one_mem
    · have hx : x = ⟨atlas1600R5, atlas1600R5_mem_sylowTwo⟩ := Subtype.ext h
      rw [hx]
      exact atlas1600R5_mem_center_sylowTwo

/-- The index of the eight-generator subgroup is odd. -/
public theorem atlas1600SylowTwoSubgroup_index : (S).index = 8775 := by
  have h := (S).card_mul_index
  rw [atlas1600SylowTwoSubgroup_card, atlas1600Group_card] at h
  omega

/-- The eight-generator subgroup, packaged as a Sylow 2-subgroup. -/
public def atlas1600SylowTwo : Sylow 2 Atlas1600Group := by
  have hp : IsPGroup 2 S := IsPGroup.of_card (n := 11)
    (by simpa using atlas1600SylowTwoSubgroup_card)
  exact hp.toSylow
    (by rw [atlas1600SylowTwoSubgroup_index]; decide)

public theorem atlas1600SylowTwo_coe :
    (atlas1600SylowTwo : Subgroup Atlas1600Group) = S := by rfl

/-- Every even-order normal subgroup of the Atlas group contains `r5`. -/
public theorem atlas1600R5_mem_normal_of_even (N : Subgroup Atlas1600Group)
    [N.Normal] (heven : 2 ∣ Nat.card N) : atlas1600R5 ∈ N := by
  apply atlas1600SylowTwo.center_generator_mem_normal atlas1600R5 _ N heven
  change ∀ x : S, x ∈ Subgroup.center S → x ≠ 1 → x.val = atlas1600R5
  intro x hx hne
  rcases (atlas1600SylowTwo_mem_center_iff x).mp hx with h | h
  · exact (hne (Subtype.ext h)).elim
  · exact h

end Tits
