module

public import Theory.GroupTheory.PGroup.NormalEightCriticalSubgroup
public import Theory.GroupTheory.PGroup.CriticalSubgroupAutDetection
public import Theory.GroupTheory.PGroup.ClassTwoThreeInvolutionExponent
public import Theory.GroupTheory.CharacteristicInvolutionProfile

/-!
# A fixed involution in a critical subgroup with nonelementary center

In the central-four, no-normal-eight setting a nonabelian critical subgroup
with nonelementary center cannot have transitive automorphisms on its three
involutions. Indeed the class-two exponent theorem and the special-group
calculation would make its center elementary. The automorphism orbit is a
nonconstant invariant on these three points, so it has a singleton fiber.
This gives a characteristic subgroup of order two.

Restriction also detects a non-two-group automorphism group on the critical
subgroup. These are reductions toward the odd-automorphism argument in
MacWilliams, Trans. AMS 150 (1970), §3, pp.366–369. They assert neither a
quaternion decomposition nor transitivity from odd automorphism detection.
-/

open Subgroup

namespace IsCriticalPSubgroup

/-- Transitivity on critical involutions forces the critical center to be elementary. -/
public theorem elementary_center_of_transitive_involutions
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    {C : Subgroup P} (hC : IsCriticalPSubgroup 2 C)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4)
    (hnonab : ¬ IsMulCommutative C)
    (htrans : ∀ x y : C, orderOf x = 2 → orderOf y = 2 →
      ∃ a : MulAut C, a x = y) : IsElementaryAbelian 2 (center C) := by
  let : IsElementaryAbelian 2 (C ⧸ center C) := hC.quotient_elementary
  have hclass : commutator C ≤ center C :=
    Normal.quotient_commutative_iff_commutator_le.mp inferInstance
  have hcentral := hC.square_one_mem_center hno hZ
  have hexp := (hP.to_subgroup C).exponent_four_of_class_two_of_transitive_three_involutions
    hnonab hcentral (hC.card_involutions_eq_three hno hZ) htrans hclass
  exact ((hP.to_subgroup C).special_of_exponent_four_of_transitive_involutions
    hnonab hcentral htrans hexp).2.2.1

/-- A nonelementary critical center singles out a characteristic involution. -/
public theorem exists_characteristic_two_of_nonelementary_center
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    {C : Subgroup P} (hC : IsCriticalPSubgroup 2 C)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4)
    (hnonab : ¬ IsMulCommutative C)
    (hbad : ¬ IsElementaryAbelian 2 (center C)) :
    ∃ K : Subgroup C, K.Characteristic ∧ Nat.card K = 2 := by
  classical
  have hnot : ¬ ∀ x y : C, orderOf x = 2 → orderOf y = 2 →
      ∃ a : MulAut C, a x = y := fun ht =>
    hbad (hC.elementary_center_of_transitive_involutions hP hno hZ hnonab ht)
  push Not at hnot
  obtain ⟨x, y, hx, hy, hxy⟩ := hnot
  let O := omega₁ C (p := 2)
  let : O.Characteristic := omega₁_characteristic C
  have hOc : O ≤ center C := by
    apply (closure_le _).mpr
    intro z hz
    exact hC.square_one_mem_center hno hZ z (by simpa using hz)
  let : IsMulCommutative O := ⟨⟨fun x y =>
    Subtype.ext (mem_center_iff.mp (hOc y.property) x)⟩⟩
  let : IsElementaryAbelian 2 O := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun z => by
      have hm := mem_map_of_mem C.subtype z.property
      rw [hC.omega_one_map_eq_center hno hZ] at hm
      let : IsElementaryAbelian 2 (omega₁ (center P) (p := 2)) :=
        IsElementaryAbelian.omega₁_of_isMulCommutative _
      let : IsElementaryAbelian 2 ((omega₁ (center P) (p := 2)).map (center P).subtype) :=
        IsElementaryAbelian.map_subtype
      exact Subtype.ext (Subtype.ext (elemPow_eq_one_of_isElementaryAbelian _ hm)) }
  let orbit (x : C) : Set C := {y | ∃ a : MulAut C, a x = y}
  have hinv (a : MulAut C) (x : C) : orbit (a x) = orbit x := by
    ext y
    constructor
    · rintro ⟨b, hb⟩
      exact ⟨b * a, hb⟩
    · rintro ⟨b, hb⟩
      refine ⟨b * a⁻¹, ?_⟩
      simpa using hb
  apply exists_characteristic_two_of_nonconstant_invariant_on_four O
    (hC.card_omega_one_eq_four hno hZ) orbit hinv
  have hmem (z : C) (hz : orderOf z = 2) : z ∈ O :=
    subset_closure (by simpa only [Set.mem_ofPred_eq, pow_one, hz] using pow_orderOf_eq_one z)
  refine ⟨x, hmem x hx, (orderOf_eq_prime_iff.mp hx).2,
    y, hmem y hy, (orderOf_eq_prime_iff.mp hy).2, ?_⟩
  intro he
  have hym : y ∈ orbit y := ⟨1, rfl⟩
  rw [← he] at hym
  obtain ⟨a, ha⟩ := hym
  exact hxy a ha

end IsCriticalPSubgroup
