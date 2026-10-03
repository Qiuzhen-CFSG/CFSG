module

public import Theory.GroupTheory.PGroup.NormalFour

/-!
# Initial reductions for normal elementary eight-groups

A normal elementary subgroup of order at least eight in a finite two-group
contains a normal subgroup of order exactly eight. Thus the two versions of
the no-normal-eight hypothesis agree. If an elementary subgroup has rank at
least three but no normal elementary eight exists, the group is nonabelian,
has a normal four-group, and first omega of its center has order two or four.

The order bound comes from the characteristic omega subgroup of the center;
normal subgroups of intermediate orders give the extraction lemma. These are
the initial two-group reductions for Janko–Thompson, Math. Z. 113 (1970),
pp.385 and 394, saved as
`refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf`.
No ambient simplicity or local-solvability hypothesis is needed here.
-/

open Subgroup

namespace IsPGroup

/-- Extract an ambient normal elementary eight from a larger normal elementary subgroup. -/
public theorem exists_normal_eight_of_normal_elementary
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (A : Subgroup P) [A.Normal] [IsElementaryAbelian 2 A]
    (hA : 8 ≤ Nat.card A) :
    ∃ U : Subgroup P, U.Normal ∧ U ≤ A ∧ IsElementaryAbelian 2 U ∧ Nat.card U = 8 := by
  let : Fact (IsPGroup 2 P) := ⟨hP⟩
  obtain ⟨n, hn⟩ := (hP.to_subgroup A).exists_card_eq
  have hn3 : 3 ≤ n := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    simpa [← hn] using hA
  obtain ⟨U, hUn, hUA, hUcard⟩ :=
    exists_normal_subgroup_card_pow_of_normal (p := 2) A inferInstance hn 3 hn3
  have hUelem : IsElementaryAbelian 2 U := by
    let : IsElementaryAbelian 2 (U.subgroupOf A) :=
      { toIsMulCommutative := inferInstance
        exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x => by
          apply Subtype.ext
          exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
            (IsElementaryAbelian.exponent_dvd_p 2 A) x }
    rw [← Subgroup.map_subgroupOf_eq_of_le hUA]
    exact IsElementaryAbelian.map_subtype (p := 2) (H := U.subgroupOf A)
  exact ⟨U, hUn, hUA, hUelem, by simpa using hUcard⟩

/-- Without a normal elementary eight, first omega of the center has order two or four. -/
public theorem card_omega_center_two_or_four_of_no_normal_eight
    {P : Type*} [Group P] [Finite P] [Nontrivial P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E) :
    Nat.card (omega₁ (center P) (p := 2)) = 2 ∨
      Nat.card (omega₁ (center P) (p := 2)) = 4 := by
  let : Nontrivial (center P) := hP.center_nontrivial
  let O := omega₁ (center P) (p := 2)
  let : O.Characteristic := omega₁_characteristic _
  let : IsElementaryAbelian 2 O := IsElementaryAbelian.omega₁_of_isMulCommutative _
  let Z := O.map (center P).subtype
  have hZn : Z.Normal := ConjAct.normal_of_characteristic_of_normal
  have hZe : IsElementaryAbelian 2 Z := IsElementaryAbelian.map_subtype
  have hlt : Nat.card O < 8 := by
    by_contra! h
    exact hno ⟨Z, hZn, hZe, by simpa only [Z, card_map_of_injective (center P).subtype_injective] using h⟩
  have hdiv : 2 ∣ Nat.card (center P) :=
    (hP.to_subgroup _).card_eq_or_dvd.resolve_left (Nat.ne_of_gt Finite.one_lt_card)
  have hnb := omega₁_map_subtype_ne_bot (center P) 2 hdiv
  have hone : Nat.card O ≠ 1 := by
    intro hc
    have hb : O = ⊥ := Subgroup.card_eq_one.mp hc
    exact hnb (by rw [show omega₁ (center P) (p := 2) = ⊥ from hb, Subgroup.map_bot])
  obtain ⟨n, hn⟩ := ((hP.to_subgroup (center P)).to_subgroup O).exists_card_eq
  have hnlt : n < 3 := by
    apply (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
    simpa [← hn] using hlt
  change Nat.card O = 2 ∨ Nat.card O = 4
  interval_cases n
  · exact False.elim (hone (by simpa using hn))
  · exact Or.inl (by simpa using hn)
  · exact Or.inr (by simpa using hn)

/-- The exact-order and lower-bound formulations of normal elementary eight agree. -/
public theorem exists_normal_elementary_eight_iff
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P) :
    (∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E) ↔
      ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ Nat.card E = 8 := by
  constructor
  · rintro ⟨E, hEn, hEe, hE⟩
    let : E.Normal := hEn
    let : IsElementaryAbelian 2 E := hEe
    obtain ⟨U, hUn, _, hUe, hU⟩ := hP.exists_normal_eight_of_normal_elementary E hE
    exact ⟨U, hUn, hUe, hU⟩
  · rintro ⟨E, hEn, hEe, hE⟩
    exact ⟨E, hEn, hEe, by omega⟩

/-- An elementary subgroup of rank three with no normal elementary eight reduces
 to the two nonabelian normal-four branches, according to the central omega order. -/
public theorem normal_four_cases_of_rank_three_of_no_normal_eight
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (A : Subgroup P) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E) :
    ¬ IsMulCommutative P ∧
      (Nat.card (omega₁ (center P) (p := 2)) = 2 ∨
        Nat.card (omega₁ (center P) (p := 2)) = 4) ∧
      ∃ W : Subgroup P, W.Normal ∧ IsElementaryAbelian 2 W ∧ Nat.card W = 4 := by
  have hnonab : ¬ IsMulCommutative P := by
    intro hcomm
    let : IsMulCommutative P := hcomm
    exact hno ⟨A, inferInstance, inferInstance, hA⟩
  have hlarge := card_le_card_group A
  let : Nontrivial P := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  exact ⟨hnonab, hP.card_omega_center_two_or_four_of_no_normal_eight hno,
    hP.exists_normal_four_of_elementary_rank_three A hA⟩

end IsPGroup

