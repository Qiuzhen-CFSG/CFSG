module

public import Theory.GroupTheory.PGroup.NormalSubgroups
public import Theory.GroupTheory.PGroup.AbelianOmega
public import Theory.GroupTheory.PGroup.NormalAbelian
public import Theory.GroupTheory.PGroup.CyclicSelfCentralizerFour

/-!
# Normal four-groups in finite two-groups

A normal elementary abelian subgroup of order at least four contains an
ambient normal four-group, by the existence of normal subgroups of intermediate
prime-power orders. Consequently any noncyclic normal abelian subgroup gives
a normal four-group: its characteristic first omega subgroup has order at
least four.

To obtain existence from an elementary subgroup of rank at least three, choose
a self-centralizing normal abelian subgroup. The noncyclic case follows from
the omega argument; the cyclic case follows from the involutory conjugation
action on that subgroup.

This proves the two-group rank-three consequence of GLS, *The Classification
of the Finite Simple Groups*, volume 2, Chapter C, Lemma 10.11, using an
elementary alternative to its classification-based proof and Lemma 10.10.
-/

namespace IsPGroup

/-- Extract an ambient normal four-group from a normal elementary subgroup. -/
public theorem exists_normal_four_of_normal_elementary
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (A : Subgroup P) [A.Normal] [IsElementaryAbelian 2 A]
    (hA : 4 ≤ Nat.card A) :
    ∃ U : Subgroup P, U.Normal ∧ U ≤ A ∧ IsElementaryAbelian 2 U ∧ Nat.card U = 4 := by
  let : Fact (IsPGroup 2 P) := ⟨hP⟩
  obtain ⟨n, hn⟩ := (hP.to_subgroup A).exists_card_eq
  have hn2 : 2 ≤ n := by
    by_contra h
    have : n = 0 ∨ n = 1 := by omega
    rw [hn] at hA
    rcases this with rfl | rfl <;> norm_num at hA
  obtain ⟨U, hUn, hUA, hUcard⟩ :=
    exists_normal_subgroup_card_pow_of_normal (p := 2) A inferInstance hn 2 hn2
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

/-- A noncyclic normal abelian subgroup of a finite two-group contains a normal four-group. -/
public theorem exists_normal_four_of_normal_abelian_not_cyclic
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (A : Subgroup P) [A.Normal] [IsMulCommutative A] (hA : ¬ IsCyclic A) :
    ∃ U : Subgroup P, U.Normal ∧ U ≤ A ∧ IsElementaryAbelian 2 U ∧ Nat.card U = 4 := by
  let O := omega₁ A (p := 2)
  let : O.Characteristic := omega₁_characteristic A
  let : IsElementaryAbelian 2 O := IsElementaryAbelian.omega₁_of_isMulCommutative A
  let B := O.map A.subtype
  let : B.Normal := ConjAct.normal_of_characteristic_of_normal
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map_subtype
  have hOgt : 2 < Nat.card O := by
    by_contra h
    exact hA ((hP.to_subgroup A).isCyclic_of_card_omega_one_le_two (le_of_not_gt h))
  have hBcard : 4 ≤ Nat.card B := by
    rw [show Nat.card B = Nat.card O from Subgroup.card_subtype A O]
    rcases ((hP.to_subgroup A).to_subgroup O).card_eq_or_dvd with h | h
    · omega
    · omega
  obtain ⟨U, hUn, hUB, hUe, hUc⟩ := hP.exists_normal_four_of_normal_elementary B hBcard
  exact ⟨U, hUn, hUB.trans (Subgroup.map_subtype_le O), hUe, hUc⟩

/-- A finite two-group containing an elementary abelian subgroup of rank at
least three has a normal elementary abelian subgroup of order four. -/
public theorem exists_normal_four_of_elementary_rank_three
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (E : Subgroup P) [IsElementaryAbelian 2 E] (hE : 8 ≤ Nat.card E) :
    ∃ U : Subgroup P, U.Normal ∧ IsElementaryAbelian 2 U ∧ Nat.card U = 4 := by
  obtain ⟨A, hAN, hAcomm, hAC⟩ := exists_normal_abelian_selfCentralizing hP
  let _ : A.Normal := hAN
  let _ : IsMulCommutative A := hAcomm
  by_cases hcyc : IsCyclic A
  · let _ : IsCyclic A := hcyc
    exact exists_normal_four_of_cyclic_selfcentralizer hP A hAC E hE
  · obtain ⟨U, hUN, -, hUelem, hUcard⟩ :=
      exists_normal_four_of_normal_abelian_not_cyclic hP A hcyc
    exact ⟨U, hUN, hUelem, hUcard⟩

end IsPGroup
