module

public import CFSG.Quasithin.ChapterB.Section03.Offenders.Defs
public import CFSG.Quasithin.ChapterB.Section03.Offenders.FixedTests
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Six.Representatives
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Six.Structure.Basic
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Six.Structure.Reduction
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Six.Structure.DLattice
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Six.Structure.ExceptionalLattice

/-!
# Degree-six subgroup structure for Proposition B.3.2

The concrete representatives have certified orders and binary ranks. Their join
`D ⊔ exceptional` is the underlying subgroup of an actual Sylow 2-subgroup of
`S₆`. Sylow conjugacy and the element tables reduce the elementary abelian
subgroup classification to the certified subgroup lattices of `D` and
`exceptional`. Combining those lattices gives the ten elementary abelian
representatives, the seven case-(a) and fourteen case-(b) members in the Sylow
subgroup, and uniqueness there of `D` and of the even case-(b) member.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
1 March 2004 manuscript, printed pp. 83–85.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterB.Offenders.Six
open Representation.BinaryOffender

/-- Every nontrivial elementary abelian 2-subgroup of `S₆` belongs to one of
these ten ambient conjugacy types. This follows from Sylow conjugacy and the
two exhaustive order-eight subgroup lattices. -/
theorem elementaryTwo_conjugacy {A : Subgroup Perm} (hA : IsElementaryTwo A) :
    IsConjugateTo A (disjointTranspositions 6 1) ∨
    IsConjugateTo A (disjointTranspositions 6 2) ∨ IsConjugateTo A (D 6) ∨
    IsConjugateTo A (exceptional 6 (by decide)) ∨
    IsConjugateTo A (evenPart 6) ∨ IsConjugateTo A plus ∨
    IsConjugateTo A double ∨ IsConjugateTo A triple ∨
    IsConjugateTo A klein ∨ IsConjugateTo A twisted := by
  obtain ⟨B, hB, hBD | hBE, hAB⟩ := exists_conjugate_le_D_or_exceptional hA
  · rcases subgroup_D_conjugacy hBD hB.1 with h | h | h | h | h | h | h
    all_goals have h := hAB.trans h
    all_goals tauto
  · rcases exceptional_subgroup_conjugacy hBE hB.1 with h | h | h | h | h | h | h
    all_goals have h := hAB.trans h
    all_goals tauto

/-- The ten-representative list characterizes the elementary abelian
2-subgroups, in both directions. -/
theorem isElementaryTwo_iff (A : Subgroup Perm) : IsElementaryTwo A ↔
    IsConjugateTo A (disjointTranspositions 6 1) ∨
    IsConjugateTo A (disjointTranspositions 6 2) ∨ IsConjugateTo A (D 6) ∨
    IsConjugateTo A (exceptional 6 (by decide)) ∨
    IsConjugateTo A (evenPart 6) ∨ IsConjugateTo A plus ∨
    IsConjugateTo A double ∨ IsConjugateTo A triple ∨
    IsConjugateTo A klein ∨ IsConjugateTo A twisted := by
  refine ⟨elementaryTwo_conjugacy, ?_⟩
  rintro (h | h | h | h | h | h | h | h | h | h)
  · exact h.isElementaryTwo (isElementaryTwo_disjointTranspositions 1 (by decide))
  · exact h.isElementaryTwo (isElementaryTwo_disjointTranspositions 2 (by decide))
  · exact h.isElementaryTwo (isElementaryTwo_disjointTranspositions 3 (by decide))
  · exact h.isElementaryTwo isElementaryTwo_exceptional
  · exact h.isElementaryTwo isElementaryTwo_evenPart
  · exact h.isElementaryTwo isElementaryTwo_plus
  · exact h.isElementaryTwo isElementaryTwo_double
  · exact h.isElementaryTwo isElementaryTwo_triple
  · exact h.isElementaryTwo isElementaryTwo_klein
  · exact h.isElementaryTwo isElementaryTwo_twisted

/-- Inside the exceptional subgroup, case (b) consists of exactly five members. -/
theorem caseBFamily_le_exceptional_iff {A : Subgroup Perm}
    (hA : A ≤ exceptional 6 (by decide)) :
    CaseBFamily 6 (by decide) A ↔
      A = last ∨ A = plus ∨ A = mixedSecond ∨ A = mixedThird ∨
      A = exceptional 6 (by decide) := by
  rw [caseBFamily_iff]
  exact exceptional_good_iff hA

/-- Every case-(a) member in the Sylow subgroup is already in `D`. -/
theorem caseAFamily_le_D_of_le_sylowCarrier {A : Subgroup Perm}
    (hA : CaseAFamily 6 A) (hAT : A ≤ sylowCarrier) : A ≤ D 6 := by
  rcases elementary_le_D_or_exceptional (caseBFamily_isElementaryTwo (Or.inl hA)) hAT
      with hD | hE
  · exact hD
  · rw [(exceptional_caseAFamily_iff hE).1 hA]
    exact last_le_plus.trans plus_le_D

/-- The exact seven case-(a) members in the canonical Sylow subgroup:
three transposition lines, three coordinate planes, and `D`. -/
theorem caseAFamily_le_sylowCarrier_iff (A : Subgroup Perm) :
    (CaseAFamily 6 A ∧ A ≤ sylowCarrier) ↔
      A = dLattice 1 ∨ A = dLattice 2 ∨ A = dLattice 4 ∨
      A = dLattice 8 ∨ A = dLattice 9 ∨ A = dLattice 10 ∨ A = D 6 := by
  rw [← caseAFamily_le_D_iff]
  exact ⟨fun ⟨h, hT⟩ => ⟨h, caseAFamily_le_D_of_le_sylowCarrier h hT⟩,
    fun ⟨h, hD⟩ => ⟨h, hD.trans D_le_sylowCarrier⟩⟩

/-- The exact case-(b) members in the canonical Sylow subgroup: the three
transposition lines, all seven hyperplanes of `D`, `D`, the exceptional group,
and the two additional mixed planes. -/
theorem caseBFamily_le_sylowCarrier_iff (A : Subgroup Perm) :
    (CaseBFamily 6 (by decide) A ∧ A ≤ sylowCarrier) ↔
      A = dLattice 1 ∨ A = dLattice 2 ∨ A = dLattice 4 ∨ A ⋖ D 6 ∨
      A = D 6 ∨ A = exceptional 6 (by decide) ∨ A = mixedSecond ∨ A = mixedThird := by
  constructor
  · rintro ⟨h, hT⟩
    rcases elementary_le_D_or_exceptional (caseBFamily_isElementaryTwo h) hT with hD | hE
    · have hl := (caseBFamily_le_D_iff A).1 ⟨h, hD⟩
      tauto
    · rcases (caseBFamily_le_exceptional_iff hE).1 h with hlast | hplus | h2 | h3 | hE
      · have hD : A ≤ D 6 := hlast ▸ last_le_plus.trans plus_le_D
        have hl := (caseBFamily_le_D_iff A).1 ⟨h, hD⟩
        tauto
      · have hp : A ⋖ D 6 := hplus ▸ plus_covBy_D
        tauto
      all_goals tauto
  · intro hl
    have hD (h : A = dLattice 1 ∨ A = dLattice 2 ∨ A = dLattice 4 ∨
        A ⋖ D 6 ∨ A = D 6) : CaseBFamily 6 (by decide) A ∧ A ≤ sylowCarrier := by
      obtain ⟨h, hD⟩ := (caseBFamily_le_D_iff A).2 h
      exact ⟨h, hD.trans D_le_sylowCarrier⟩
    rcases hl with h | h | h | h | h | rfl | rfl | rfl
    · exact hD (Or.inl h)
    · exact hD (Or.inr (Or.inl h))
    · exact hD (Or.inr (Or.inr (Or.inl h)))
    · exact hD (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact hD (Or.inr (Or.inr (Or.inr (Or.inr h))))
    · exact ⟨Or.inr (Or.inl (IsConjugateTo.refl _)), exceptional_le_sylowCarrier⟩
    · exact ⟨(caseBFamily_le_exceptional_iff mixedSecond_le_exceptional).2 (by tauto),
        mixedSecond_le_exceptional.trans exceptional_le_sylowCarrier⟩
    · exact ⟨(caseBFamily_le_exceptional_iff mixedThird_le_exceptional).2 (by tauto),
        mixedThird_le_exceptional.trans exceptional_le_sylowCarrier⟩

/-- The sole subgroup of the canonical Sylow subgroup conjugate to `D`
is `D` itself. -/
theorem eq_D_of_le_sylowCarrier_of_conjugate {A : Subgroup Perm}
    (hAT : A ≤ sylowCarrier) (h : IsConjugateTo A (D 6)) : A = D 6 := by
  have hA := h.isElementaryTwo (isElementaryTwo_disjointTranspositions 3 (by decide))
  rcases elementary_le_D_or_exceptional hA hAT with hD | hE
  · exact eq_D_of_le_of_conjugate hD h
  · exact (exceptional_not_conjugate_D hE h).elim

/-- Exactly one case-(b) member of the canonical Sylow subgroup is even. -/
theorem caseBFamily_even_le_sylowCarrier_iff (A : Subgroup Perm) :
    (CaseBFamily 6 (by decide) A ∧ A ≤ sylowCarrier ∧
      A ≤ alternatingGroup (Fin 6)) ↔ A = evenPart 6 := by
  constructor
  · rintro ⟨h, hT, he⟩
    rcases elementary_le_D_or_exceptional (caseBFamily_isElementaryTwo h) hT with hD | hE
    · exact eq_evenPart_of_caseBFamily_of_le hD h he
    · exact (exceptional_not_conjugate_evenPart hE ((caseBFamily_even_iff A).1 ⟨h, he⟩)).elim
  · rintro rfl
    exact ⟨Or.inr (Or.inr (Or.inl (IsConjugateTo.refl _))),
      inf_le_left.trans D_le_sylowCarrier, inf_le_right⟩

/-- The fourteen case-(b) members of the canonical Sylow subgroup, with the
three transposition lines first, then the seven planes of `D`, `D`, the
exceptional group, and the two remaining mixed planes. -/
def sylowCaseBMember : Fin 14 → Subgroup Perm :=
  ![dLattice 1, dLattice 2, dLattice 4,
    dLattice 8, dLattice 9, dLattice 10, dLattice 11, dLattice 12,
    dLattice 13, dLattice 14, D 6, exceptional 6 (by decide), mixedSecond, mixedThird]

/-- The complete fourteen-member list, expressed as an indexed range. -/
theorem caseBFamily_le_sylowCarrier_list (A : Subgroup Perm) :
    (CaseBFamily 6 (by decide) A ∧ A ≤ sylowCarrier) ↔
      ∃ i, A = sylowCaseBMember i := by
  rw [caseBFamily_le_sylowCarrier_iff, covBy_D_list]
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, sylowCaseBMember, dPlane,
    Matrix.cons_val_zero, Matrix.cons_val_succ, or_false]
  tauto

private def sylowCaseBIndices : Fin 14 → Finset (Fin 16) :=
  ![{0,1}, {0,2}, {0,4}, {0,1,2,3}, {0,1,4,5}, {0,2,4,6},
    {0,1,6,7}, {0,2,5,7}, {0,3,4,7}, {0,3,5,6},
    {0,1,2,3,4,5,6,7}, {0,3,4,7,8,11,12,15}, {0,4,8,12}, {0,4,11,15}]

private theorem sylowWords_mem_caseBMember (r : Fin 14) (i : Fin 16) :
    sylowWords i ∈ sylowCaseBMember r ↔ i ∈ sylowCaseBIndices r := by
  fin_cases r
  · change (∃ j ∈ dLatticeIndices 1, dWords j = sylowWords i) ↔ i ∈ sylowCaseBIndices 0
    revert i
    decide
  · change (∃ j ∈ dLatticeIndices 2, dWords j = sylowWords i) ↔ i ∈ sylowCaseBIndices 1
    revert i
    decide
  · change (∃ j ∈ dLatticeIndices 4, dWords j = sylowWords i) ↔ i ∈ sylowCaseBIndices 2
    revert i
    decide
  · change (∃ j ∈ dLatticeIndices 8, dWords j = sylowWords i) ↔ i ∈ sylowCaseBIndices 3
    revert i
    decide
  · change (∃ j ∈ dLatticeIndices 9, dWords j = sylowWords i) ↔ i ∈ sylowCaseBIndices 4
    revert i
    decide
  · change (∃ j ∈ dLatticeIndices 10, dWords j = sylowWords i) ↔ i ∈ sylowCaseBIndices 5
    revert i
    decide
  · change (∃ j ∈ dLatticeIndices 11, dWords j = sylowWords i) ↔ i ∈ sylowCaseBIndices 6
    revert i
    decide
  · change (∃ j ∈ dLatticeIndices 12, dWords j = sylowWords i) ↔ i ∈ sylowCaseBIndices 7
    revert i
    decide
  · change (∃ j ∈ dLatticeIndices 13, dWords j = sylowWords i) ↔ i ∈ sylowCaseBIndices 8
    revert i
    decide
  · change (∃ j ∈ dLatticeIndices 14, dWords j = sylowWords i) ↔ i ∈ sylowCaseBIndices 9
    revert i
    decide
  · change sylowWords i ∈ D 6 ↔ _
    rw [← dLattice_fifteen]
    change (∃ j ∈ dLatticeIndices 15, dWords j = sylowWords i) ↔ i ∈ sylowCaseBIndices 10
    revert i
    decide
  · change sylowWords i ∈ exceptional 6 (by decide) ↔ _
    rw [← exceptionalSubgroup_exceptional]
    change (∃ j ∈ exceptionalIndices 15, exceptionalWords j = sylowWords i) ↔
      i ∈ sylowCaseBIndices 11
    revert i
    decide
  · change sylowWords i ∈ mixedSecond ↔ _
    rw [← exceptionalSubgroup_mixedSecond]
    change (∃ j ∈ exceptionalIndices 10, exceptionalWords j = sylowWords i) ↔
      i ∈ sylowCaseBIndices 12
    revert i
    decide
  · change sylowWords i ∈ mixedThird ↔ _
    rw [← exceptionalSubgroup_mixedThird]
    change (∃ j ∈ exceptionalIndices 11, exceptionalWords j = sylowWords i) ↔
      i ∈ sylowCaseBIndices 13
    revert i
    decide

/-- No two entries in the fourteen-member list coincide. -/
theorem sylowCaseBMember_injective : Function.Injective sylowCaseBMember := by
  intro r s h
  have he : sylowCaseBIndices r = sylowCaseBIndices s := by
    ext i
    rw [← sylowWords_mem_caseBMember, ← sylowWords_mem_caseBMember, h]
  exact (by decide : Function.Injective sylowCaseBIndices) he

/-- There are exactly fourteen case-(b) subgroups in the canonical Sylow subgroup. -/
theorem card_caseBFamily_le_sylowCarrier :
    Nat.card {A : Subgroup Perm // CaseBFamily 6 (by decide) A ∧ A ≤ sylowCarrier} = 14 := by
  let e : Fin 14 ≃ {A : Subgroup Perm // CaseBFamily 6 (by decide) A ∧ A ≤ sylowCarrier} :=
    Equiv.ofBijective (fun i => ⟨sylowCaseBMember i,
      (caseBFamily_le_sylowCarrier_list _).2 ⟨i, rfl⟩⟩) ⟨
      fun _ _ h => sylowCaseBMember_injective (congrArg Subtype.val h), by
        rintro ⟨A, hA⟩
        obtain ⟨i, rfl⟩ := (caseBFamily_le_sylowCarrier_list A).1 hA
        exact ⟨i, rfl⟩⟩
  exact (Nat.card_congr e).symm.trans (by simp)

end CFSG.Quasithin.ChapterB.Offenders.Six
