module
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Defs
public import CFSG.Quasithin.ChapterB.Section03.Offenders.FixedTests
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Six.Representatives
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Six.Structure.Basic
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Six.Structure.Reduction
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Six.Structure.ExceptionalLattice.Tables

/-!
# Ambient conjugacy of the exceptional subgroup lattice

The explicit sixteen-row lattice (including the trivial subgroup) yields seven
nontrivial ambient conjugacy types. Explicit coordinate permutations identify
the three mixed planes. The exceptional group contains exactly one
transposition; this rules out conjugates of `A₂` and `D`. Support sizes force a
hypothetical conjugate of `evenPart` to have a common fixed point, contradicting
its action on six points. Consequently the six good conjugacy types select
exactly the five subgroups containing the final transposition, and case (a)
selects only the final line. All five good groups contain an odd permutation.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
1 March 2004 manuscript, Proposition B.3.2 and Lemma B.3.4, printed pp. 83–85.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterB.Offenders.Six
open Representation.BinaryOffender
private def exceptionalCanonicalRow (r : Fin 16) : Fin 16 :=
  ![0,1,1,1,4,5,5,5,8,9,9,9,12,12,12,15] r

private def exceptionalConjugator (r : Fin 16) : Perm :=
  ![1,1,Equiv.swap 1 2,Equiv.swap 1 3,1,1,Equiv.swap 1 2,Equiv.swap 1 3,
    1,1,Equiv.swap 1 2,Equiv.swap 1 3,1,Equiv.swap 1 2,Equiv.swap 1 3,1] r

private theorem exceptionalSubgroup_conjugate (r : Fin 16) :
    IsConjugateTo (exceptionalSubgroup r)
      (exceptionalSubgroup (exceptionalCanonicalRow r)) := by
  have hf : ∀ r i, i ∈ exceptionalIndices r →
      ∃ j ∈ exceptionalIndices (exceptionalCanonicalRow r),
        (MulAut.conj (exceptionalConjugator r)) (exceptionalWords j) = exceptionalWords i :=
    by decide
  have hb : ∀ r j, j ∈ exceptionalIndices (exceptionalCanonicalRow r) →
      ∃ i ∈ exceptionalIndices r,
        exceptionalWords i = (MulAut.conj (exceptionalConjugator r)) (exceptionalWords j) :=
    by decide
  refine ⟨exceptionalConjugator r, ?_⟩
  ext g
  constructor
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨j, hj, hji⟩ := hf r i hi
    exact Subgroup.mem_map.mpr ⟨exceptionalWords j, ⟨j, hj, rfl⟩, hji⟩
  · rintro ⟨x, ⟨j, hj, rfl⟩, rfl⟩
    exact hb r j hj

/-- Permuting the first four points identifies the second mixed plane with `plus`. -/
theorem mixedSecond_conjugate_plus : IsConjugateTo mixedSecond plus := by
  have h := exceptionalSubgroup_conjugate 10
  change IsConjugateTo (exceptionalSubgroup 10) (exceptionalSubgroup 9) at h
  simpa only [exceptionalSubgroup_mixedSecond, exceptionalSubgroup_plus] using h

/-- Permuting the first four points identifies the third mixed plane with `plus`. -/
theorem mixedThird_conjugate_plus : IsConjugateTo mixedThird plus := by
  have h := exceptionalSubgroup_conjugate 11
  change IsConjugateTo (exceptionalSubgroup 11) (exceptionalSubgroup 9) at h
  simpa only [exceptionalSubgroup_mixedThird, exceptionalSubgroup_plus] using h

/-- Every nontrivial subgroup of the exceptional group has one of these seven
ambient conjugacy types, deduced from the explicit lattice. -/
theorem exceptional_subgroup_conjugacy {A : Subgroup Perm}
    (hA : A ≤ exceptional 6 (by decide)) (hne : A ≠ ⊥) :
    IsConjugateTo A (disjointTranspositions 6 1) ∨
    IsConjugateTo A (exceptional 6 (by decide)) ∨ IsConjugateTo A plus ∨
    IsConjugateTo A double ∨ IsConjugateTo A triple ∨
    IsConjugateTo A klein ∨ IsConjugateTo A twisted := by
  obtain ⟨r, rfl⟩ := (subgroup_le_exceptional_iff A).1 hA
  have h := exceptionalSubgroup_conjugate r
  have ht : r = 0 ∨ exceptionalCanonicalRow r = 1 ∨ exceptionalCanonicalRow r = 4 ∨
      exceptionalCanonicalRow r = 5 ∨ exceptionalCanonicalRow r = 8 ∨
      exceptionalCanonicalRow r = 9 ∨ exceptionalCanonicalRow r = 12 ∨
      exceptionalCanonicalRow r = 15 := (by decide : ∀ r : Fin 16,
        r = 0 ∨ exceptionalCanonicalRow r = 1 ∨ exceptionalCanonicalRow r = 4 ∨
        exceptionalCanonicalRow r = 5 ∨ exceptionalCanonicalRow r = 8 ∨
        exceptionalCanonicalRow r = 9 ∨ exceptionalCanonicalRow r = 12 ∨
        exceptionalCanonicalRow r = 15) r
  rcases ht with hr | hr | hr | hr | hr | hr | hr | hr
  · subst r
    exact (hne exceptionalSubgroup_zero).elim
  · rw [hr, exceptionalSubgroup_double] at h
    exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rw [hr, exceptionalSubgroup_last] at h
    exact Or.inl (h.trans last_conjugate)
  · rw [hr, exceptionalSubgroup_triple] at h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · rw [hr, exceptionalSubgroup_klein] at h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · rw [hr, exceptionalSubgroup_plus] at h
    exact Or.inr (Or.inr (Or.inl h))
  · rw [hr, exceptionalSubgroup_twisted] at h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
  · rw [hr, exceptionalSubgroup_exceptional] at h
    exact Or.inr (Or.inl h)

/-- The only transposition in the exceptional group is the final one. -/
theorem exceptional_transposition_unique {g : Perm}
    (hg : g ∈ exceptional 6 (by decide)) (hs : g.support.card = 2) :
    g = pairSwap 6 2 := by
  obtain ⟨i, rfl⟩ := (mem_exceptional_iff g).1 hg
  exact (by decide : ∀ i, (exceptionalWords i).support.card = 2 →
    exceptionalWords i = pairSwap 6 2) i hs

private theorem conjugate_has_transposition {A B : Subgroup Perm}
    (h : IsConjugateTo A B) (hb : ∃ b ∈ B, (b : Perm).support.card = 2) :
    ∃ a ∈ A, (a : Perm).support.card = 2 := by
  obtain ⟨p, rfl⟩ := h
  obtain ⟨b, hb, hs⟩ := hb
  refine ⟨(MulAut.conj p) b, Subgroup.mem_map_of_mem _ hb, ?_⟩
  simpa only [MulAut.conj_apply, Equiv.Perm.card_support_conj] using hs

private theorem not_conjugate_two_transpositions {A B : Subgroup Perm}
    (hA : A ≤ exceptional 6 (by decide))
    (hx : pairSwap 6 0 ∈ B) (hy : pairSwap 6 1 ∈ B) : ¬ IsConjugateTo A B := by
  rintro ⟨p, hp⟩
  have hmem (x : Perm) (hx : x ∈ B) : (MulAut.conj p) x ∈ exceptional 6 (by decide) :=
    hA (hp ▸ Subgroup.mem_map_of_mem _ hx)
  have hs (i : Fin 3) : ((MulAut.conj p) (pairSwap 6 i)).support.card = 2 := by
    rw [MulAut.conj_apply, Equiv.Perm.card_support_conj]
    exact (by decide : ∀ i : Fin 3, (pairSwap 6 i).support.card = 2) i
  have he := (exceptional_transposition_unique (hmem _ hx) (hs 0)).trans
    (exceptional_transposition_unique (hmem _ hy) (hs 1)).symm
  have hf := (MulAut.conj p).injective he
  exact (by decide : pairSwap 6 0 ≠ pairSwap 6 1) hf

/-- No subgroup of the exceptional group is conjugate to `A₂`. -/
theorem exceptional_not_conjugate_A2 {A : Subgroup Perm}
    (hA : A ≤ exceptional 6 (by decide)) :
    ¬ IsConjugateTo A (disjointTranspositions 6 2) :=
  not_conjugate_two_transpositions hA (pairSwap_mem 0 (by decide)) (pairSwap_mem 1 (by decide))

/-- No subgroup of the exceptional group is conjugate to `D`. -/
theorem exceptional_not_conjugate_D {A : Subgroup Perm}
    (hA : A ≤ exceptional 6 (by decide)) : ¬ IsConjugateTo A (D 6) :=
  not_conjugate_two_transpositions hA (pairSwap_mem 0 (by decide)) (pairSwap_mem 1 (by decide))

/-- Unlike the regular Klein four group in the exceptional group, `evenPart`
has no common fixed point. Thus none of its conjugates is contained here. -/
theorem exceptional_not_conjugate_evenPart {A : Subgroup Perm}
    (hA : A ≤ exceptional 6 (by decide)) : ¬ IsConjugateTo A (evenPart 6) := by
  rintro ⟨p, hp⟩
  have hfix (i : Fin 4) : (MulAut.conj p) (planeWords 4 i) 4 = 4 := by
    have hm : (MulAut.conj p) (planeWords 4 i) ∈ exceptional 6 (by decide) :=
      hA (hp ▸ Subgroup.mem_map_of_mem _ ((mem_evenPart_iff _).2 ⟨i, rfl⟩))
    obtain ⟨j, hj⟩ := (mem_exceptional_iff _).1 hm
    have hs : (exceptionalWords j).support.card = (planeWords 4 i).support.card := by
      rw [hj, MulAut.conj_apply, Equiv.Perm.card_support_conj]
    rw [← hj]
    exact (by decide : ∀ i j, (exceptionalWords j).support.card = (planeWords 4 i).support.card →
      exceptionalWords j 4 = 4) i j hs
  obtain ⟨i, hi⟩ := (by decide : ∀ k : Fin 6, ∃ i : Fin 4, planeWords 4 i k ≠ k) (p⁻¹ 4)
  apply hi
  have he := congrArg (fun x => (p⁻¹ : Perm) x) (hfix i)
  simpa [MulAut.conj_apply, Equiv.Perm.mul_apply] using he
private theorem last_mem_of_conjugate {A B : Subgroup Perm}
    (hA : A ≤ exceptional 6 (by decide)) (h : IsConjugateTo A B)
    (hb : ∃ b ∈ B, (b : Perm).support.card = 2) : pairSwap 6 2 ∈ A := by
  obtain ⟨a, ha, hs⟩ := conjugate_has_transposition h hb
  exact exceptional_transposition_unique (hA ha) hs ▸ ha

/-- Exactly five subgroups contain the unique transposition. -/
theorem exceptional_last_mem_iff {A : Subgroup Perm}
    (hA : A ≤ exceptional 6 (by decide)) :
    pairSwap 6 2 ∈ A ↔ A = last ∨ A = plus ∨ A = mixedSecond ∨
      A = mixedThird ∨ A = exceptional 6 (by decide) := by
  obtain ⟨r, rfl⟩ := (subgroup_le_exceptional_iff A).1 hA
  change exceptionalWords 4 ∈ exceptionalSubgroup r ↔ _
  rw [exceptionalWord_mem_iff]
  have ht : 4 ∈ exceptionalIndices r ↔ r = 4 ∨ r = 9 ∨ r = 10 ∨ r = 11 ∨ r = 15 :=
    (by decide : ∀ r, 4 ∈ exceptionalIndices r ↔
      r = 4 ∨ r = 9 ∨ r = 10 ∨ r = 11 ∨ r = 15) r
  rw [ht, ← exceptionalSubgroup_last, ← exceptionalSubgroup_plus,
    ← exceptionalSubgroup_mixedSecond, ← exceptionalSubgroup_mixedThird,
    ← exceptionalSubgroup_exceptional]
  simp only [exceptionalSubgroup_injective.eq_iff]

/-- The literal six-representative disjunction inside the exceptional group.
It consists of the final line, the three mixed planes, and the whole group. -/
theorem exceptional_good_iff {A : Subgroup Perm}
    (hA : A ≤ exceptional 6 (by decide)) :
    (IsConjugateTo A (disjointTranspositions 6 1) ∨
      IsConjugateTo A (disjointTranspositions 6 2) ∨ IsConjugateTo A (D 6) ∨
      IsConjugateTo A (exceptional 6 (by decide)) ∨
      IsConjugateTo A (evenPart 6) ∨ IsConjugateTo A plus) ↔
    (A = last ∨ A = plus ∨ A = mixedSecond ∨ A = mixedThird ∨
      A = exceptional 6 (by decide)) := by
  constructor
  · intro h
    apply (exceptional_last_mem_iff hA).1
    rcases h with h | h | h | h | h | h
    · exact last_mem_of_conjugate hA h
        ⟨pairSwap 6 0, pairSwap_mem 0 (by decide), by decide⟩
    · exact (exceptional_not_conjugate_A2 hA h).elim
    · exact (exceptional_not_conjugate_D hA h).elim
    · exact last_mem_of_conjugate hA h
        ⟨pairSwap 6 2, (mem_exceptional_iff _).2 ⟨4, rfl⟩, by decide⟩
    · exact (exceptional_not_conjugate_evenPart hA h).elim
    · exact last_mem_of_conjugate hA h
        ⟨pairSwap 6 2, (mem_plus_iff _).2 ⟨2, rfl⟩, by decide⟩
  · rintro (rfl | rfl | rfl | rfl | rfl)
    · exact Or.inl last_conjugate
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (IsConjugateTo.refl _)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr mixedSecond_conjugate_plus))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr mixedThird_conjugate_plus))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (IsConjugateTo.refl _))))

/-- Case (a) contributes only the final transposition subgroup inside the
exceptional group. -/
theorem exceptional_caseAFamily_iff {A : Subgroup Perm}
    (hA : A ≤ exceptional 6 (by decide)) : CaseAFamily 6 A ↔ A = last := by
  constructor
  · rintro ⟨m, hm, hm3, h⟩
    have hm' : m = 1 ∨ m = 2 ∨ m = 3 := by omega
    rcases hm' with rfl | rfl | rfl
    · have hc : Nat.card A = 2 := h.card_eq.trans (card_disjointTranspositions 1)
      have hm := last_mem_of_conjugate hA h
        ⟨pairSwap 6 0, pairSwap_mem 0 (by decide), by decide⟩
      have hl : last ≤ A := (Subgroup.closure_le _).2 (by rintro g rfl; exact hm)
      exact (Subgroup.eq_of_le_of_card_ge hl (by rw [hc, card_last])).symm
    · exact (exceptional_not_conjugate_A2 hA h).elim
    · exact (exceptional_not_conjugate_D hA h).elim
  · rintro rfl
    exact ⟨1, by decide, by decide, last_conjugate⟩

/-- Each of the five good subgroups contains an odd transposition. -/
theorem exceptional_good_not_le_alternating {A : Subgroup Perm}
    (hA : A ≤ exceptional 6 (by decide))
    (h : A = last ∨ A = plus ∨ A = mixedSecond ∨ A = mixedThird ∨
      A = exceptional 6 (by decide)) : ¬ A ≤ alternatingGroup (Fin 6) := by
  intro hAlt
  have hm := hAlt ((exceptional_last_mem_iff hA).2 h)
  have hn : pairSwap 6 2 ∉ alternatingGroup (Fin 6) := by
    simp [pairSwap, Equiv.Perm.mem_alternatingGroup]
  exact hn hm

/-- The second mixed plane lies in the exceptional group. -/
theorem mixedSecond_le_exceptional : mixedSecond ≤ exceptional 6 (by decide) := by
  rw [← exceptionalSubgroup_mixedSecond]
  exact exceptionalSubgroup_le 10

/-- The third mixed plane lies in the exceptional group. -/
theorem mixedThird_le_exceptional : mixedThird ≤ exceptional 6 (by decide) := by
  rw [← exceptionalSubgroup_mixedThird]
  exact exceptionalSubgroup_le 11

/-- All five good subgroups fail containment in `A₆`. -/
theorem exceptional_five_not_le_alternating :
    ¬ last ≤ alternatingGroup (Fin 6) ∧
    ¬ plus ≤ alternatingGroup (Fin 6) ∧
    ¬ mixedSecond ≤ alternatingGroup (Fin 6) ∧
    ¬ mixedThird ≤ alternatingGroup (Fin 6) ∧
    ¬ exceptional 6 (by decide) ≤ alternatingGroup (Fin 6) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact exceptional_good_not_le_alternating last_le_exceptional (Or.inl rfl)
  · exact exceptional_good_not_le_alternating plus_le_exceptional (Or.inr (Or.inl rfl))
  · exact exceptional_good_not_le_alternating mixedSecond_le_exceptional
      (Or.inr (Or.inr (Or.inl rfl)))
  · exact exceptional_good_not_le_alternating mixedThird_le_exceptional
      (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact exceptional_good_not_le_alternating le_rfl
      (Or.inr (Or.inr (Or.inr (Or.inr rfl))))

end CFSG.Quasithin.ChapterB.Offenders.Six
