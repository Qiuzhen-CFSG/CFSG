module
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Defs
public import CFSG.Quasithin.ChapterB.Section03.Offenders.FixedTests
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Six.Representatives
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Six.Structure.Basic
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Six.Structure.Reduction
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Six.Structure.DLattice.Cube
import Mathlib.Tactic.FinCases

/-!
# The degree-six disjoint-transposition lattice and offender families

The exhaustive cube list gives seven involution lines, seven planes, and `D`.
Explicit permutations identify their ambient conjugacy types. Subgroup order,
the number of transpositions, and support size separate the representatives.
The seven planes are exactly the lattice hyperplanes, giving the global
case-(b) conjugacy list and the exact case-(a) and case-(b) lists inside `D`.
The even plane is the unique even case-(b) member inside `D`.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
1 March 2004 manuscript, Proposition B.3.2 and Lemma B.3.4, printed pp. 83–85.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterB.Offenders.Six
open Representation.BinaryOffender

/-- The named representatives occurring in the cube, indexed by conjugacy type. -/
def dRepresentative : Fin 8 → Subgroup Perm :=
  ![⊥, disjointTranspositions 6 1, disjointTranspositions 6 2,
    D 6, double, triple, plus, evenPart 6]

/-- The type of each entry of the subgroup list. -/
def dLatticeType : Fin 16 → Fin 8 := ![0,1,1,4,1,4,4,5,2,2,2,6,6,6,7,3]

private def dRepresentativeIndex : Fin 8 → Fin 16 := ![0,1,8,15,3,7,13,14]

private theorem eq_dLattice_of_table {k : ℕ} {A : Subgroup Perm}
    (f : Fin k → Perm) (r : Fin 16) (hm : ∀ g, g ∈ A ↔ ∃ i, f i = g)
    (hf : ∀ i, ∃ j ∈ dLatticeIndices r, dWords j = f i)
    (hb : ∀ j ∈ dLatticeIndices r, ∃ i, f i = dWords j) : A = dLattice r := by
  ext g
  rw [hm, mem_dLattice_iff]
  constructor
  · rintro ⟨i, rfl⟩
    exact hf i
  · rintro ⟨j, hj, rfl⟩
    exact hb j hj

private theorem dRepresentative_eq (r : Fin 8) :
    dRepresentative r = dLattice (dRepresentativeIndex r) := by
  fin_cases r
  · exact dLattice_zero.symm
  · exact eq_dLattice_of_table (initialWords 1) 1
      (mem_disjointTranspositions_iff 1) (by decide) (by decide)
  · exact eq_dLattice_of_table (initialWords 2) 8
      (mem_disjointTranspositions_iff 2) (by decide) (by decide)
  · exact dLattice_fifteen.symm
  · exact eq_dLattice_of_table (lineWords 1) 3 mem_double_iff (by decide) (by decide)
  · exact eq_dLattice_of_table (lineWords 2) 7 mem_triple_iff (by decide) (by decide)
  · exact eq_dLattice_of_table (planeWords 0) 13 mem_plus_iff (by decide) (by decide)
  · exact eq_dLattice_of_table (planeWords 4) 14 mem_evenPart_iff (by decide) (by decide)

@[simp] theorem dLattice_one : dLattice 1 = disjointTranspositions 6 1 :=
  (dRepresentative_eq 1).symm
@[simp] theorem dLattice_eight : dLattice 8 = disjointTranspositions 6 2 :=
  (dRepresentative_eq 2).symm
@[simp] theorem dLattice_three : dLattice 3 = double := (dRepresentative_eq 4).symm
@[simp] theorem dLattice_seven : dLattice 7 = triple := (dRepresentative_eq 5).symm
@[simp] theorem dLattice_thirteen : dLattice 13 = plus := (dRepresentative_eq 6).symm
@[simp] theorem dLattice_fourteen : dLattice 14 = evenPart 6 := (dRepresentative_eq 7).symm

private def dConjugator (r : Fin 16) : Perm :=
  let s01 := Equiv.swap 0 2 * Equiv.swap 1 3
  let s02 := Equiv.swap 0 4 * Equiv.swap 1 5
  let s12 := Equiv.swap 2 4 * Equiv.swap 3 5
  ![1,1,s01,1,s02,s12,s02,1,1,s12,s02,s02,s12,1,1,1] r

/-- The ambient conjugacy type of every subgroup in the explicit list. -/
theorem dLattice_conjugate (r : Fin 16) :
    IsConjugateTo (dLattice r) (dRepresentative (dLatticeType r)) := by
  rw [dRepresentative_eq]
  have hf : ∀ r : Fin 16, ∀ i ∈ dLatticeIndices r,
      ∃ j ∈ dLatticeIndices (dRepresentativeIndex (dLatticeType r)),
        (MulAut.conj (dConjugator r)) (dWords j) = dWords i := by decide
  have hb : ∀ r : Fin 16, ∀ j ∈ dLatticeIndices (dRepresentativeIndex (dLatticeType r)),
      ∃ i ∈ dLatticeIndices r,
        dWords i = (MulAut.conj (dConjugator r)) (dWords j) := by decide
  refine ⟨dConjugator r, ?_⟩
  ext g
  constructor
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨j, hj, he⟩ := hf r i hi
    exact Subgroup.mem_map.mpr ⟨dWords j, (dWords_mem_dLattice _ _).2 hj, he⟩
  · rintro ⟨g, ⟨j, hj, rfl⟩, rfl⟩
    exact hb r j hj

/-- The seven nontrivial ambient conjugacy types inside `D`. -/
theorem subgroup_D_conjugacy {A : Subgroup Perm} (hAD : A ≤ D 6) (hne : A ≠ ⊥) :
    IsConjugateTo A (disjointTranspositions 6 1) ∨
    IsConjugateTo A (disjointTranspositions 6 2) ∨ IsConjugateTo A (D 6) ∨
    IsConjugateTo A double ∨ IsConjugateTo A triple ∨
    IsConjugateTo A plus ∨ IsConjugateTo A (evenPart 6) := by
  obtain ⟨r, hr, rfl⟩ := (nontrivial_subgroup_le_D_iff A).1 ⟨hAD, hne⟩
  have hc := dLattice_conjugate r
  fin_cases r <;> simp_all [dLatticeType, dRepresentative]

/-- The three conjugacy types of hyperplanes. -/
theorem hyperplane_D_conjugacy {A : Subgroup Perm} (hA : A ⋖ D 6) :
    IsConjugateTo A (disjointTranspositions 6 2) ∨
      IsConjugateTo A plus ∨ A = evenPart 6 := by
  obtain ⟨r, h1, h2, rfl⟩ := (covBy_D_iff A).1 hA
  have hc := dLattice_conjugate r
  fin_cases r <;> simp_all [dLatticeType, dRepresentative]

/-- The initial coordinate plane is a hyperplane. -/
theorem disjointTranspositions_two_covBy_D : disjointTranspositions 6 2 ⋖ D 6 := by
  rw [← dLattice_eight]
  exact (dLattice_covBy_D_iff 8).2 (by decide)

/-- The mixed representative is a hyperplane. -/
theorem plus_covBy_D : plus ⋖ D 6 := by
  rw [← dLattice_thirteen]
  exact (dLattice_covBy_D_iff 13).2 (by decide)

/-- The even part is a hyperplane. -/
theorem evenPart_covBy_D : evenPart 6 ⋖ D 6 := by
  rw [← dLattice_fourteen]
  exact (dLattice_covBy_D_iff 14).2 (by decide)

private theorem plus_ne_evenPart : plus ≠ evenPart 6 := by
  rw [← dLattice_thirteen, ← dLattice_fourteen]
  exact fun h => (by decide : (13 : Fin 16) ≠ 14) (dLattice_injective h)

/-- The global degree-six case-(a) family. -/
theorem caseAFamily_iff (A : Subgroup Perm) : CaseAFamily 6 A ↔
    IsConjugateTo A (disjointTranspositions 6 1) ∨
    IsConjugateTo A (disjointTranspositions 6 2) ∨ IsConjugateTo A (D 6) := by
  constructor
  · rintro ⟨m, hm, hm3, h⟩
    have : m = 1 ∨ m = 2 ∨ m = 3 := by omega
    rcases this with rfl | rfl | rfl
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rintro (h | h | h)
    · exact ⟨1, by decide, by decide, h⟩
    · exact ⟨2, by decide, by decide, h⟩
    · exact ⟨3, by decide, by decide, h⟩

/-- The globally defined case-(b) family has exactly these six conjugacy types. -/
theorem caseBFamily_iff (A : Subgroup Perm) : CaseBFamily 6 (by decide) A ↔
    IsConjugateTo A (disjointTranspositions 6 1) ∨
    IsConjugateTo A (disjointTranspositions 6 2) ∨ IsConjugateTo A (D 6) ∨
    IsConjugateTo A (exceptional 6 (by decide)) ∨
    IsConjugateTo A (evenPart 6) ∨ IsConjugateTo A plus := by
  constructor
  · rintro (h | h | h | ⟨B, hB, hne, hAB⟩)
    · rcases (caseAFamily_iff A).1 h with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · rcases hyperplane_D_conjugacy hB with h | h | h
      · exact Or.inr (Or.inl (hAB.trans h))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hAB.trans h)))))
      · exact (hne h).elim
  · rintro (h | h | h | h | h | h)
    · exact Or.inl ((caseAFamily_iff A).2 (Or.inl h))
    · exact Or.inl ((caseAFamily_iff A).2 (Or.inr (Or.inl h)))
    · exact Or.inl ((caseAFamily_iff A).2 (Or.inr (Or.inr h)))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr ⟨plus, plus_covBy_D, plus_ne_evenPart, h⟩))

/-- Every member of the degree-six case-(b) family is elementary abelian. -/
theorem caseBFamily_isElementaryTwo {A : Subgroup Perm}
    (h : CaseBFamily 6 (by decide) A) : IsElementaryTwo A := by
  rcases (caseBFamily_iff A).1 h with h | h | h | h | h | h
  · exact h.isElementaryTwo (isElementaryTwo_disjointTranspositions 1 (by decide))
  · exact h.isElementaryTwo (isElementaryTwo_disjointTranspositions 2 (by decide))
  · exact h.isElementaryTwo (isElementaryTwo_disjointTranspositions 3 (by decide))
  · exact h.isElementaryTwo isElementaryTwo_exceptional
  · exact h.isElementaryTwo isElementaryTwo_evenPart
  · exact h.isElementaryTwo isElementaryTwo_plus

private theorem transposition_not_even (i : Fin 3) :
    pairSwap 6 i ∉ alternatingGroup (Fin 6) := by
  fin_cases i <;> simp [pairSwap, Equiv.Perm.mem_alternatingGroup]

private theorem initial_not_even (m : Fin 4) (hm : 0 < m.val) :
    ¬disjointTranspositions 6 m.val ≤ alternatingGroup (Fin 6) :=
  fun h => transposition_not_even 0 (h (pairSwap_mem 0 hm))

private theorem exceptional_not_even :
    ¬exceptional 6 (by decide) ≤ alternatingGroup (Fin 6) := by
  intro h
  apply transposition_not_even 2
  apply h
  exact Subgroup.subset_closure (Or.inr ⟨2, by decide, rfl⟩)

private theorem plus_not_even : ¬plus ≤ alternatingGroup (Fin 6) := by
  intro h
  exact transposition_not_even 2 (h (Subgroup.subset_closure (Or.inr rfl)))

/-- Among the case-(b) types, exactly the even plane lies in the alternating group. -/
theorem caseBFamily_even_iff (A : Subgroup Perm) :
    (CaseBFamily 6 (by decide) A ∧ A ≤ alternatingGroup (Fin 6)) ↔
      IsConjugateTo A (evenPart 6) := by
  constructor
  · rintro ⟨h, he⟩
    rcases (caseBFamily_iff A).1 h with h | h | h | h | h | h
    · exact (initial_not_even 1 (by decide) (h.le_alternating_iff.1 he)).elim
    · exact (initial_not_even 2 (by decide) (h.le_alternating_iff.1 he)).elim
    · exact (initial_not_even 3 (by decide) (h.le_alternating_iff.1 he)).elim
    · exact (exceptional_not_even (h.le_alternating_iff.1 he)).elim
    · exact h
    · exact (plus_not_even (h.le_alternating_iff.1 he)).elim
  · intro h
    exact ⟨Or.inr (Or.inr (Or.inl h)), h.le_alternating_iff.2 inf_le_right⟩

/-- A subgroup of `D` conjugate to `D` is `D` itself. -/
theorem eq_D_of_le_of_conjugate {A : Subgroup Perm} (hAD : A ≤ D 6)
    (h : IsConjugateTo A (D 6)) : A = D 6 :=
  Subgroup.eq_of_le_of_card_ge hAD h.card_eq.ge

/-- The unique even case-(b) member inside `D` is its even plane. -/
theorem eq_evenPart_of_caseBFamily_of_le {A : Subgroup Perm} (hAD : A ≤ D 6)
    (h : CaseBFamily 6 (by decide) A) (he : A ≤ alternatingGroup (Fin 6)) :
    A = evenPart 6 :=
  Subgroup.eq_of_le_of_card_ge (le_inf hAD he) ((caseBFamily_even_iff A).1 ⟨h, he⟩).card_eq.ge

/-- The number of transpositions in an ambient degree-six subgroup. -/
noncomputable def transpositionCount (A : Subgroup Perm) : ℕ :=
  Nat.card {g : Perm // g ∈ A ∧ g.support.card = 2}

/-- Conjugacy preserves the number of transpositions. -/
theorem transpositionCount_eq_of_conjugate {A B : Subgroup Perm}
    (h : IsConjugateTo A B) : transpositionCount A = transpositionCount B := by
  classical
  obtain ⟨g, rfl⟩ := h
  let e := Equiv.subtypeEquiv (MulAut.conj g).toEquiv
    (p := fun x => x ∈ B ∧ x.support.card = 2)
    (q := fun x => x ∈ B.map (MulAut.conj g).toMonoidHom ∧ x.support.card = 2) (by
      intro x
      have hc : ((MulAut.conj g) x).support.card = x.support.card :=
        Equiv.Perm.card_support_conj
      change (x ∈ B ∧ x.support.card = 2) ↔
        ((MulAut.conj g) x ∈ B.map (MulAut.conj g).toMonoidHom ∧
          ((MulAut.conj g) x).support.card = 2)
      rw [hc]
      constructor
      · rintro ⟨hx, hs⟩
        exact ⟨Subgroup.mem_map_of_mem _ hx, hs⟩
      · rintro ⟨⟨y, hy, he⟩, hs⟩
        have : y = x := (MulAut.conj g).injective he
        exact ⟨this ▸ hy, hs⟩)
  exact (Nat.card_congr e).symm

/-- The transposition counts in the exhaustive cube list. -/
theorem transpositionCount_dLattice (r : Fin 16) :
    transpositionCount (dLattice r) = ![0,1,1,0,1,0,0,0,2,2,2,1,1,1,0,3] r := by
  classical
  let f : {i : Fin 8 // i ∈ dLatticeIndices r ∧ (dWords i).support.card = 2} →
      {g : Perm // g ∈ dLattice r ∧ g.support.card = 2} := fun i =>
    ⟨dWords i.val, (dWords_mem_dLattice r i.val).2 i.property.1, i.property.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j h
      exact Subtype.ext (dWords_injective (congrArg Subtype.val h))
    · rintro ⟨g, ⟨i, hi, rfl⟩, hs⟩
      exact ⟨⟨i, hi, hs⟩, rfl⟩
  unfold transpositionCount
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card,
    Fintype.card_subtype]
  have cert : ∀ r : Fin 16,
      (Finset.univ.filter fun i => i ∈ dLatticeIndices r ∧ (dWords i).support.card = 2).card =
        ![0,1,1,0,1,0,0,0,2,2,2,1,1,1,0,3] r := by decide
  exact cert r

/-- Exactly the three transposition lines, three coordinate planes, and `D`
belong to case (a). -/
theorem caseAFamily_dLattice_iff (r : Fin 16) : CaseAFamily 6 (dLattice r) ↔
    r = 1 ∨ r = 2 ∨ r = 4 ∨ r = 8 ∨ r = 9 ∨ r = 10 ∨ r = 15 := by
  constructor
  · intro h
    have hc : ∃ s : Fin 16, (s = 1 ∨ s = 8 ∨ s = 15) ∧
        (dLatticeIndices r).card = (dLatticeIndices s).card ∧
        ![0,1,1,0,1,0,0,0,2,2,2,1,1,1,0,3] r =
          (![0,1,1,0,1,0,0,0,2,2,2,1,1,1,0,3] s : ℕ) := by
      rcases (caseAFamily_iff _).1 h with h | h | h
      · rw [← dLattice_one] at h
        exact ⟨1, Or.inl rfl, by simpa only [card_dLattice] using h.card_eq,
          by simpa only [transpositionCount_dLattice] using transpositionCount_eq_of_conjugate h⟩
      · rw [← dLattice_eight] at h
        exact ⟨8, Or.inr (Or.inl rfl), by simpa only [card_dLattice] using h.card_eq,
          by simpa only [transpositionCount_dLattice] using transpositionCount_eq_of_conjugate h⟩
      · rw [← dLattice_fifteen] at h
        exact ⟨15, Or.inr (Or.inr rfl), by simpa only [card_dLattice] using h.card_eq,
          by simpa only [transpositionCount_dLattice] using transpositionCount_eq_of_conjugate h⟩
    have cert : ∀ r s : Fin 16, (s = 1 ∨ s = 8 ∨ s = 15) →
        (dLatticeIndices r).card = (dLatticeIndices s).card →
        ![0,1,1,0,1,0,0,0,2,2,2,1,1,1,0,3] r =
          (![0,1,1,0,1,0,0,0,2,2,2,1,1,1,0,3] s : ℕ) →
        r = 1 ∨ r = 2 ∨ r = 4 ∨ r = 8 ∨ r = 9 ∨ r = 10 ∨ r = 15 := by
      intro r; fin_cases r <;> decide
    obtain ⟨s, hs, hcard, hcount⟩ := hc
    exact cert r s hs hcard hcount
  · intro h
    have hc := dLattice_conjugate r
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals apply (caseAFamily_iff _).2
    all_goals simp only [dLatticeType, dRepresentative, Matrix.cons_val_zero,
      Matrix.cons_val_one] at hc
    all_goals tauto

/-- Exactly the three transposition lines, all seven planes, and `D`
belong to case (b). -/
theorem caseBFamily_dLattice_iff (r : Fin 16) : CaseBFamily 6 (by decide) (dLattice r) ↔
    r = 1 ∨ r = 2 ∨ r = 4 ∨ 8 ≤ r.val := by
  constructor
  · intro h
    rcases (caseBFamily_iff _).1 h with h | h | h | h | h | h
    · have ha := (caseAFamily_dLattice_iff r).1 ((caseAFamily_iff _).2 (Or.inl h))
      rcases ha with h | h | h | h | h | h | h <;> subst r <;> decide
    all_goals
      have hc := h.card_eq
      have h2 : Nat.card (disjointTranspositions 6 2) = 4 := card_disjointTranspositions 2
      have h3 : Nat.card (D 6) = 8 := card_disjointTranspositions 3
      simp only [h2, h3, card_exceptional, card_evenPart, card_plus] at hc
      rw [card_dLattice] at hc
      have cert : ∀ r : Fin 16, 4 ≤ (dLatticeIndices r).card → 8 ≤ r.val := by decide
      exact Or.inr (Or.inr (Or.inr (cert r (by omega))))
  · intro h
    rcases h with rfl | rfl | rfl | hr
    · exact Or.inl ((caseAFamily_dLattice_iff 1).2 (by decide))
    · exact Or.inl ((caseAFamily_dLattice_iff 2).2 (by decide))
    · exact Or.inl ((caseAFamily_dLattice_iff 4).2 (by decide))
    · have hc := dLattice_conjugate r
      apply (caseBFamily_iff _).2
      fin_cases r <;> simp_all [dLatticeType, dRepresentative]

/-- Exact case-(a) list among subgroups of `D`. -/
theorem caseAFamily_le_D_iff (A : Subgroup Perm) :
    CaseAFamily 6 A ∧ A ≤ D 6 ↔
      A = dLattice 1 ∨ A = dLattice 2 ∨ A = dLattice 4 ∨
      A = dLattice 8 ∨ A = dLattice 9 ∨ A = dLattice 10 ∨ A = D 6 := by
  constructor
  · rintro ⟨h, hAD⟩
    obtain ⟨r, rfl⟩ := (subgroup_le_D_iff A).1 hAD
    rcases (caseAFamily_dLattice_iff r).1 h with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp
  · intro h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals rw [← dLattice_fifteen]
    all_goals refine ⟨(caseAFamily_dLattice_iff _).2 (by decide), ?_⟩
    all_goals first | exact le_rfl | (rw [dLattice_fifteen]; exact dLattice_le_D _)

/-- Exact case-(b) list among subgroups of `D`. -/
theorem caseBFamily_le_D_iff (A : Subgroup Perm) :
    CaseBFamily 6 (by decide) A ∧ A ≤ D 6 ↔
      A = dLattice 1 ∨ A = dLattice 2 ∨ A = dLattice 4 ∨
      A ⋖ D 6 ∨ A = D 6 := by
  constructor
  · rintro ⟨h, hAD⟩
    obtain ⟨r, rfl⟩ := (subgroup_le_D_iff A).1 hAD
    rcases (caseBFamily_dLattice_iff r).1 h with rfl | rfl | rfl | hr
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · by_cases h15 : r = 15
      · exact Or.inr (Or.inr (Or.inr (Or.inr (h15 ▸ dLattice_fifteen))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ((dLattice_covBy_D_iff r).2
          ⟨hr, by have := r.isLt; have : r.val ≠ 15 := fun h => h15 (Fin.ext h); omega⟩))))
  · intro h
    rcases h with rfl | rfl | rfl | h | rfl
    · exact ⟨(caseBFamily_dLattice_iff 1).2 (by decide), dLattice_le_D _⟩
    · exact ⟨(caseBFamily_dLattice_iff 2).2 (by decide), dLattice_le_D _⟩
    · exact ⟨(caseBFamily_dLattice_iff 4).2 (by decide), dLattice_le_D _⟩
    · obtain ⟨r, h1, _, rfl⟩ := (covBy_D_iff A).1 h
      exact ⟨(caseBFamily_dLattice_iff r).2 (Or.inr (Or.inr (Or.inr h1))), dLattice_le_D _⟩
    · rw [← dLattice_fifteen]
      exact ⟨(caseBFamily_dLattice_iff 15).2 (by decide), le_rfl⟩

/-- The seven involution lines of `D`, in word order. -/
def dLine (i : Fin 7) : Subgroup Perm := dLattice ⟨i.val + 1, by omega⟩

/-- The seven planes of `D`: coordinate planes first, then mixed planes,
then the even plane. -/
def dPlane (i : Fin 7) : Subgroup Perm := dLattice ⟨i.val + 8, by omega⟩

/-- Explicit generating pairs for all seven planes. The first three are
`⟨t₀,t₁⟩`, `⟨t₀,t₂⟩`, `⟨t₁,t₂⟩`; the next three are mixed planes. -/
def dPlaneGenerators : Fin 7 → Perm × Perm :=
  ![(pairSwap 6 0, pairSwap 6 1), (pairSwap 6 0, pairSwap 6 2),
    (pairSwap 6 1, pairSwap 6 2),
    (pairSwap 6 1 * pairSwap 6 2, pairSwap 6 0),
    (pairSwap 6 0 * pairSwap 6 2, pairSwap 6 1),
    (pairSwap 6 0 * pairSwap 6 1, pairSwap 6 2),
    (pairSwap 6 0 * pairSwap 6 1, pairSwap 6 0 * pairSwap 6 2)]

/-- Each listed line is generated by its indicated nonidentity word. -/
theorem dLine_eq_closure (i : Fin 7) :
    dLine i = Subgroup.closure {dWords ⟨i.val + 1, by omega⟩} := by
  apply le_antisymm
  · rintro g ⟨j, hj, rfl⟩
    have cert : ∀ i : Fin 7, ∀ j ∈ dLatticeIndices ⟨i.val + 1, by omega⟩,
        j = 0 ∨ j = ⟨i.val + 1, by omega⟩ := by decide
    rcases cert i j hj with rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure rfl
  · apply (Subgroup.closure_le _).2
    rintro g rfl
    apply (dWords_mem_dLattice _ _).2
    have cert : ∀ i : Fin 7, (⟨i.val + 1, by omega⟩ : Fin 8) ∈
        dLatticeIndices ⟨i.val + 1, by omega⟩ := by decide
    exact cert i

/-- Each listed plane is generated by the corresponding explicit pair. -/
theorem dPlane_eq_closure (i : Fin 7) :
    dPlane i = Subgroup.closure {(dPlaneGenerators i).1, (dPlaneGenerators i).2} := by
  have ha : (dPlaneGenerators i).1 ∈
      Subgroup.closure {(dPlaneGenerators i).1, (dPlaneGenerators i).2} :=
    Subgroup.subset_closure (Or.inl rfl)
  have hb : (dPlaneGenerators i).2 ∈
      Subgroup.closure {(dPlaneGenerators i).1, (dPlaneGenerators i).2} :=
    Subgroup.subset_closure (Or.inr rfl)
  apply le_antisymm
  · rintro g ⟨j, hj, rfl⟩
    have cert : ∀ i : Fin 7, ∀ j ∈ dLatticeIndices ⟨i.val + 8, by omega⟩,
        dWords j = 1 ∨ dWords j = (dPlaneGenerators i).1 ∨
        dWords j = (dPlaneGenerators i).2 ∨
        dWords j = (dPlaneGenerators i).1 * (dPlaneGenerators i).2 := by decide
    rcases cert i j hj with h | h | h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact ha
    · rw [h]; exact hb
    · rw [h]; exact Subgroup.mul_mem _ ha hb
  · apply (Subgroup.closure_le _).2
    have cert : ∀ i : Fin 7,
        (∃ j ∈ dLatticeIndices ⟨i.val + 8, by omega⟩, dWords j = (dPlaneGenerators i).1) ∧
        (∃ j ∈ dLatticeIndices ⟨i.val + 8, by omega⟩, dWords j = (dPlaneGenerators i).2) := by decide
    rintro g (rfl | hg)
    · exact (cert i).1
    · rw [Set.mem_singleton_iff] at hg
      subst g
      exact (cert i).2

theorem card_dLine (i : Fin 7) : Nat.card (dLine i) = 2 := by
  rw [dLine, card_dLattice]
  revert i
  decide

theorem card_dPlane (i : Fin 7) : Nat.card (dPlane i) = 4 := by
  rw [dPlane, card_dLattice]
  revert i
  decide

theorem dLine_injective : Function.Injective dLine := by
  intro i j h
  have h := congrArg Fin.val (dLattice_injective h)
  apply Fin.ext
  simpa using h

theorem dPlane_injective : Function.Injective dPlane := by
  intro i j h
  have h := congrArg Fin.val (dLattice_injective h)
  apply Fin.ext
  simpa using h

/-- The nontrivial subgroup list in seven-line, seven-plane, and whole-group form. -/
theorem nontrivial_subgroup_le_D_list (A : Subgroup Perm) :
    A ≤ D 6 ∧ A ≠ ⊥ ↔
      (∃ i : Fin 7, A = dLine i) ∨ (∃ i : Fin 7, A = dPlane i) ∨ A = D 6 := by
  rw [nontrivial_subgroup_le_D_iff]
  constructor
  · rintro ⟨r, hr, rfl⟩
    by_cases h7 : r.val < 8
    · left
      have h0 : 0 < r.val := by have : r.val ≠ 0 := fun h => hr (Fin.ext h); omega
      refine ⟨⟨r.val - 1, by omega⟩, ?_⟩
      apply congrArg dLattice
      apply Fin.ext
      dsimp
      omega
    · by_cases h15 : r = 15
      · exact Or.inr (Or.inr (h15 ▸ dLattice_fifteen))
      · right; left
        have hlt : r.val < 15 := by
          have : r.val ≠ 15 := fun h => h15 (Fin.ext h)
          have := r.isLt
          omega
        refine ⟨⟨r.val - 8, by omega⟩, ?_⟩
        apply congrArg dLattice
        apply Fin.ext
        dsimp
        omega
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩ | rfl)
    · exact ⟨⟨i.val + 1, by omega⟩, by intro h; have := congrArg Fin.val h; dsimp at this; omega, rfl⟩
    · exact ⟨⟨i.val + 8, by omega⟩, by intro h; have := congrArg Fin.val h; dsimp at this; omega, rfl⟩
    · exact ⟨15, by decide, dLattice_fifteen.symm⟩

/-- Exactly the seven explicitly generated planes are hyperplanes. -/
theorem covBy_D_list (A : Subgroup Perm) :
    A ⋖ D 6 ↔ ∃ i : Fin 7, A = dPlane i := by
  rw [covBy_D_iff]
  constructor
  · rintro ⟨r, h1, h2, rfl⟩
    refine ⟨⟨r.val - 8, by omega⟩, ?_⟩
    apply congrArg dLattice
    apply Fin.ext
    dsimp
    omega
  · rintro ⟨i, rfl⟩
    exact ⟨⟨i.val + 8, by omega⟩, by dsimp; omega, by dsimp; omega, rfl⟩

theorem dPlane_covBy_D (i : Fin 7) : dPlane i ⋖ D 6 :=
  (covBy_D_list _).2 ⟨i, rfl⟩

@[simp] theorem dPlane_zero : dPlane 0 = disjointTranspositions 6 2 := dLattice_eight
@[simp] theorem dPlane_five : dPlane 5 = plus := dLattice_thirteen
@[simp] theorem dPlane_six : dPlane 6 = evenPart 6 := dLattice_fourteen

/-- Removing the even plane leaves precisely the two hyperplane conjugacy types. -/
theorem hyperplaneFamily_iff (A : Subgroup Perm) : HyperplaneFamily 6 A ↔
    IsConjugateTo A (disjointTranspositions 6 2) ∨ IsConjugateTo A plus := by
  constructor
  · rintro ⟨B, hB, hne, hAB⟩
    rcases hyperplane_D_conjugacy hB with h | h | h
    · exact Or.inl (hAB.trans h)
    · exact Or.inr (hAB.trans h)
    · exact (hne h).elim
  · rintro (h | h)
    · refine ⟨disjointTranspositions 6 2, disjointTranspositions_two_covBy_D, ?_, h⟩
      rw [← dLattice_eight, ← dLattice_fourteen]
      exact fun he => (by decide : (8 : Fin 16) ≠ 14) (dLattice_injective he)
    · exact ⟨plus, plus_covBy_D, plus_ne_evenPart, h⟩

/-- The double- and triple-transposition lines have different conjugacy types. -/
theorem double_not_conjugate_triple : ¬IsConjugateTo double triple := by
  rintro ⟨g, hg⟩
  have hx : (MulAut.conj g) (lineWords 2 1) ∈ double := by
    rw [hg]
    exact Subgroup.mem_map_of_mem _ ((mem_triple_iff _).2 ⟨1, rfl⟩)
  obtain ⟨i, hi⟩ := (mem_double_iff _).1 hx
  have hc : ((MulAut.conj g) (lineWords 2 1)).support.card = 6 := by
    calc
      _ = (lineWords 2 1).support.card := Equiv.Perm.card_support_conj
      _ = 6 := by decide
  rw [← hi] at hc
  have hn : ∀ i : Fin 2, (lineWords 1 i).support.card ≠ 6 := by decide
  exact hn i hc

private def dRepresentativeProfile : Fin 8 → ℕ × ℕ :=
  ![(1,0), (2,1), (4,2), (8,3), (2,0), (2,0), (4,1), (4,0)]

private theorem dRepresentative_profile (r : Fin 8) :
    (Nat.card (dRepresentative r), transpositionCount (dRepresentative r)) =
      dRepresentativeProfile r := by
  rw [dRepresentative_eq, card_dLattice, transpositionCount_dLattice]
  revert r
  decide

/-- The seven nontrivial representatives, together with the trivial subgroup,
are pairwise nonconjugate. -/
theorem dRepresentative_conjugate_iff (r s : Fin 8) :
    IsConjugateTo (dRepresentative r) (dRepresentative s) ↔ r = s := by
  constructor
  · intro h
    have hp : dRepresentativeProfile r = dRepresentativeProfile s := by
      rw [← dRepresentative_profile r, ← dRepresentative_profile s,
        h.card_eq, transpositionCount_eq_of_conjugate h]
    have cert : ∀ r s : Fin 8, dRepresentativeProfile r = dRepresentativeProfile s →
        r = s ∨ (r = 4 ∧ s = 5) ∨ (r = 5 ∧ s = 4) := by decide
    rcases cert r s hp with he | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact he
    · exact (double_not_conjugate_triple h).elim
    · exact (double_not_conjugate_triple h.symm).elim
  · rintro rfl
    exact IsConjugateTo.refl _

/-- A complete classification up to ambient conjugacy of the cube subgroup list. -/
theorem dLattice_conjugate_iff (r s : Fin 16) :
    IsConjugateTo (dLattice r) (dLattice s) ↔ dLatticeType r = dLatticeType s := by
  constructor
  · intro h
    exact (dRepresentative_conjugate_iff _ _).1
      ((dLattice_conjugate r).symm.trans (h.trans (dLattice_conjugate s)))
  · intro h
    have hr := dLattice_conjugate r
    rw [h] at hr
    exact hr.trans (dLattice_conjugate s).symm

end CFSG.Quasithin.ChapterB.Offenders.Six
