module
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Defs
public import CFSG.Quasithin.ChapterB.Section03.Offenders.FixedTests
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Six.Representatives
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Six.Structure
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Six.Dimensions
public import Theory.Representation.BinaryOffender.PermutationConjugacy

/-!
# Exhaustive degree-six offender classification

The ten elementary abelian conjugacy types and their fixed dimensions determine
all offenders and strong offenders. Every offender is best: a subgroup of larger
weight would be strong, hence conjugate to the rank-three group `D`, and the
order bound forces it to equal the original group. This also gives the unique
strong best offender in the canonical Sylow subgroup and the equal-weight
inclusions used in B.3.4.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
1 March 2004 manuscript, Proposition B.3.2 and Lemma B.3.4, printed pp. 83–85.
-/

public section
namespace CFSG.Quasithin.ChapterB.Offenders.Six
open Representation.BinaryOffender BinaryPermutation

private theorem codim_conjugate {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) Perm V)
    {A B : Subgroup Perm} (h : IsConjugateTo A B) :
    fixedCodim ρ A = fixedCodim ρ B := by
  obtain ⟨g, rfl⟩ := h
  exact fixedCodim_map_conj ρ B g

/-- The first three disjoint-transposition representatives have their expected ranks. -/
theorem rank_A1 : rank (disjointTranspositions 6 1) = 1 := rank_disjointTranspositions 1

/-- The two-pair group has binary rank two. -/
theorem rank_A2 : rank (disjointTranspositions 6 2) = 2 := rank_disjointTranspositions 2

/-- The full disjoint-transposition group has binary rank three. -/
theorem rank_D : rank (D 6) = 3 := rank_disjointTranspositions 3

/-- All nontrivial elementary abelian subgroups of `S₆` have rank at most three. -/
theorem rank_le_three {A : Subgroup Perm} (hA : IsElementaryTwo A) : rank A ≤ 3 := by
  rcases elementaryTwo_conjugacy hA with h | h | h | h | h | h | h | h | h | h
  · rw [h.rank_eq, rank_A1]; decide
  · rw [h.rank_eq, rank_A2]; decide
  · rw [h.rank_eq, rank_D]
  · rw [h.rank_eq, rank_exceptional]
  · rw [h.rank_eq, rank_evenPart]; decide
  · rw [h.rank_eq, rank_plus]; decide
  · rw [h.rank_eq, rank_double]; decide
  · rw [h.rank_eq, rank_triple]; decide
  · rw [h.rank_eq, rank_klein]; decide
  · rw [h.rank_eq, rank_twisted]; decide

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

private structure CodimTable (ρ : Representation (ZMod 2) Perm V) (b : Bool) : Prop where
  a1 : fixedCodim ρ (disjointTranspositions 6 1) = 1
  a2 : fixedCodim ρ (disjointTranspositions 6 2) = 2
  d : fixedCodim ρ (D 6) = if b then 2 else 3
  exceptional : fixedCodim ρ (exceptional 6 (by decide)) = if b then 3 else 4
  even : fixedCodim ρ (evenPart 6) = if b then 2 else 3
  plus : fixedCodim ρ plus = if b then 2 else 3
  double : fixedCodim ρ double = 2
  triple : 2 ≤ fixedCodim ρ triple
  klein : fixedCodim ρ klein = 3
  twisted : 3 ≤ fixedCodim ρ twisted

private theorem strong_iff (ρ : Representation (ZMod 2) Perm V) (b : Bool)
    (t : CodimTable ρ b) (A : Subgroup Perm) :
    IsStrongOffender ρ A ↔ b = true ∧ IsConjugateTo A (D 6) := by
  constructor
  · rintro ⟨hA, hlt⟩
    rcases elementaryTwo_conjugacy hA with h | h | h | h | h | h | h | h | h | h
    · rw [codim_conjugate ρ h, h.rank_eq, rank_A1] at hlt
      have hc := t.a1
      cases b <;> simp_all
    · rw [codim_conjugate ρ h, h.rank_eq, rank_A2] at hlt
      have hc := t.a2
      cases b <;> simp_all
    · rw [codim_conjugate ρ h, h.rank_eq, rank_D] at hlt
      have hc := t.d
      exact ⟨by cases b <;> simp_all, h⟩
    · rw [codim_conjugate ρ h, h.rank_eq, rank_exceptional] at hlt
      have hc := t.exceptional
      cases b <;> simp_all
    · rw [codim_conjugate ρ h, h.rank_eq, rank_evenPart] at hlt
      have hc := t.even
      cases b <;> simp_all
    · rw [codim_conjugate ρ h, h.rank_eq, rank_plus] at hlt
      have hc := t.plus
      cases b <;> simp_all
    · rw [codim_conjugate ρ h, h.rank_eq, rank_double] at hlt
      have hc := t.double
      cases b <;> simp_all
    · rw [codim_conjugate ρ h, h.rank_eq, rank_triple] at hlt
      have hc := t.triple
      omega
    · rw [codim_conjugate ρ h, h.rank_eq, rank_klein] at hlt
      have hc := t.klein
      cases b <;> simp_all
    · rw [codim_conjugate ρ h, h.rank_eq, rank_twisted] at hlt
      have hc := t.twisted
      omega
  · rintro ⟨rfl, h⟩
    refine ⟨h.isElementaryTwo (isElementaryTwo_disjointTranspositions 3 (by decide)), ?_⟩
    rw [codim_conjugate ρ h, h.rank_eq, rank_D, t.d]; decide

private theorem offender_iff (ρ : Representation (ZMod 2) Perm V) (b : Bool)
    (t : CodimTable ρ b) (A : Subgroup Perm) :
    IsOffender ρ A ↔ if b then CaseBFamily 6 (by decide) A else CaseAFamily 6 A := by
  constructor
  · rintro ⟨hA, hle⟩
    rcases elementaryTwo_conjugacy hA with h | h | h | h | h | h | h | h | h | h
    · rw [codim_conjugate ρ h, h.rank_eq, rank_A1] at hle
      have hc := t.a1
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, caseAFamily_iff, caseBFamily_iff]
      all_goals tauto
    · rw [codim_conjugate ρ h, h.rank_eq, rank_A2] at hle
      have hc := t.a2
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, caseAFamily_iff, caseBFamily_iff]
      all_goals tauto
    · rw [codim_conjugate ρ h, h.rank_eq, rank_D] at hle
      have hc := t.d
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, caseAFamily_iff, caseBFamily_iff]
      all_goals tauto
    · rw [codim_conjugate ρ h, h.rank_eq, rank_exceptional] at hle
      have hc := t.exceptional
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, caseAFamily_iff, caseBFamily_iff]
      all_goals first | tauto | simp_all
    · rw [codim_conjugate ρ h, h.rank_eq, rank_evenPart] at hle
      have hc := t.even
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, caseAFamily_iff, caseBFamily_iff]
      all_goals first | tauto | simp_all
    · rw [codim_conjugate ρ h, h.rank_eq, rank_plus] at hle
      have hc := t.plus
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, caseAFamily_iff, caseBFamily_iff]
      all_goals first | tauto | simp_all
    · rw [codim_conjugate ρ h, h.rank_eq, rank_double] at hle
      have hc := t.double
      omega
    · rw [codim_conjugate ρ h, h.rank_eq, rank_triple] at hle
      have hc := t.triple
      omega
    · rw [codim_conjugate ρ h, h.rank_eq, rank_klein] at hle
      have hc := t.klein
      omega
    · rw [codim_conjugate ρ h, h.rank_eq, rank_twisted] at hle
      have hc := t.twisted
      omega
  · intro h
    have he : IsElementaryTwo A := by
      cases b
      · exact caseBFamily_isElementaryTwo (Or.inl h)
      · exact caseBFamily_isElementaryTwo h
    refine ⟨he, ?_⟩
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, caseAFamily_iff] at h
      rcases h with h | h | h
      · rw [codim_conjugate ρ h, h.rank_eq, rank_A1, t.a1]
      · rw [codim_conjugate ρ h, h.rank_eq, rank_A2, t.a2]
      · rw [codim_conjugate ρ h, h.rank_eq, rank_D, t.d]
        decide
    · simp only [↓reduceIte, caseBFamily_iff] at h
      rcases h with h | h | h | h | h | h
      · rw [codim_conjugate ρ h, h.rank_eq, rank_A1, t.a1]
      · rw [codim_conjugate ρ h, h.rank_eq, rank_A2, t.a2]
      · rw [codim_conjugate ρ h, h.rank_eq, rank_D, t.d]
        decide
      · rw [codim_conjugate ρ h, h.rank_eq, rank_exceptional, t.exceptional]
        decide
      · rw [codim_conjugate ρ h, h.rank_eq, rank_evenPart, t.even]
        decide
      · rw [codim_conjugate ρ h, h.rank_eq, rank_plus, t.plus]
        decide

private theorem best_iff_offender (ρ : Representation (ZMod 2) Perm V) (b : Bool)
    (t : CodimTable ρ b) (A : Subgroup Perm) :
    IsBestOffender ρ A ↔ IsOffender ρ A := by
  refine ⟨fun h => h.isOffender ρ, fun h => ⟨h.1, ?_⟩⟩
  intro B hBA
  by_cases hB : B = ⊥
  · subst B
    rw [weight_bot]
    exact (fixedCodim_le_rank_iff ρ A).1 h.2
  · have he := h.1.of_le hBA hB
    by_cases hs : IsStrongOffender ρ B
    · have hc := ((strong_iff ρ b t B).1 hs).2
      have hr : rank B = 3 := hc.rank_eq.trans rank_D
      have hcard : Nat.card A ≤ Nat.card B := by
        rw [h.1.card_eq_two_pow_rank, he.card_eq_two_pow_rank, hr]
        exact Nat.pow_le_pow_right (by decide) (rank_le_three h.1)
      have heq : B = A := Subgroup.eq_of_le_of_card_ge hBA hcard
      exact heq ▸ le_rfl
    · have hw : weight ρ B ≤ Module.finrank (ZMod 2) V := by
        have hn : ¬fixedCodim ρ B < rank B := fun hlt => hs ⟨he, hlt⟩
        have hf := fixedCodim_add_finrank ρ B
        unfold weight
        omega
      exact hw.trans ((fixedCodim_le_rank_iff ρ A).1 h.2)

private theorem fullTable : CodimTable (representation (Fin 6)) false := by
  refine ⟨fixedCodim_A1.1, fixedCodim_A2.1, fixedCodim_D.1,
    fixedCodim_exceptional.1, fixedCodim_evenPart.1, fixedCodim_plus.1, fixedCodim_double.1,
    ?_, fixedCodim_klein.1, ?_⟩
  · have := fixedCodim_triple.1
    omega
  · have := fixedCodim_twisted.1
    omega

/-- The complete offender classification for the full representation. -/
theorem isOffender_full_iff (A : Subgroup Perm) :
    IsOffender (representation (Fin 6)) A ↔ CaseAFamily 6 A :=
  offender_iff _ false fullTable A

/-- Proposition B.3.2: the complete best-offender classification for the full representation. -/
theorem isBestOffender_full_iff (A : Subgroup Perm) :
    IsBestOffender (representation (Fin 6)) A ↔ CaseAFamily 6 A :=
  (best_iff_offender _ false fullTable A).trans (isOffender_full_iff A)

/-- The full representation has no strong offenders. -/
theorem not_isStrongOffender_full (A : Subgroup Perm) :
    ¬IsStrongOffender (representation (Fin 6)) A := by
  rw [strong_iff _ false fullTable A]
  simp

private theorem deletedTable : CodimTable (deletedRepresentation (Fin 6)) false := by
  refine ⟨fixedCodim_A1.2.1, fixedCodim_A2.2.1, fixedCodim_D.2.1,
    fixedCodim_exceptional.2.1, fixedCodim_evenPart.2.1, fixedCodim_plus.2.1, fixedCodim_double.2.1,
    ?_, fixedCodim_klein.2.1, ?_⟩
  · have := fixedCodim_triple.2.1
    omega
  · have := fixedCodim_twisted.2.1
    omega

/-- The complete offender classification for the deleted representation. -/
theorem isOffender_deleted_iff (A : Subgroup Perm) :
    IsOffender (deletedRepresentation (Fin 6)) A ↔ CaseAFamily 6 A :=
  offender_iff _ false deletedTable A

/-- Proposition B.3.2: the complete best-offender classification for the deleted representation. -/
theorem isBestOffender_deleted_iff (A : Subgroup Perm) :
    IsBestOffender (deletedRepresentation (Fin 6)) A ↔ CaseAFamily 6 A :=
  (best_iff_offender _ false deletedTable A).trans (isOffender_deleted_iff A)

/-- The deleted representation has no strong offenders. -/
theorem not_isStrongOffender_deleted (A : Subgroup Perm) :
    ¬IsStrongOffender (deletedRepresentation (Fin 6)) A := by
  rw [strong_iff _ false deletedTable A]
  simp

private theorem coreTable : CodimTable (coreRepresentation (Fin 6)) true := by
  refine ⟨fixedCodim_A1.2.2.1, fixedCodim_A2.2.2.1, fixedCodim_D.2.2.1,
    fixedCodim_exceptional.2.2.1, fixedCodim_evenPart.2.2.1, fixedCodim_plus.2.2.1, fixedCodim_double.2.2.1,
    ?_, fixedCodim_klein.2.2.1, ?_⟩
  · have := fixedCodim_triple.2.2.1
    omega
  · have := fixedCodim_twisted.2.2.1
    omega

/-- The complete offender classification for the core representation. -/
theorem isOffender_core_iff (A : Subgroup Perm) :
    IsOffender (coreRepresentation (Fin 6)) A ↔ CaseBFamily 6 (by decide) A :=
  offender_iff _ true coreTable A

/-- Proposition B.3.2: the complete best-offender classification for the core representation. -/
theorem isBestOffender_core_iff (A : Subgroup Perm) :
    IsBestOffender (coreRepresentation (Fin 6)) A ↔ CaseBFamily 6 (by decide) A :=
  (best_iff_offender _ true coreTable A).trans (isOffender_core_iff A)

/-- Strong offenders on the core representation are precisely the conjugates of `D`. -/
theorem isStrongOffender_core_iff (A : Subgroup Perm) :
    IsStrongOffender (coreRepresentation (Fin 6)) A ↔ IsConjugateTo A (D 6) := by
  simpa using strong_iff _ true coreTable A

/-- `D` is the unique strong best offender in the canonical Sylow subgroup. -/
theorem strong_best_core_le_sylowCarrier_iff (A : Subgroup Perm) :
    (IsBestOffender (coreRepresentation (Fin 6)) A ∧ IsStrongOffender (coreRepresentation (Fin 6)) A ∧
      A ≤ sylowCarrier) ↔ A = D 6 := by
  constructor
  · rintro ⟨_, hs, hT⟩
    exact eq_D_of_le_sylowCarrier_of_conjugate hT ((isStrongOffender_core_iff A).1 hs)
  · rintro rfl
    exact ⟨(isBestOffender_core_iff _).2 (Or.inl
      (caseAFamily_disjointTranspositions (by decide) (by decide))),
      (isStrongOffender_core_iff _).2 (IsConjugateTo.refl _), D_le_sylowCarrier⟩

private theorem naturalTable : CodimTable (naturalRepresentation (Fin 6)) true := by
  refine ⟨fixedCodim_A1.2.2.2, fixedCodim_A2.2.2.2, fixedCodim_D.2.2.2,
    fixedCodim_exceptional.2.2.2, fixedCodim_evenPart.2.2.2, fixedCodim_plus.2.2.2, fixedCodim_double.2.2.2,
    ?_, fixedCodim_klein.2.2.2, ?_⟩
  · have := fixedCodim_triple.2.2.2
    omega
  · have := fixedCodim_twisted.2.2.2
    omega

/-- The complete offender classification for the natural representation. -/
theorem isOffender_natural_iff (A : Subgroup Perm) :
    IsOffender (naturalRepresentation (Fin 6)) A ↔ CaseBFamily 6 (by decide) A :=
  offender_iff _ true naturalTable A

/-- Proposition B.3.2: the complete best-offender classification for the natural representation. -/
theorem isBestOffender_natural_iff (A : Subgroup Perm) :
    IsBestOffender (naturalRepresentation (Fin 6)) A ↔ CaseBFamily 6 (by decide) A :=
  (best_iff_offender _ true naturalTable A).trans (isOffender_natural_iff A)

/-- Strong offenders on the natural representation are precisely the conjugates of `D`. -/
theorem isStrongOffender_natural_iff (A : Subgroup Perm) :
    IsStrongOffender (naturalRepresentation (Fin 6)) A ↔ IsConjugateTo A (D 6) := by
  simpa using strong_iff _ true naturalTable A

/-- `D` is the unique strong best offender in the canonical Sylow subgroup. -/
theorem strong_best_natural_le_sylowCarrier_iff (A : Subgroup Perm) :
    (IsBestOffender (naturalRepresentation (Fin 6)) A ∧ IsStrongOffender (naturalRepresentation (Fin 6)) A ∧
      A ≤ sylowCarrier) ↔ A = D 6 := by
  constructor
  · rintro ⟨_, hs, hT⟩
    exact eq_D_of_le_sylowCarrier_of_conjugate hT ((isStrongOffender_natural_iff A).1 hs)
  · rintro rfl
    exact ⟨(isBestOffender_natural_iff _).2 (Or.inl
      (caseAFamily_disjointTranspositions (by decide) (by decide))),
      (isStrongOffender_natural_iff _).2 (IsConjugateTo.refl _), D_le_sylowCarrier⟩

/-- The last transposition has equal weight in `tailTwo`, as used in B.3.4. -/
theorem equalWeightLE_last_tailTwo_core :
    EqualWeightLE (coreRepresentation (Fin 6)) last tailTwo := by
  refine ⟨last_le_tailTwo, ?_⟩
  simp only [weight, rank_last, rank_tailTwo, finrank_fixedSpace_last.2.2.1,
    finrank_fixedSpace_tailTwo.2.2.1]

/-- The last transposition has equal weight in `plus`, as used in B.3.4. -/
theorem equalWeightLE_last_plus_core :
    EqualWeightLE (coreRepresentation (Fin 6)) last plus := by
  refine ⟨last_le_plus, ?_⟩
  simp only [weight, rank_last, rank_plus, finrank_fixedSpace_last.2.2.1,
    finrank_fixedSpace_plus.2.2.1]

/-- The last transposition has equal weight in `exceptional`, as used in B.3.4. -/
theorem equalWeightLE_last_exceptional_core :
    EqualWeightLE (coreRepresentation (Fin 6)) last (exceptional 6 (by decide)) := by
  refine ⟨last_le_exceptional, ?_⟩
  simp only [weight, rank_last, rank_exceptional, finrank_fixedSpace_last.2.2.1,
    finrank_fixedSpace_exceptional.2.2.1]

/-- The complete fourteen-member best-offender list in the canonical Sylow subgroup. -/
theorem best_core_le_sylowCarrier_list (A : Subgroup Perm) :
    (IsBestOffender (coreRepresentation (Fin 6)) A ∧ A ≤ sylowCarrier) ↔
      ∃ i, A = sylowCaseBMember i := by
  rw [isBestOffender_core_iff, caseBFamily_le_sylowCarrier_list]

/-- The even best offenders are precisely the conjugates of the even part of `D`. -/
theorem best_core_even_iff (A : Subgroup Perm) :
    (IsBestOffender (coreRepresentation (Fin 6)) A ∧ A ≤ alternatingGroup (Fin 6)) ↔
      IsConjugateTo A (evenPart 6) := by
  rw [isBestOffender_core_iff, caseBFamily_even_iff]

/-- Inside the canonical Sylow subgroup there is exactly one even best offender. -/
theorem best_core_even_le_sylowCarrier_iff (A : Subgroup Perm) :
    (IsBestOffender (coreRepresentation (Fin 6)) A ∧ A ≤ sylowCarrier ∧
      A ≤ alternatingGroup (Fin 6)) ↔ A = evenPart 6 := by
  rw [isBestOffender_core_iff, caseBFamily_even_le_sylowCarrier_iff]

/-- The last transposition has equal weight in `tailTwo`, as used in B.3.4. -/
theorem equalWeightLE_last_tailTwo_natural :
    EqualWeightLE (naturalRepresentation (Fin 6)) last tailTwo := by
  refine ⟨last_le_tailTwo, ?_⟩
  simp only [weight, rank_last, rank_tailTwo, finrank_fixedSpace_last.2.2.2,
    finrank_fixedSpace_tailTwo.2.2.2]

/-- The last transposition has equal weight in `plus`, as used in B.3.4. -/
theorem equalWeightLE_last_plus_natural :
    EqualWeightLE (naturalRepresentation (Fin 6)) last plus := by
  refine ⟨last_le_plus, ?_⟩
  simp only [weight, rank_last, rank_plus, finrank_fixedSpace_last.2.2.2,
    finrank_fixedSpace_plus.2.2.2]

/-- The last transposition has equal weight in `exceptional`, as used in B.3.4. -/
theorem equalWeightLE_last_exceptional_natural :
    EqualWeightLE (naturalRepresentation (Fin 6)) last (exceptional 6 (by decide)) := by
  refine ⟨last_le_exceptional, ?_⟩
  simp only [weight, rank_last, rank_exceptional, finrank_fixedSpace_last.2.2.2,
    finrank_fixedSpace_exceptional.2.2.2]

/-- The complete fourteen-member best-offender list in the canonical Sylow subgroup. -/
theorem best_natural_le_sylowCarrier_list (A : Subgroup Perm) :
    (IsBestOffender (naturalRepresentation (Fin 6)) A ∧ A ≤ sylowCarrier) ↔
      ∃ i, A = sylowCaseBMember i := by
  rw [isBestOffender_natural_iff, caseBFamily_le_sylowCarrier_list]

/-- The even best offenders are precisely the conjugates of the even part of `D`. -/
theorem best_natural_even_iff (A : Subgroup Perm) :
    (IsBestOffender (naturalRepresentation (Fin 6)) A ∧ A ≤ alternatingGroup (Fin 6)) ↔
      IsConjugateTo A (evenPart 6) := by
  rw [isBestOffender_natural_iff, caseBFamily_even_iff]

/-- Inside the canonical Sylow subgroup there is exactly one even best offender. -/
theorem best_natural_even_le_sylowCarrier_iff (A : Subgroup Perm) :
    (IsBestOffender (naturalRepresentation (Fin 6)) A ∧ A ≤ sylowCarrier ∧
      A ≤ alternatingGroup (Fin 6)) ↔ A = evenPart 6 := by
  rw [isBestOffender_natural_iff, caseBFamily_even_le_sylowCarrier_iff]

/-- The complete seven-member best-offender list in the canonical Sylow subgroup. -/
theorem best_full_le_sylowCarrier_iff (A : Subgroup Perm) :
    (IsBestOffender (representation (Fin 6)) A ∧ A ≤ sylowCarrier) ↔
      A = dLattice 1 ∨ A = dLattice 2 ∨ A = dLattice 4 ∨
      A = dLattice 8 ∨ A = dLattice 9 ∨ A = dLattice 10 ∨ A = D 6 := by
  rw [isBestOffender_full_iff, caseAFamily_le_sylowCarrier_iff]

/-- The complete seven-member best-offender list in the canonical Sylow subgroup. -/
theorem best_deleted_le_sylowCarrier_iff (A : Subgroup Perm) :
    (IsBestOffender (deletedRepresentation (Fin 6)) A ∧ A ≤ sylowCarrier) ↔
      A = dLattice 1 ∨ A = dLattice 2 ∨ A = dLattice 4 ∨
      A = dLattice 8 ∨ A = dLattice 9 ∨ A = dLattice 10 ∨ A = D 6 := by
  rw [isBestOffender_deleted_iff, caseAFamily_le_sylowCarrier_iff]

/-- All seven hyperplanes of `D` have rank two and codimension two on core
and natural. On full and deleted their common codimension is two or three. -/
theorem hyperplane_dimensions {A : Subgroup Perm} (hA : A ⋖ D 6) :
    rank A = 2 ∧
    fixedCodim (coreRepresentation (Fin 6)) A = 2 ∧
    fixedCodim (naturalRepresentation (Fin 6)) A = 2 ∧
    ((fixedCodim (representation (Fin 6)) A = 2 ∧
      fixedCodim (deletedRepresentation (Fin 6)) A = 2) ∨
     (fixedCodim (representation (Fin 6)) A = 3 ∧
      fixedCodim (deletedRepresentation (Fin 6)) A = 3)) := by
  rcases hyperplane_D_conjugacy hA with h | h | rfl
  · simp only [h.rank_eq, rank_A2, codim_conjugate _ h,
      fixedCodim_A2.1, fixedCodim_A2.2.1, fixedCodim_A2.2.2.1, fixedCodim_A2.2.2.2,
      true_and, true_or]
  · simp only [h.rank_eq, rank_plus, codim_conjugate _ h,
      fixedCodim_plus.1, fixedCodim_plus.2.1, fixedCodim_plus.2.2.1, fixedCodim_plus.2.2.2,
      true_and, or_true]
  · simp only [rank_evenPart,
      fixedCodim_evenPart.1, fixedCodim_evenPart.2.1, fixedCodim_evenPart.2.2.1,
      fixedCodim_evenPart.2.2.2, true_and, or_true]

end CFSG.Quasithin.ChapterB.Offenders.Six
