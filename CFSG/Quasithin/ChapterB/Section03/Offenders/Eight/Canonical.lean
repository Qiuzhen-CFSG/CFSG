module

public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Canonical.Dimensions
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Canonical.Conjugacy
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Canonical.Coordinates
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Canonical.DBounds
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Canonical.ExceptionalBest
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Canonical.Hyperplanes
public import Theory.Representation.BinaryPermutation.OrbitFixedSpace
public import Theory.GroupAction.AbelianPermutationOrbitBound

/-!
# Canonical degree-eight offender calculations

The concrete word tables prove the ranks of the disjoint-swap and exceptional
groups; fixed-vector counts prove their fixed codimensions on all four sections.
Every hyperplane of `D` is a kernel of a nonzero binary form on its four swap
coordinates. The quotient calculations retain constant-displacement fixed vectors.

The abelian orbit bound and the all-subgroup bounds inside `D` and the exceptional
group establish best offending for every case-(a) family on the full and deleted
modules and every case-(b) family on the core and natural modules. In particular,
all hyperplanes are covered, including the even part. Conjugacy transports the
ranks, fixed spaces and best-offender comparisons. Among the canonical case-(b)
groups, precisely the conjugates of `D` are strong. The additional regular family
and the necessity directions belong to the separate degree-eight developments.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Proposition B.3.2(1),(2) and the sufficiency directions of (4)–(6), printed pp. 83–84.
-/

public section
namespace CFSG.Quasithin.ChapterB.Offenders.Eight
open BinaryPermutation Representation.BinaryOffender

/-- Exact fixed codimensions for all four disjoint-swap representatives. -/
theorem fixedCodim_disjointTranspositions {m : ℕ} (hm0 : 1 ≤ m) (hm : m ≤ 4) :
    fixedCodim (representation (Fin 8)) (disjointTranspositions 8 m) = m ∧
    fixedCodim (deletedRepresentation (Fin 8)) (disjointTranspositions 8 m) = m ∧
    fixedCodim (coreRepresentation (Fin 8)) (disjointTranspositions 8 m) =
      (if m = 4 then 3 else m) ∧
    fixedCodim (naturalRepresentation (Fin 8)) (disjointTranspositions 8 m) =
      (if m = 4 then 3 else m) := by
  interval_cases m
  · exact fixedCodim_A1
  · exact fixedCodim_A2
  · exact fixedCodim_A3
  · exact fixedCodim_D

/-- Both case-(a) sections give codimension equal to rank on this family. -/
theorem caseAFamily_rank_codim {A : Subgroup Perm} (hA : CaseAFamily 8 A) :
    IsElementaryTwo A ∧
    fixedCodim (representation (Fin 8)) A = rank A ∧
    fixedCodim (deletedRepresentation (Fin 8)) A = rank A := by
  obtain ⟨m, hm0, hm, hconj⟩ := hA
  have hm4 : m ≤ 4 := hm
  have hr := rank_disjointTranspositions (⟨m, by omega⟩ : Fin 5)
  have hc := fixedCodim_disjointTranspositions hm0 hm4
  refine ⟨hconj.isElementaryTwo (isElementaryTwo_disjointTranspositions
    ⟨m, by omega⟩ hm0), ?_, ?_⟩
  · rw [hconj.fixedCodim_eq, hconj.rank_eq, hc.1, hr]
  · rw [hconj.fixedCodim_eq, hconj.rank_eq, hc.2.1, hr]

/-- The elementary abelian orbit bound applies in even degree as well. -/
theorem rank_le_fixedCodim_full {A : Subgroup Perm} (hA : IsElementaryTwo A) :
    rank A ≤ fixedCodim (representation (Fin 8)) A := by
  let _ : IsElementaryAbelian 2 A := hA.2
  apply (Nat.pow_le_pow_iff_right (a := 2) (by decide)).mp
  rw [← hA.card_eq_two_pow_rank, fixedCodim_full_eq_card_sub_card_orbits]
  exact AbelianPermutation.card_le_two_pow_degree_sub_orbits A

/-- Every case-(a) representative and its conjugates are best on the full module. -/
theorem isBestOffender_full_of_caseAFamily {A : Subgroup Perm} (hA : CaseAFamily 8 A) :
    IsBestOffender (representation (Fin 8)) A := by
  apply (isBestOffender_iff_of_not_strong (representation (Fin 8)) ?_ A).mpr
  · exact ⟨(caseAFamily_rank_codim hA).1, (caseAFamily_rank_codim hA).2.1⟩
  · rintro ⟨B, hB, hlt⟩
    exact (Nat.not_lt_of_ge (rank_le_fixedCodim_full hB)) hlt

/-- The deleted representatives satisfy the offender inequality. -/
theorem isOffender_deleted_of_caseAFamily {A : Subgroup Perm} (hA : CaseAFamily 8 A) :
    IsOffender (deletedRepresentation (Fin 8)) A :=
  ⟨(caseAFamily_rank_codim hA).1, (caseAFamily_rank_codim hA).2.2.le⟩

/-- Every disjoint-swap representative offends on both case-(b) sections. -/
theorem isOffender_core_natural_disjointTranspositions (m : Fin 5) (hm : 0 < m.val) :
    IsOffender (coreRepresentation (Fin 8)) (disjointTranspositions 8 m.val) ∧
    IsOffender (naturalRepresentation (Fin 8)) (disjointTranspositions 8 m.val) := by
  have h := fixedCodim_disjointTranspositions hm (by have := m.isLt; omega)
  have hr := rank_disjointTranspositions m
  have hi := isElementaryTwo_disjointTranspositions m hm
  constructor
  · refine ⟨hi, ?_⟩
    rw [h.2.2.1, hr]
    split_ifs <;> omega
  · refine ⟨hi, ?_⟩
    rw [h.2.2.2, hr]
    split_ifs <;> omega

/-- The exceptional group has rank and case-(b) codimensions all equal to four. -/
theorem exceptional_rank_codim :
    rank (exceptional 8 (by decide)) = 4 ∧
    fixedCodim (coreRepresentation (Fin 8)) (exceptional 8 (by decide)) = 4 ∧
    fixedCodim (naturalRepresentation (Fin 8)) (exceptional 8 (by decide)) = 4 :=
  ⟨rank_exceptional, fixedCodim_exceptional.2.2⟩

theorem isOffender_core_exceptional :
    IsOffender (coreRepresentation (Fin 8)) (exceptional 8 (by decide)) := by
  refine ⟨isElementaryTwo_exceptional, ?_⟩
  rw [rank_exceptional, fixedCodim_exceptional.2.2.1]

theorem isOffender_natural_exceptional :
    IsOffender (naturalRepresentation (Fin 8)) (exceptional 8 (by decide)) := by
  refine ⟨isElementaryTwo_exceptional, ?_⟩
  rw [rank_exceptional, fixedCodim_exceptional.2.2.2]

/-- The strong-offender statements for `D` have no unproved rank premise. -/
theorem isStrongOffender_core_D : IsStrongOffender (coreRepresentation (Fin 8)) (D 8) :=
  D8_strong_core rank_D

theorem isStrongOffender_natural_D :
    IsStrongOffender (naturalRepresentation (Fin 8)) (D 8) := by
  refine ⟨isElementaryTwo_D8, ?_⟩
  rw [rank_D, fixedCodim_D.2.2.2]
  decide


/-- The full fixed-space data transports under an ambient conjugacy. -/
theorem HasDimensions.of_isConjugateTo {A B : Subgroup Perm} {a b c d : ℕ}
    (hB : HasDimensions B a b c d) (h : IsConjugateTo A B) :
    HasDimensions A a b c d := by
  unfold HasDimensions at *
  simpa only [h.finrank_fixedSpace_eq] using hB

/-- Exact fixed dimensions of the four disjoint-swap groups on all four sections. -/
theorem finrank_fixedSpace_disjointTranspositions {m : ℕ} (hm0 : 1 ≤ m) (hm : m ≤ 4) :
    HasDimensions (disjointTranspositions 8 m) (8 - m) (7 - m)
      (if m = 4 then 4 else 7 - m) (if m = 4 then 3 else 6 - m) := by
  interval_cases m
  · exact finrank_fixedSpace_A1
  · exact finrank_fixedSpace_A2
  · exact finrank_fixedSpace_A3
  · exact finrank_fixedSpace_D

/-- B.3.2(4), deleted-module sufficiency, with comparison against every subgroup. -/
theorem isBestOffender_deleted_of_caseAFamily {A : Subgroup Perm} (hA : CaseAFamily 8 A) :
    IsBestOffender (deletedRepresentation (Fin 8)) A := by
  obtain ⟨m, hm0, hm, hconj⟩ := hA
  exact hconj.isBestOffender _
    (isBestOffender_deleted_disjointTranspositions ⟨m, by omega⟩ hm0)

/-- Every disjoint-swap group and its conjugates are best offenders on the core. -/
theorem isBestOffender_core_of_caseAFamily {A : Subgroup Perm} (hA : CaseAFamily 8 A) :
    IsBestOffender (coreRepresentation (Fin 8)) A := by
  obtain ⟨m, hm0, hm, hconj⟩ := hA
  exact hconj.isBestOffender _
    (isBestOffender_core_disjointTranspositions ⟨m, by omega⟩ hm0)

/-- Every disjoint-swap group and its conjugates are best on the natural module. -/
theorem isBestOffender_natural_of_caseAFamily {A : Subgroup Perm} (hA : CaseAFamily 8 A) :
    IsBestOffender (naturalRepresentation (Fin 8)) A := by
  obtain ⟨m, hm0, hm, hconj⟩ := hA
  exact hconj.isBestOffender _
    (isBestOffender_natural_disjointTranspositions ⟨m, by omega⟩ hm0)

private theorem bestOffender_hyperplane {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) Perm V)
    {H : Subgroup Perm} (hH : H ⋖ D 8) (hc : fixedCodim ρ H = 3)
    (hb : ∀ B < D 8, rank B ≤ fixedCodim ρ B) : IsBestOffender ρ H := by
  refine ⟨isElementaryTwo_hyperplane hH, ?_⟩
  intro B hB
  have hbound := hb B (lt_of_le_of_lt hB hH.lt)
  have hr := rank_hyperplane hH
  have hdimH := fixedCodim_add_finrank ρ H
  have hdimB := fixedCodim_add_finrank ρ B
  unfold weight
  omega

/-- Every hyperplane of `D`, with no restriction on its support, is best on the core. -/
theorem isBestOffender_core_hyperplane {H : Subgroup Perm} (hH : H ⋖ D 8) :
    IsBestOffender (coreRepresentation (Fin 8)) H :=
  bestOffender_hyperplane _ hH (fixedCodim_hyperplane hH).1
    (fun _ hB => rank_le_fixedCodim_core_of_lt_D hB)

/-- Every hyperplane of `D` is best on the natural module. -/
theorem isBestOffender_natural_hyperplane {H : Subgroup Perm} (hH : H ⋖ D 8) :
    IsBestOffender (naturalRepresentation (Fin 8)) H :=
  bestOffender_hyperplane _ hH (fixedCodim_hyperplane hH).2
    (fun _ hB => rank_le_fixedCodim_natural_of_lt_D hB)

theorem isBestOffender_core_evenPart :
    IsBestOffender (coreRepresentation (Fin 8)) (evenPart 8) :=
  isBestOffender_core_hyperplane evenPart_covBy_D

theorem isBestOffender_natural_evenPart :
    IsBestOffender (naturalRepresentation (Fin 8)) (evenPart 8) :=
  isBestOffender_natural_hyperplane evenPart_covBy_D

/-- B.3.2(5), sufficiency for every canonical family on the degree-eight core. -/
theorem isBestOffender_core_of_caseBFamily {A : Subgroup Perm}
    (hA : CaseBFamily 8 (by decide) A) : IsBestOffender (coreRepresentation (Fin 8)) A := by
  rcases hA with hA | hA | hA | ⟨H, hH, _, hconj⟩
  · exact isBestOffender_core_of_caseAFamily hA
  · exact hA.isBestOffender _ isBestOffender_exceptional_core
  · exact hA.isBestOffender _ isBestOffender_core_evenPart
  · exact hconj.isBestOffender _ (isBestOffender_core_hyperplane hH)

/-- B.3.2(6), sufficiency for the canonical families on the natural module.
The additional regular `E₈` family is treated in `Eight.Regular`. -/
theorem isBestOffender_natural_of_caseBFamily {A : Subgroup Perm}
    (hA : CaseBFamily 8 (by decide) A) : IsBestOffender (naturalRepresentation (Fin 8)) A := by
  rcases hA with hA | hA | hA | ⟨H, hH, _, hconj⟩
  · exact isBestOffender_natural_of_caseAFamily hA
  · exact hA.isBestOffender _ isBestOffender_exceptional_natural
  · exact hA.isBestOffender _ isBestOffender_natural_evenPart
  · exact hconj.isBestOffender _ (isBestOffender_natural_hyperplane hH)

/-- Apart from the conjugates of `D`, the canonical case-(b) groups have
fixed codimension equal to their rank on both sections. -/
theorem caseBFamily_rank_codim_of_not_conjugate_D {A : Subgroup Perm}
    (hA : CaseBFamily 8 (by decide) A) (hD : ¬ IsConjugateTo A (D 8)) :
    fixedCodim (coreRepresentation (Fin 8)) A = rank A ∧
    fixedCodim (naturalRepresentation (Fin 8)) A = rank A := by
  rcases hA with ⟨m, hm0, hm, hconj⟩ | hconj | hconj | ⟨H, hH, _, hconj⟩
  · have hm4 : m ≠ 4 := by
      intro he
      subst m
      exact hD hconj
    have hc := (fixedCodim_disjointTranspositions hm0 hm).2.2
    have hr := rank_disjointTranspositions (⟨m, by omega⟩ : Fin 5)
    simpa only [hconj.fixedCodim_eq, hconj.rank_eq, hr, if_neg hm4] using hc
  · simpa only [hconj.fixedCodim_eq, hconj.rank_eq, rank_exceptional] using
      fixedCodim_exceptional.2.2
  · simpa only [hconj.fixedCodim_eq, hconj.rank_eq, rank_evenPart] using
      fixedCodim_evenPart.2.2
  · simpa only [hconj.fixedCodim_eq, hconj.rank_eq, rank_hyperplane hH] using
      fixedCodim_hyperplane hH

/-- Within the canonical families, exactly the conjugates of `D` are strong
on the core. No classification of arbitrary subgroups is assumed. -/
theorem isStrongOffender_core_iff_of_caseBFamily {A : Subgroup Perm}
    (hA : CaseBFamily 8 (by decide) A) :
    IsStrongOffender (coreRepresentation (Fin 8)) A ↔ IsConjugateTo A (D 8) := by
  constructor
  · intro hs
    by_contra hn
    have he := (caseBFamily_rank_codim_of_not_conjugate_D hA hn).1
    exact (ne_of_lt hs.2) he
  · intro hconj
    exact hconj.isStrongOffender _ isStrongOffender_core_D

/-- Within the canonical families, exactly the conjugates of `D` are strong
on the natural module. -/
theorem isStrongOffender_natural_iff_of_caseBFamily {A : Subgroup Perm}
    (hA : CaseBFamily 8 (by decide) A) :
    IsStrongOffender (naturalRepresentation (Fin 8)) A ↔ IsConjugateTo A (D 8) := by
  constructor
  · intro hs
    by_contra hn
    have he := (caseBFamily_rank_codim_of_not_conjugate_D hA hn).2
    exact (ne_of_lt hs.2) he
  · intro hconj
    exact hconj.isStrongOffender _ isStrongOffender_natural_D

end CFSG.Quasithin.ChapterB.Offenders.Eight
