module

public import CFSG.Quasithin.ChapterB.Section03.Offenders.Defs
public import CFSG.Quasithin.ChapterB.Section03.Offenders.FixedTests
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Canonical
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Exhaustion
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Regular
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Sylow.RegularModel
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Sylow.CaseB

/-!+# Complete degree-eight offender classification

The structural orbit and displacement arguments exhaust arbitrary offenders;
the canonical fixed-space calculations and the affine-function calculation for
regular elementary eight groups prove bestness for every listed group. Combining
them gives the four exhaustive equivalences, with every hyperplane of `D`
included. All rank and fixed-codimension calculations are re-exported from the
canonical and regular developments.

The only strong offenders on the core or natural module are conjugates of `D`.
The regular family has rank and natural fixed codimension both equal to three,
so contributes no additional strong offenders.

The explicit Sylow subgroup contains all standard representatives and has `D`
as its unique strong best offender. The regular cube translations complete its
generation by natural-module best offenders. For the core, the swap and double
transposition bounds give both inputs to the parent's generated-offender formula.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
1 March 2004 manuscript, Proposition B.3.2 in degree eight, printed pp. 83–84.
-/

public section

namespace CFSG.Quasithin.ChapterB.Offenders.Eight

open BinaryPermutation Representation.BinaryOffender

/-- B.3.2(4): the full degree-eight permutation module. -/
theorem isBestOffender_full_iff (A : Subgroup Perm) :
    IsBestOffender (representation (Fin 8)) A ↔ CaseAFamily 8 A :=
  ⟨EightExhaustion.caseAFamily_of_isBestOffender_full,
    isBestOffender_full_of_caseAFamily⟩

/-- B.3.2(4): quotienting the full module by its constant line gives the same list. -/
theorem isBestOffender_deleted_iff (A : Subgroup Perm) :
    IsBestOffender (deletedRepresentation (Fin 8)) A ↔ CaseAFamily 8 A :=
  ⟨EightExhaustion.caseAFamily_of_isBestOffender_deleted,
    isBestOffender_deleted_of_caseAFamily⟩

/-- B.3.2(5): the even-weight core, including every hyperplane type. -/
theorem isBestOffender_core_iff (A : Subgroup Perm) :
    IsBestOffender (coreRepresentation (Fin 8)) A ↔ CaseBFamily 8 (by decide) A :=
  ⟨EightExhaustion.caseBFamily_of_isBestOffender_core,
    isBestOffender_core_of_caseBFamily⟩

/-- B.3.2(6): exactly the canonical families and the regular elementary eight
groups are best offenders on the natural module. -/
theorem isBestOffender_natural_iff (A : Subgroup Perm) :
    IsBestOffender (naturalRepresentation (Fin 8)) A ↔
      CaseBFamily 8 (by decide) A ∨ IsRegularEight A := by
  constructor
  · exact EightExhaustion.caseBFamily_or_isRegularEight_of_isBestOffender_natural
  · rintro (hA | hA)
    · exact isBestOffender_natural_of_caseBFamily hA
    · exact isBestOffender_natural_regularEight hA

/-- The explicit regular group used in Sylow generation is a best offender. -/
theorem isBestOffender_natural_standardRegular :
    IsBestOffender (naturalRepresentation (Fin 8)) standardRegular :=
  isBestOffender_natural_regularEight isRegularEight_standardRegular

/-- On the core, the strong offenders are exactly the conjugates of `D`. -/
theorem isStrongOffender_core_iff (A : Subgroup Perm) :
    IsStrongOffender (coreRepresentation (Fin 8)) A ↔ IsConjugateTo A (D 8) := by
  constructor
  · intro hA
    exact (isStrongOffender_core_iff_of_caseBFamily
      (EightExhaustion.caseBFamily_of_isOffender_core ⟨hA.1, hA.2.le⟩)).mp hA
  · intro hA
    exact hA.isStrongOffender _ isStrongOffender_core_D

/-- On the natural module, the additional regular family is never strong. -/
theorem isStrongOffender_natural_iff (A : Subgroup Perm) :
    IsStrongOffender (naturalRepresentation (Fin 8)) A ↔ IsConjugateTo A (D 8) := by
  constructor
  · intro hA
    rcases EightExhaustion.caseBFamily_or_isRegularEight_of_isOffender_natural
      ⟨hA.1, hA.2.le⟩ with hc | hr
    · exact (isStrongOffender_natural_iff_of_caseBFamily hc).mp hA
    · have hlt := hA.2
      rw [fixedCodim_natural_regularEight hr, rank_eq_three_of_isRegularEight hr] at hlt
      exact False.elim (Nat.lt_irrefl _ hlt)
  · intro hA
    exact hA.isStrongOffender _ isStrongOffender_natural_D

/-- The case-(a) containment needed to compute the generated-offender subgroup. -/
theorem bestOffender_full_le_D {P A : Subgroup Perm} (hP : IsPGroup 2 P)
    (hD : D 8 ≤ P) (hAP : A ≤ P) (hA : IsBestOffender (representation (Fin 8)) A) :
    A ≤ D 8 :=
  caseAFamily_le_D_of_isPGroup hP hD ((isBestOffender_full_iff A).mp hA) hAP

theorem bestOffender_deleted_le_D {P A : Subgroup Perm} (hP : IsPGroup 2 P)
    (hD : D 8 ≤ P) (hAP : A ≤ P)
    (hA : IsBestOffender (deletedRepresentation (Fin 8)) A) : A ≤ D 8 :=
  caseAFamily_le_D_of_isPGroup hP hD ((isBestOffender_deleted_iff A).mp hA) hAP

/-- The upper containment for the core's generated-offender calculation. -/
theorem bestOffender_core_le_D_sup_doubleSwaps {P A : Subgroup Perm} (hP : IsPGroup 2 P)
    (hD : D 8 ≤ P) (hAP : A ≤ P) (hA : IsBestOffender (coreRepresentation (Fin 8)) A) :
    A ≤ D 8 ⊔ Subgroup.closure {s | IsConj (kleinFirst 8 (by decide)) s ∧ s ∈ P} :=
  caseBFamily_le_D_sup_doubleSwaps hP hD ((isBestOffender_core_iff A).mp hA) hAP

/-- The double transpositions in the canonical Sylow all lie in core and
natural best offenders contained in that Sylow. -/
theorem doubleSwap_mem_bestOffender {s : Perm} (hs : s ∈ canonicalSylow)
    (hd : IsConj (kleinFirst 8 (by decide)) s) :
    ∃ A : Subgroup Perm, s ∈ A ∧ A ≤ canonicalSylow ∧
      IsBestOffender (coreRepresentation (Fin 8)) A ∧
      IsBestOffender (naturalRepresentation (Fin 8)) A := by
  rcases doubleSwap_mem_D_or_exceptional hs hd with hD | hE | hE
  · exact ⟨D 8, hD, D_le_canonicalSylow,
      isBestOffender_core_of_caseAFamily
        (caseAFamily_disjointTranspositions (by decide) (by decide)),
      isBestOffender_natural_of_caseAFamily
        (caseAFamily_disjointTranspositions (by decide) (by decide))⟩
  · exact ⟨exceptional 8 (by decide), hE, exceptional_le_canonicalSylow,
      isBestOffender_exceptional_core, isBestOffender_exceptional_natural⟩
  · have hc : IsConjugateTo oppositeExceptional (exceptional 8 (by decide)) :=
      ⟨halfSwap, rfl⟩
    exact ⟨oppositeExceptional, hE, oppositeExceptional_le_canonicalSylow,
      hc.isBestOffender _ isBestOffender_exceptional_core,
      hc.isBestOffender _ isBestOffender_exceptional_natural⟩

/-- Uniqueness already holds in any two-subgroup containing the standard `D`. -/
theorem isStrongOffender_natural_iff_eq_D {P A : Subgroup Perm} (hP : IsPGroup 2 P)
    (hD : D 8 ≤ P) (hAP : A ≤ P) :
    IsStrongOffender (naturalRepresentation (Fin 8)) A ↔ A = D 8 := by
  constructor
  · intro hA
    exact conjugate_D_eq_of_le_isPGroup hP hD
      ((isStrongOffender_natural_iff A).mp hA) hAP
  · rintro rfl
    exact isStrongOffender_natural_D

/-- B.3.2(6): `D` is the unique strong best offender in the concrete Sylow. -/
theorem strongBestOffender_canonicalSylow_iff (A : Subgroup Perm) :
    (A ≤ canonicalSylow ∧ IsBestOffender (naturalRepresentation (Fin 8)) A ∧
      IsStrongOffender (naturalRepresentation (Fin 8)) A) ↔ A = D 8 := by
  constructor
  · rintro ⟨hAT, _, hA⟩
    exact (isStrongOffender_natural_iff_eq_D canonicalSylow.isPGroup'
      D_le_canonicalSylow hAT).mp hA
  · rintro rfl
    exact ⟨D_le_canonicalSylow,
      isBestOffender_natural_of_caseAFamily
        (caseAFamily_disjointTranspositions (by decide) (by decide)),
      isStrongOffender_natural_D⟩

end CFSG.Quasithin.ChapterB.Offenders.Eight
