module
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Generated
public import CFSG.Quasithin.ChapterB.Section03.Offenders.SourceSylow

/-!
# Simultaneous Sylow and generation assembly for B.3.2

Choose the explicit Sylow containing `D` and the exceptional group. The
case-(a), case-(b), and degree-eight natural generation theorems then apply to
this same subgroup. In odd degree the word-table construction supplies the
simultaneous containment; in degrees six and eight we use the canonical Sylows
already used for the exhaustive lists and strong-offender uniqueness.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Proposition B.3.2(4)–(6), printed pp. 83–84.
-/

public section
namespace CFSG.Quasithin.ChapterB.Offenders
open BinaryPermutation Representation.BinaryOffender

/-- A single Sylow choice realizes all the generated-offender formulas in B.3.2. -/
theorem exists_sylow_generatedOffenders {n : ℕ}
    (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8) :
    ∃ T : Sylow 2 (Equiv.Perm (Fin n)),
      D n ≤ T ∧ exceptional n (by omega) ≤ T ∧
      generatedBy {A | IsBestOffender (representation (Fin n)) A} T = D n ∧
      generatedBy {A | IsBestOffender (deletedRepresentation (Fin n)) A} T = D n ∧
      generatedBy {A | IsBestOffender (coreRepresentation (Fin n)) A} T =
        (if Even n then D n ⊔ Subgroup.closure
          {s | IsConj (kleinFirst n (by omega)) s ∧ s ∈ T} else D n) ∧
      generatedBy {A | IsBestOffender (naturalRepresentation (Fin n)) A} T =
        (if n = 8 then (T : Subgroup (Equiv.Perm (Fin n))) else
          if Even n then D n ⊔ Subgroup.closure
            {s | IsConj (kleinFirst n (by omega)) s ∧ s ∈ T} else D n) := by
  by_cases ho : n = 5 ∨ n = 7
  · obtain ⟨T, hT⟩ := Odd.exists_sylow_containing_D_exceptional ho
    have hD : D n ≤ T := by rw [hT]; exact le_sup_left
    have hE : exceptional n (by omega) ≤ T := by rw [hT]; exact le_sup_right
    have he : ¬ Even n := by rcases ho with rfl | rfl <;> decide
    have h8 : n ≠ 8 := by omega
    refine ⟨T, hD, hE, Odd.generatedBy_full ho T hD, Odd.generatedBy_deleted ho T hD, ?_⟩
    simp only [he, h8, ite_false]
    exact ⟨Odd.generatedBy_core ho T hD, Odd.generatedBy_natural ho T hD⟩
  · have hn : n = 6 ∨ n = 8 := by omega
    rcases hn with rfl | rfl
    · refine ⟨Six.sylow, Six.D_le_sylowCarrier, Six.exceptional_le_sylowCarrier,
        Six.generatedBy_full, Six.generatedBy_deleted, ?_⟩
      simp only [show Even 6 from by decide, show ¬ (6 = 8) from by decide,
        ite_true, ite_false]
      exact ⟨Six.generatedBy_core_source, Six.generatedBy_natural_source⟩
    · refine ⟨Eight.canonicalSylow, Eight.D_le_canonicalSylow, Eight.exceptional_le_canonicalSylow,
        Eight.generatedBy_full, Eight.generatedBy_deleted, ?_⟩
      simpa only [show Even 8 from by decide, ite_true] using
        And.intro Eight.generatedBy_core Eight.generatedBy_natural

end CFSG.Quasithin.ChapterB.Offenders
