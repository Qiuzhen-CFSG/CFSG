module

public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.ConjugateIntersections.Orbits.Generation
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.ConjugateIntersections.Orbits.Stabilizer

/-!
# The orbit-generation branch of J.2.2(5)

If one distinct L-conjugate of U were contained in Q, the H ∩ L orbit
and relative H-normality of Q would put every conjugate in Q. Their
span is S, so |S| = |Q| would force S = Q, contradicting J.2.2(1).
This supplies the remaining containment premise of
`ConjugateIntersections.conclusions_of_not_le_Q`.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
J.2.2(5), printed pp.432–433 (PDF pp.443–444).
-/

public section
namespace CFSG.Quasithin.ChapterJ.ConjugateIntersections
open Subgroup Representation
variable {G : Type*} [Group G] [Finite G]

/-- The orbit-generation branch of J.2.2(5). -/
theorem conjugateU_not_le_Q (d : LocalSetup G) (l : G) (hl : l ∈ d.L)
    (hne : conjugateU d l ≠ d.toTypeRuSetup.U) :
    ¬ conjugateU d l ≤ d.toTypeRuSetup.Q := by
  intro hQ
  have hAll (k : d.L) : conjugateU d k ≤ d.toTypeRuSetup.Q := by
    by_cases hkH : (k : G) ∈ d.toTypeRuSetup.H
    · rw [conjugateU_eq_of_mem_H d k hkH]
      exact d.ru2.six.kernel_le
    · obtain ⟨h, _, hhH, he⟩ := exists_conjugateU_transport d l k hl k.property
        (not_mem_H_of_conjugateU_ne d l hne) hkH
      rw [he]
      exact (map_mono hQ).trans_eq
        (mem_normalizer_iff_map_conj_eq.mp (d.ru2.six.normalized hhH))
  have hSQ : d.toTypeRuSetup.S ≤ d.toTypeRuSetup.Q := by
    rw [← conjugateSpan_eq_S d]
    exact iSup_le hAll
  apply d.Q_ne_S
  apply Eq.symm
  apply Subgroup.eq_of_le_of_card_ge hSQ
  rw [d.ru1.card_S, d.ru2.card_Q d.card_Z]

end CFSG.Quasithin.ChapterJ.ConjugateIntersections
