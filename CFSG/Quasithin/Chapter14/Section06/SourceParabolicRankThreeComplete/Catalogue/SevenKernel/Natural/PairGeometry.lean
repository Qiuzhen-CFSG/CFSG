module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Catalogue.SevenKernel.Natural.Inputs
public import Theory.SpecificGroups.SymmetricSeven.FewPairsCubic

/-!
# Relative seven-letter pair geometry

The three-pair fixed-space theorem first bounds a pointwise fixer by the
elementary eight. For one or two pairs, one additional fixed core vector
removes the unused swaps. The equivariant core-to-natural identification
preserves the literal quotient-module convention. The existing one-, two-
and three-pair cubic generation theorems use the same cycle (016).

This supplies the geometric premise of `Natural.selection_of_coordinates`.
Source: Aschbacher--Smith C.1.24(a), printed p.131.
-/

public section
open Subgroup Equiv BinaryPermutation Representation.BinaryOffender
open Representation.AlternatingSevenConjugatePair.ElementaryGeometry
namespace CFSG.Quasithin.Chapter14.Section06.ParabolicCatalogue.SevenKernel.Natural
open ChapterB.Offenders
open Theory.SpecificGroups.SymmetricSeven.ThreePairsCubic
open ChapterC.RankOne.Alternating.SevenSource

private theorem disjoint_one : disjointTranspositions 7 1 = pairOne := by
  apply le_antisymm
  · apply (closure_le _).mpr
    rintro g ⟨i, hi, rfl⟩
    have hi0 : i = 0 := Fin.ext (by change i.val = 0; omega)
    subst i
    exact reflection_mem_pairOne
  · exact zpowers_le.mpr (pairSwap_mem 0 (by decide))

private theorem disjoint_two : disjointTranspositions 7 2 = pairTwo := by
  apply le_antisymm
  · apply (closure_le _).mpr
    rintro g ⟨i, hi, rfl⟩
    have hi01 : i = 0 ∨ i = 1 := by
      have : i.val = 0 ∨ i.val = 1 := by omega
      simpa only [Fin.ext_iff, Fin.val_zero, Fin.val_one] using this
    rcases hi01 with rfl | rfl
    · exact reflection_mem_pairTwo
    · exact (show zpowers swap23 ≤ pairTwo from le_sup_right) (mem_zpowers swap23)
  · exact sup_le (zpowers_le.mpr (pairSwap_mem 0 (by decide)))
      (zpowers_le.mpr (pairSwap_mem 1 (by decide)))

private def testOne : core (Fin 7) :=
  ⟨![0,0,1,0,1,0,0], by rw [mem_core]; decide⟩
private def testTwo : core (Fin 7) :=
  ⟨![0,0,0,0,1,0,1], by rw [mem_core]; decide⟩

private theorem testOne_fixed :
    testOne ∈ fixedSpace (coreRepresentation (Fin 7)) (disjointTranspositions 7 1) := by
  apply (mem_fixedSpace_closure_iff _ _ _).mpr
  rintro g ⟨i, hi, rfl⟩
  have hi0 : i = 0 := Fin.ext (by change i.val = 0; omega)
  subst i
  decide +kernel

private theorem testTwo_fixed :
    testTwo ∈ fixedSpace (coreRepresentation (Fin 7)) (disjointTranspositions 7 2) := by
  apply (mem_fixedSpace_closure_iff _ _ _).mpr
  rintro g ⟨i, hi, rfl⟩
  have hi01 : i = 0 ∨ i = 1 := by
    have : i.val = 0 ∨ i.val = 1 := by omega
    simpa only [Fin.ext_iff, Fin.val_zero, Fin.val_one] using this
  rcases hi01 with rfl | rfl <;> decide +kernel

private theorem core_fixer (k : ℕ) (hk1 : 1 ≤ k) (hk3 : k ≤ 3) (g : Sym)
    (hf : ∀ v ∈ fixedSpace (coreRepresentation (Fin 7)) (disjointTranspositions 7 k),
      coreRepresentation (Fin 7) g v = v) : g ∈ disjointTranspositions 7 k := by
  have hg : g ∈ pairElementary := by
    rw [←natural_D_eq_pairElementary]
    apply natural_fixed_space_fixer_le_D g
    intro v hv
    exact hf v (fun a => hv ⟨a, disjointTranspositions_mono hk3 a.property⟩)
  obtain ⟨v, rfl⟩ := hg
  interval_cases k
  · have hh := hf testOne testOne_fixed
    have he : firstWord v = 1 ∨ firstWord v = swap01 :=
      (by decide +kernel : ∀ v : Triple,
        coreRepresentation (Fin 7) (firstWord v) testOne = testOne →
          firstWord v = 1 ∨ firstWord v = swap01) v hh
    rw [disjoint_one]
    rcases he with he | he
    · rw [he]; exact one_mem _
    · rw [he]; exact reflection_mem_pairOne
  · have hh := hf testTwo testTwo_fixed
    have he : firstWord v = 1 ∨ firstWord v = swap01 ∨
        firstWord v = swap23 ∨ firstWord v = swap01 * swap23 :=
      (by decide +kernel : ∀ v : Triple,
        coreRepresentation (Fin 7) (firstWord v) testTwo = testTwo →
          firstWord v = 1 ∨ firstWord v = swap01 ∨
          firstWord v = swap23 ∨ firstWord v = swap01 * swap23) v hh
    rw [disjoint_two]
    have h23 : swap23 ∈ pairTwo := (show zpowers swap23 ≤ pairTwo from le_sup_right) (mem_zpowers swap23)
    rcases he with he | he | he | he
    · rw [he]; exact one_mem _
    · rw [he]; exact reflection_mem_pairTwo
    · rw [he]; exact h23
    · rw [he]; exact mul_mem reflection_mem_pairTwo h23
  · rw [show disjointTranspositions 7 3 = pairElementary from natural_D_eq_pairElementary]
    exact ⟨v, rfl⟩

/-- Fixed-space rigidity and cubic generation for each permitted relative pair group. -/
theorem pair_geometry : PairGeometryInput := by
  intro k hk1 hk3
  refine ⟨?_, ?_⟩
  · intro g hg
    apply core_fixer k hk1 hk3 g
    intro v hv
    let hodd : Odd (Fintype.card (Fin 7)) := by decide
    let e := coreEquivNatural (Fin 7) hodd
    have he (a : Sym) (w : core (Fin 7)) :
        e (coreRepresentation (Fin 7) a w) = naturalRepresentation (Fin 7) a (e w) :=
      coreEquivNatural_equivariant (Fin 7) hodd a w
    apply e.injective
    rw [he]
    apply hg
    intro a
    exact (he a v).symm.trans (congrArg e (hv a))
  · interval_cases k
    · rw [disjoint_one]; exact pairOne_normalizer_cubic_generate
    · rw [disjoint_two]; exact pairTwo_normalizer_cubic_generate
    · rw [show disjointTranspositions 7 3 = pairElementary from natural_D_eq_pairElementary]
      exact normalizer_cubic_generate

end CFSG.Quasithin.Chapter14.Section06.ParabolicCatalogue.SevenKernel.Natural
