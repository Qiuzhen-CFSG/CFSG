module
public import Theory.SpecificGroups.Held.TransvectionCentralizer.Marking
public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.Coverage.FiniteFusion
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration.ExtensionChecks.NodeMembers

/-! A retained conjugacy certificate sends the actual central involution
into a distinct element of its normal row-nine subgroup, hence into its
literal centralizer two-core. -/

namespace Held.TransvectionCentralizer
open Subgroup LocalPairs.SylowGeometry.Calculations
open TwoLocalCandidates.MaximalNormalizerCatalogue
open IntrinsicEnumeration ExtensionChecks
open InvolutionFixedData.Coverage

private theorem witness_mem : (normalForm 96).val ∈ ambient 9 := by
  exact mem_map.mpr ⟨normalForm 96,
    (certified_members (some 9) _).mpr ⟨96, by decide +kernel, rfl⟩, rfl⟩

private theorem witness_ne : (normalForm 96).val ≠ centralWord := by
  have hh : normalFormAction 96 (0 : Fin 2058) ≠ wordAction commonWord 0 := by
    decide +kernel
  intro he
  apply hh
  rw [normalFormAction_eq, wordAction_eq]
  exact congrArg (fun x : He => representation x 0) he

/-- The original native point has an explicitly certified distinct
conjugate in the two-core of its entire centralizer. -/
public theorem point_core_fusion : Theory.GroupTheory.TransvectionFive.PointCoreFusion centralWord := by
  have hfirst : IsConj (TwoLocalCandidates.max5First ^ 4) centralWord :=
    isConj_iff.mpr ⟨conjugator 0, conjugator_zero_max5First_four⟩
  have hsecond : IsConj (TwoLocalCandidates.max5First ^ 4) (normalForm 96).val := by
    have hh := root_conjugation_identity 11
    have hr : rootRepresentative 11 = TwoLocalCandidates.max5First ^ 4 := by
      simp [rootRepresentative, rootClass]
    have hi : rootIndex 11 = 96 := by decide +kernel
    rw [hr, hi] at hh
    exact isConj_iff.mpr ⟨rootConjugator 11, hh⟩
  obtain ⟨g, he⟩ := isConj_iff.mp (hfirst.symm.trans hsecond)
  refine ⟨g, ?_, by rw [he]; exact witness_ne⟩
  rw [he]
  have hA := row_nine_elementary
  let := hA
  have hAC : ambient 9 ≤ centralizer ({centralWord} : Set He) := by
    rw [← row_nine_normalizer]
    exact le_normalizer
  exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 (ambient 9))
    hAC row_nine_normalizer.symm.le witness_mem

end Held.TransvectionCentralizer
