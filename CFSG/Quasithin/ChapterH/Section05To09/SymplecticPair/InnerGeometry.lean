module

public import CFSG.Quasithin.ChapterH.Section05To09.SymplecticPair.InnerGeometry.LocalCalculations
public import CFSG.Quasithin.ChapterH.Section05To09.SymplecticPair.InnerGeometry.NaturalFamily
public import CFSG.Quasithin.ChapterH.Section05To09.AlternatingPair.Parameters

/-!
# Native geometry and module parameters for H.7

For the literal graph-paired symplectic action, the root witnesses and the
geometric involution classification give m = 3n. Elementary subgroup placement
excludes every F−1 offender; the pointwise-centralizer definition then gives
α = ∞. The two natural planes force a member of the E.3.8 family at 2n into
the Sylow center, where a root intersection contradicts membership. Thus
a < 2n. The exact natural-family criterion and its attaining radical give
a = 2n for the single natural module.

The exported full-group parameters use actual subgroup ranks, fixed spaces,
relative indices and pointwise centralizers. The genuine derived action has
the same lower involution bound and both exclusions by restriction. These
are the native inputs for the source acting-overgroup assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.7,
printed pp.388–389. The actual commutator carrier is retained by the exported
restriction lemma; binary full-group witnesses are not assumed to lie in it.
-/

public section

namespace CFSG.Quasithin.ChapterH.Section05To09.SymplecticPair
open Representation.BinaryOffender
open Representation.OneCohomology.SymplecticFour
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph
open SymplecticConjugatePair
variable {F : Type*} [Field F] [CharP F 2] [Finite F] [Algebra (ZMod 2) F]

/-- Root involutions attain the native minimum, and every involution meets it. -/
theorem moduleM_graphPair_eq {n : ℕ} (hF : Nat.card F = 2^n) :
    ChapterE.moduleM (graphPair (F := F)) = 3*n := by
  have hr := root_involution 0 (one_ne_zero : (1 : F) ≠ 0)
  apply le_antisymm
  · exact (ChapterE.moduleM_le_involution (graphPair (F := F))
      (t := rootElement 0 (1 : F)) hr).trans_eq
      (root_fixedCodim_of_card hF 0 one_ne_zero)
  · obtain ⟨g, hg, hmin⟩ := ChapterE.moduleM_attained (graphPair (F := F)) ⟨_, hr⟩
    rw [← hmin]
    exact Involutions.involution_fixedCodim_lower hF g hg

/-- The actual commutator action inherits the lower bound, including at n = 1. -/
theorem le_moduleM_derivedPair {n : ℕ} (hF : Nat.card F = 2^n) :
    3*n ≤ ChapterE.moduleM (derivedPair (graphAut (F := F))) := by
  apply le_csInf ⟨_, Set.mem_insert _ _⟩
  rintro d (rfl | ⟨g, hg, rfl⟩)
  · rw [finrank_space hF]
    omega
  · exact Involutions.derived_involution_fixedCodim_lower hF g hg

/-- No elementary actor in the full matrix group satisfies the F−1 inequality. -/
theorem graphPair_no_offender {n : ℕ} (hF : Nat.card F = 2^n) (hn : 0 < n)
    (A : Subgroup (Sp F)) : ¬ AlternatingPair.IsFMinusOneOffender (graphPair (F := F)) A := by
  rintro ⟨hA, hcod⟩
  exact (not_le_of_gt (elementary_subgroup_not_offender hF hn hA)) hcod

/-- Offender exclusion on the genuine derived carrier. -/
theorem derivedPair_no_offender {n : ℕ} (hF : Nat.card F = 2^n) (hn : 0 < n)
    (A : Subgroup (commutator (Sp F))) :
    ¬ AlternatingPair.IsFMinusOneOffender (derivedPair (graphAut (F := F))) A := by
  rintro ⟨hA, hcod⟩
  exact (not_le_of_gt (derived_elementary_subgroup_not_offender hF hn hA)) hcod

/-- The source pointwise-centralizer parameter is infinite for the native pair. -/
theorem moduleAlpha_graphPair_eq_top {n : ℕ} (hF : Nat.card F = 2^n)
    (hn : 0 < n) : AlternatingPair.moduleAlpha (graphPair (F := F)) = ⊤ :=
  AlternatingPair.moduleAlpha_eq_top_of_no_offender (graphPair (F := F))
    (graphPair_no_offender hF hn)

/-- The pointwise-centralizer parameter is infinite on the derived action too. -/
theorem moduleAlpha_derivedPair_eq_top {n : ℕ} (hF : Nat.card F = 2^n)
    (hn : 0 < n) : AlternatingPair.moduleAlpha (derivedPair (graphAut (F := F))) = ⊤ :=
  AlternatingPair.moduleAlpha_eq_top_of_no_offender (derivedPair (graphAut (F := F)))
    (derivedPair_no_offender hF hn)

/-- The native full-group rank and the three module parameters supplied by
the elementary geometry in H.7. -/
theorem native_parameters {n : ℕ} (hF : Nat.card F = 2^n) (hn : 0 < n) :
    primeRank 2 (Sp F) = 3*n ∧
      ChapterE.moduleM (graphPair (F := F)) = 3*n ∧
      ChapterE.moduleA (graphPair (F := F)) < (2*n : ℕ) ∧
      AlternatingPair.moduleAlpha (graphPair (F := F)) = ⊤ :=
  ⟨EvenTwoRank.rank hF hn, moduleM_graphPair_eq hF,
    pair_moduleA_lt hF hn, moduleAlpha_graphPair_eq_top hF hn⟩

end CFSG.Quasithin.ChapterH.Section05To09.SymplecticPair
