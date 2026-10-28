module

public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.CanonicalGeometry.Qrc.Thompson
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.CanonicalGeometry.Escape

/-!
# Canonical qrc and escaping witnesses at the original maximal counterexample

The actual maximal counterexample selected from Hypothesis 13.3.1 carries
all canonical qrc hypotheses, a nonzero reduced module and the literal
two-residual. The proved implication converts supplement uniqueness to
Thompson movement. Every contrary maximal overgroup of an actual radical
supplement also gives the refined escaping witness, with all canonical
geometry discharged by the original constructions.

The separate FF owner must exclude that witness to prove uniqueness;
qt-d-1317-supplements retains this assembly. Canonical starred membership
and the exact earlier 13.1.2 clauses remain with qt-d-1317-source for final
discharge. No uniqueness or movement is asserted without its premise.
Source: Aschbacher--Smith 13.1.9, pp.869--871, and 13.3.2, p.884.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.FaithfulSource
open Chapter1 Chapter12.Section02 Chapter13.Section01
open Chapter13.Section01.SourceNonquasisimple.Supplements
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L₀ : Subgroup G}

/-- The literal maximal counterexample has the complete canonical qrc
configuration, including its nonzero module and actual two-residual. -/
theorem Hypothesis1331.canonical_qrc_of_many (h : Hypothesis1331 T L₀)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ IsQuasisimple (XiQuotient L₀)) (hs : Escape.CanonicalStars T) :
    ∃ L : Subgroup G, L₀ ≤ L ∧ FaithfulMaximalLocal T L ∧
      ¬ IsQuasisimple (XiQuotient L) ∧
      let W : Subgroup G := canonicalSupplement T L ⊔ (T : Subgroup G)
      let V : Subgroup G := canonicalReducedModule T L
      IsMaximalTwoLocal (normalizer (L : Set G)) ∧ V ≠ ⊥ ∧
      (pResidual 2 W).map W.subtype = canonicalSupplement T L ∧
      ∀ H : Subgroup G, H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) →
        Chapter3.QrcHypotheses T (normalizer (L : Set G)) W H V := by
  obtain ⟨L,_,hL₀,hL,hLn,hM,_⟩ := h.maximal_counterexample_of_many hmany hn
  exact ⟨L,hL₀,hL,hLn.2,hM,canonicalReducedModule_ne_bot h.hypothesis1311 hmany hL hLn.2,
    canonical_embedded_twoResidual h.hypothesis1311 hmany hL hLn.2,
    fun H hH => canonical_qrc_hypotheses h.hypothesis1311 hmany hs hL hLn.2 hH⟩

/-- Supplement uniqueness at the actual maximal counterexample implies the
literal source Thompson commutator conclusion. -/
theorem Hypothesis1331.canonical_thompson_implication_of_many (h : Hypothesis1331 T L₀)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ IsQuasisimple (XiQuotient L₀)) (hs : Escape.CanonicalStars T) :
    ∃ L : Subgroup G, L₀ ≤ L ∧ FaithfulMaximalLocal T L ∧
      ¬ IsQuasisimple (XiQuotient L) ∧
      ((∀ B ∈ radicalSupplements T L, ∀ N : Subgroup G, IsMaximalTwoLocal N →
        B ⊔ (T : Subgroup G) ≤ N → N = normalizer (L : Set G)) →
        L = ⁅L,ChapterB.thompsonJ (T : Subgroup G) 0⁆) := by
  obtain ⟨L,_,hL₀,hL,hLn,_,_⟩ := h.maximal_counterexample_of_many hmany hn
  exact ⟨L,hL₀,hL,hLn.2,
    thompson_movement_of_supplement_uniqueness h.hypothesis1311 hmany hs hL hLn.2⟩

/-- Every contrary supplement overgroup at the actual maximal counterexample
supplies the refined source witness, with all canonical geometry proved. -/
theorem Hypothesis1331.canonical_escape_of_many (h : Hypothesis1331 T L₀)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ IsQuasisimple (XiQuotient L₀))
    (hs : Escape.CanonicalStars T) (hrig : Escape.QuasisimpleRigidity T)
    (hclass : Escape.QuasisimpleClassification T) :
    ∃ L : Subgroup G, L₀ ≤ L ∧ FaithfulMaximalLocal T L ∧
      ¬ IsQuasisimple (XiQuotient L) ∧
      ∀ B : Subgroup G, B ∈ radicalSupplements T L →
        ∀ H : Subgroup G, IsMaximalTwoLocal H → B ⊔ (T : Subgroup G) ≤ H →
          H ≠ normalizer (L : Set G) →
          ∃ C Y : Subgroup G, C ∈ cComponentsIn H ∧
            canonicalSupplement T L ≤ C ∧ (C.subgroupOf H).Normal ∧
            Escape.RefinedWitness T L H C Y := by
  obtain ⟨L,_,hL₀,hL,hLn,_,_⟩ := h.maximal_counterexample_of_many hmany hn
  exact ⟨L,hL₀,hL,hLn.2,fun B hB H hH hBH hne =>
    canonical_escape_for_supplement h.hypothesis1311 hmany hs hrig hclass hL hLn.2 hB hH hBH hne⟩

end CFSG.Quasithin.Chapter14.Section03.FaithfulSource
