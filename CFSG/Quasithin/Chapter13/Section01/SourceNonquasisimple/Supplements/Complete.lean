module

public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction.Complete

/-!
# Supplement uniqueness and Thompson movement in original 13.1.9

For every actual radical supplement B of L, the completed FF contradiction
excludes a maximal two-local over BT different from N_G(L). The original
normalizer calculation supplies N_G(L) itself, so the overgroup family is
exactly its singleton. Apply this uniqueness to the constructed canonical
supplement: the proved qrc argument excludes J₀(T) ≤ C_T(L/O∞(L)), giving
L = [L,J₀(T)]. Here J₀ is the source's elementary Thompson subgroup.

All canonical geometry, escaping witnesses and FF premises are discharged.
Only CanonicalStars and the exact earlier 13.1.2 rigidity and classification
clauses remain explicit, with final discharge owned by qt-d-1317-source.
The last theorem applies both conclusions to the same maximal counterexample
selected from the original Hypothesis 13.3.1.

Source: Aschbacher--Smith, 13.1.9, printed pp.869--871, and 13.3.2, p.884.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements
open Chapter1 Chapter1.Section02 Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

/-- Original 13.1.9(1), including existence of the asserted unique overgroup,
for every local component supplementing the embedded solvable radical. -/
theorem radical_supplement_unique
    (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hs : Escape.CanonicalStars T) (hrig : Escape.QuasisimpleRigidity T)
    (hclass : Escape.QuasisimpleClassification T) {L B : Subgroup G}
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L))
    (hB : B ∈ radicalSupplements T L) :
    IsMaximalTwoLocal (normalizer (L : Set G)) ∧
      B ⊔ (T : Subgroup G) ≤ normalizer (L : Set G) ∧
      ∀ H : Subgroup G, IsMaximalTwoLocal H → B ⊔ (T : Subgroup G) ≤ H →
        H = normalizer (L : Set G) := by
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  have hBL : B ≤ L := hB.2 ▸ le_sup_right
  refine ⟨(Escape.nonquasisimple_centralizer_unique_of_stars h hmany hs hL hn).1,
    sup_le (hBL.trans L.le_normalizer) hTL,?_⟩
  intro H hH hBH
  by_contra hne
  exact FFContradiction.supplement_candidate_false h hmany hs hrig hclass
    hL hn hB hH hBH hne

/-- The literal singleton formulation M(L₁T) = {N_G(L)} of 13.1.9(1). -/
theorem radical_supplement_overgroups_eq
    (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hs : Escape.CanonicalStars T) (hrig : Escape.QuasisimpleRigidity T)
    (hclass : Escape.QuasisimpleClassification T) {L B : Subgroup G}
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L))
    (hB : B ∈ radicalSupplements T L) :
    maximalTwoLocalOvergroups (B ⊔ (T : Subgroup G)) = {normalizer (L : Set G)} := by
  obtain ⟨hM,hBM,hu⟩ := radical_supplement_unique h hmany hs hrig hclass hL hn hB
  ext H
  constructor
  · intro hH
    exact Set.mem_singleton_iff.mpr (hu H hH.1 hH.2)
  · intro hH
    rcases Set.mem_singleton_iff.mp hH with rfl
    exact ⟨hM,hBM⟩

/-- Original 13.1.9(2), using the constructed canonical supplement and its
qrc configuration. Supplement uniqueness is proved, not a premise. -/
theorem thompson_movement_source
    (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hs : Escape.CanonicalStars T) (hrig : Escape.QuasisimpleRigidity T)
    (hclass : Escape.QuasisimpleClassification T) {L : Subgroup G}
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L)) :
    L = ⁅L,ChapterB.thompsonJ (T : Subgroup G) 0⁆ :=
  thompson_movement_of_supplement_uniqueness h hmany hs hL hn
    (fun _ hB => (radical_supplement_unique h hmany hs hrig hclass hL hn hB).2.2)

/-- Both clauses of original 13.1.9 with only the named earlier-source
inputs retained for final assembly by qt-d-1317-source. -/
theorem source_lemma_13_1_9
    (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hs : Escape.CanonicalStars T) (hrig : Escape.QuasisimpleRigidity T)
    (hclass : Escape.QuasisimpleClassification T) {L : Subgroup G}
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L)) :
    (∀ B ∈ radicalSupplements T L,
      maximalTwoLocalOvergroups (B ⊔ (T : Subgroup G)) = {normalizer (L : Set G)}) ∧
      L = ⁅L,ChapterB.thompsonJ (T : Subgroup G) 0⁆ :=
  ⟨fun _ hB => radical_supplement_overgroups_eq h hmany hs hrig hclass hL hn hB,
    thompson_movement_source h hmany hs hrig hclass hL hn⟩

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements

namespace CFSG.Quasithin.Chapter14.Section03.FaithfulSource
open Chapter1 Chapter12.Section02 Chapter13.Section01
open Chapter13.Section01.SourceNonquasisimple.Supplements
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L₀ : Subgroup G}

/-- The actual 13.3.2 maximal counterexample satisfies both source 13.1.9
conclusions on the same L. Only the three earlier-source inputs remain. -/
theorem Hypothesis1331.nonquasisimple_supplements_of_many (h : Hypothesis1331 T L₀)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ IsQuasisimple (XiQuotient L₀))
    (hs : Escape.CanonicalStars T) (hrig : Escape.QuasisimpleRigidity T)
    (hclass : Escape.QuasisimpleClassification T) :
    ∃ L : Subgroup G, L₀ ≤ L ∧ FaithfulMaximalLocal T L ∧
      ¬ IsQuasisimple (XiQuotient L) ∧
      IsMaximalTwoLocal (normalizer (L : Set G)) ∧
      (L ⊔ (T : Subgroup G) ≤ normalizer (L : Set G)) ∧
      (∀ B ∈ radicalSupplements T L,
        maximalTwoLocalOvergroups (B ⊔ (T : Subgroup G)) = {normalizer (L : Set G)}) ∧
      L = ⁅L,ChapterB.thompsonJ (T : Subgroup G) 0⁆ := by
  obtain ⟨L,_,hL₀,hL,hLn,hM,hLT,_⟩ := h.maximal_counterexample_of_many hmany hn
  exact ⟨L,hL₀,hL,hLn.2,hM,sup_le L.le_normalizer (le_sup_right.trans hLT),
    source_lemma_13_1_9 h.hypothesis1311 hmany hs hrig hclass hL hLn.2⟩

end CFSG.Quasithin.Chapter14.Section03.FaithfulSource
