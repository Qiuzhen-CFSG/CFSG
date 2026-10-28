module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.Basic
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.RadicalCentralizationComplete

/-!
# Original source applications of the radical-supplement setup

The completed radical centralization identifies the action kernel and
constructs the same PSL₂(p) quotient for every actual radical supplement.
The kernel-intersection and section-centralizer comparisons therefore
apply without any extra action assumption. The literal maximal
counterexample of 13.3.2 supplies these constructions and the Thompson
dichotomy. Original 13.1.4 also proves uniqueness in the faithful
nonquasisimple supplement branch.

This does not establish uniqueness for every supplement or exclude the
centralizing Thompson branch. Those require the canonical normalizer
geometry and the escaping-subgroup argument of 13.1.9.

Source: Aschbacher--Smith 13.1.8--9, printed pp.868--871; 13.3.2, p.884.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements
open Chapter1 Chapter1.Section02 Chapter12.Section02 ChapterA.Section04
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}

/-- Every literal radical supplement has the same prime-field PSL₂ action,
its own radical kernel, and the same nonzero moved subgroup. -/
theorem radical_supplements_action_source
    (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) :
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧
      ∀ B ∈ radicalSupplements (T : Subgroup G) L,
        ClassicalGroup.IsPSL (B ⧸ solvableRadical B) 2 p ∧
        (solvableRadical B).map B.subtype = B ⊓ (solvableRadical L).map L.subtype ∧
        ⁅normalizerReduced L,B⁆ = normalizerMoved L ∧
        normalizerMoved L ≠ ⊥ ∧
        (∀ hBL : B ≤ L,
          ((NormalizerReducedAction.componentMap L).comp (inclusion hBL)).ker =
            solvableRadical B ∧
          ((NormalizerReducedAction.componentMap L).comp (inclusion hBL)).range =
            NormalizerReducedAction.componentImage L) ∧
        ((T : Subgroup G) ≤ normalizer (B : Set G) →
          radicalSylowCentralizer (T : Subgroup G) B =
            radicalSylowCentralizer (T : Subgroup G) L) := by
  have ha := maximal_nonquasisimple_normalizer_action_source h hmany hL hn
  obtain ⟨p,hp,hp3,he⟩ := ha.2.2.1
  refine ⟨p,hp,hp3,?_⟩
  intro B hB
  have hBL : B ≤ L := hB.2 ▸ le_sup_right
  refine ⟨he.of_mulEquiv (NormalizerReducedAction.supplementQuotientEquiv hBL ha.1 hB.2),
    supplement_radical ha.1 hB.2,ha.2.2.2.2 B hB.2,ha.2.2.2.1,?_,?_⟩
  · intro hBL
    exact ⟨NormalizerReducedAction.supplement_kernel hBL ha.1 hB.2,
      NormalizerReducedAction.supplement_range hBL ha.1 hB.2⟩
  · intro hTB
    exact supplement_radicalSylowCentralizer
      (radicalLocal_invariant_source hL.1.1
        (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn) hTB ha.1 hB.2

/-- The remaining Thompson branch is centralization of L/O∞(L), with
normality and the canonical perfect residual constructed from the source. -/
theorem canonical_supplement_setup_source
    (h : Hypothesis1311 T) {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) :
    IsPGroup 2 (radicalSylowCentralizer (T : Subgroup G) L) ∧
      (T : Subgroup G) ≤ normalizer (radicalSylowCentralizer (T : Subgroup G) L : Set G) ∧
      canonicalSupplement (T : Subgroup G) L ≤ L ∧
      (T : Subgroup G) ≤ normalizer (canonicalSupplement (T : Subgroup G) L : Set G) ∧
      Group.IsPerfect (canonicalSupplement (T : Subgroup G) L) ∧
      (L = ⁅L,ChapterB.thompsonJ (T : Subgroup G) 0⁆ ∨
        ChapterB.thompsonJ (T : Subgroup G) 0 ≤ radicalSylowCentralizer (T : Subgroup G) L) := by
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  exact ⟨T.isPGroup'.to_le (radicalSylowCentralizer_le _ _),
    sylow_normalizes_radicalSylowCentralizer hTL,canonicalSupplement_le _ _,
    sylow_normalizes_canonicalSupplement hTL,canonicalSupplement_perfect _ _,
    thompson_movement_or_le_radicalSylowCentralizer hL.1.1 hTL⟩

/-- The full uniqueness conclusion already holds in the faithful
nonquasisimple supplement branch, using original 13.1.4(2). -/
theorem nonquasisimple_faithful_supplement_unique
    (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L B : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (hB : B ∈ radicalSupplements (T : Subgroup G) L)
    (hf : IsFaithfulSignalizerType B) (hnB : ¬ IsQuasisimple (XiQuotient B)) :
    IsMaximalTwoLocal (normalizer (L : Set G)) ∧
      B ⊔ (T : Subgroup G) ≤ normalizer (L : Set G) ∧
      ∀ H : Subgroup G, IsMaximalTwoLocal H → B ⊔ (T : Subgroup G) ≤ H →
        H = normalizer (L : Set G) := by
  have hBL : B ≤ L := hB.2 ▸ le_sup_right
  have hLplus : L ∈ nonquasisimpleFaithful T :=
    ⟨(Adequate.mem_faithfulLocalComponents_iff T L).mpr ⟨hL.1.1,hL.2⟩,hn⟩
  obtain ⟨K,hK,hLK,_,_,hmax,hjoin,_⟩ := h.maximal_counterexample_of_many hmany hLplus
  have hKL : K = L := hL.1.2 K hK.1 hLK
  subst K
  have hBM : B ⊔ (T : Subgroup G) ≤ normalizer (L : Set G) :=
    (sup_le_sup_right hBL _).trans hjoin
  obtain ⟨D,_,_,_,_,_,_,hu,_⟩ := h.maximal_counterexample_of_many hmany
    ⟨(Adequate.mem_faithfulLocalComponents_iff T B).mpr ⟨hB.1,hf⟩,hnB⟩
  have he := hu _ hmax hBM
  exact ⟨hmax,hBM,fun H hH hBH => (hu H hH hBH).trans he.symm⟩

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements

namespace CFSG.Quasithin.Chapter14.Section03.FaithfulSource
open Chapter1 Chapter12.Section02 Chapter13.Section01
open Chapter13.Section01.SourceNonquasisimple.Supplements
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L₀ : Subgroup G}

/-- The original maximal counterexample has the literal R and L_R setup,
and all its radical supplements have prime-field PSL₂ radical quotient.
The centralizing Thompson alternative is not yet excluded. -/
theorem Hypothesis1331.nonquasisimple_supplement_setup_of_many
    (h : Hypothesis1331 T L₀)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ IsQuasisimple (XiQuotient L₀)) :
    ∃ K : Subgroup G, L₀ ≤ K ∧ FaithfulMaximalLocal T K ∧
      ¬ IsQuasisimple (XiQuotient K) ∧
      IsMaximalTwoLocal (normalizer (K : Set G)) ∧
      (T : Subgroup G) ≤ normalizer (radicalSylowCentralizer (T : Subgroup G) K : Set G) ∧
      (T : Subgroup G) ≤ normalizer (canonicalSupplement (T : Subgroup G) K : Set G) ∧
      (K = ⁅K,ChapterB.thompsonJ (T : Subgroup G) 0⁆ ∨
        ChapterB.thompsonJ (T : Subgroup G) 0 ≤ radicalSylowCentralizer (T : Subgroup G) K) ∧
      ∃ p : ℕ, p.Prime ∧ 3 < p ∧
        ∀ B ∈ radicalSupplements (T : Subgroup G) K,
          ClassicalGroup.IsPSL (B ⧸ solvableRadical B) 2 p ∧
          (solvableRadical B).map B.subtype = B ⊓ (solvableRadical K).map K.subtype := by
  obtain ⟨K,_,hLK,hf,hkn,hmax,_⟩ := h.maximal_counterexample_of_many hmany hn
  have hs := canonical_supplement_setup_source h.hypothesis1311 hf hkn.2
  obtain ⟨p,hp,hp3,ha⟩ := radical_supplements_action_source h.hypothesis1311 hmany hf hkn.2
  refine ⟨K,hLK,hf,hkn.2,hmax,hs.2.1,hs.2.2.2.1,hs.2.2.2.2.2,p,hp,hp3,?_⟩
  intro B hB
  exact ⟨(ha B hB).1,(ha B hB).2.1⟩

end CFSG.Quasithin.Chapter14.Section03.FaithfulSource
