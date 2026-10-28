module
public import CFSG.Quasithin.ChapterB.Section02.Thompson.Factorization.SolvableThreePrime
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction.Generation
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.CanonicalGeometry.Qrc.Source
/-!
# The completed conditional FF contradiction in original 13.1.9

The solvable three-prime Thompson factorization is now proved for the
literal XR. Choose its supported odd prime from the original Fitting
quotient, obtain j in {0,1}, and feed the actual controlled normalizer into
the established FF inequality, odd-prime exclusion, whole natural tensor
identification and lifted generation contradiction.

The actual contrary maximal overgroup of every original radical supplement
is excluded, with a literal application to the maximal counterexample of
13.3.2. No factorization, controlled-index, FF, tensor or generation premise
remains. The three explicit earlier-source inputs are CanonicalStars,
QuasisimpleRigidity and QuasisimpleClassification, owned by
qt-d-1317-source. Supplement uniqueness and movement assembly remain with
qt-d-1317-supplements; this module proves their independent FF exclusion.

Source: Aschbacher–Smith 13.1.9, printed pp.870–871, and 13.3.2, p.884;
GLS, Number 2, G.26.18(a), printed pp.152–153.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open CFSG.Quasithin ChapterB
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction
open Chapter1 Chapter1.Section02 Chapter12.Section02 ChapterA.Section04 Escape
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

/-- The exact source normalizer product on XR, with the local selection and
proper-overgroup induction discharged. -/
theorem controlledIndex_factorization (h : Hypothesis1311 T)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) (p : ℕ) [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L))) :
    ControlledIndexFactorization (XiP p L) (radicalSylowCentralizer T L) := by
  let R := radicalSylowCentralizer T L
  let W := XiP p L ⊔ R
  obtain ⟨P,hP⟩ := controlledIndex_XR_sylow h hL hn p ho
  let : Group.IsSolvable W := controlledIndex_XR_solvable h hL hn p ho
  have hr : 1 < twoRank (P : Subgroup W) := by
    rw [←twoRank_map_injective W.subtype W.subtype_injective,hP]
    exact lt_of_lt_of_le (by decide : 1 < 3) (controlledIndex_radical_rank h hL hn)
  have hF := controlledIndex_XR_generalizedFitting h hL hn p ho hd
  have hc : centralizer (pCore 2 W : Set W) ≤ pCore 2 W := by
    rw [←hF]
    exact centralizer_generalizedFitting_le W
  have hf := solvable_threePrime_thompson_factorization P hr
    (controlledIndex_XR_three_coprime h hL hn p ho hd) hc
  have hh := thompson_factorization_subgroup_product W (P : Subgroup W) hf
  rw [hP] at hh
  exact hh

/-- Choose the original controlled Thompson index without any factorization
or index premise. The odd canonical prime is chosen from the source quotient. -/
theorem controlledIndex_exists (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hs : CanonicalStars T) {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) :
    ∃ j : ℕ, j ≤ 1 ∧ j < twoRank (radicalSylowCentralizer T L) ∧
      thompsonJ (radicalSylowCentralizer T L) 0 ≤ thompsonJ (radicalSylowCentralizer T L) j ∧
      normalizer (thompsonJ (radicalSylowCentralizer T L) j : Set G) ≤ normalizer (L : Set G) := by
  have h36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun D _ _ => ChapterA.Section02.theoremA_knownSimple (G := D))
    (fun D _ _ => ChapterA.Section02.theoremC_knownSimple (G := D))
  obtain ⟨p,hp,ho,_,hd,_,_⟩ := exists_odd_radical_source h.simpleQTKE h36
    ⟨(Adequate.mem_faithfulLocalComponents_iff T L).mpr ⟨hL.1.1,hL.2⟩,hn⟩
  let : Fact p.Prime := ⟨hp⟩
  exact controlledIndex_of_factorization h hmany hs hL hn p ho hd
    (controlledIndex_factorization h hL hn p ho hd)

/-- The original FF/tensor/generation contradiction, with controlled index
selection fully proved. Only the named earlier-source geometry remains. -/
theorem candidate_false (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hs : CanonicalStars T) (hrig : QuasisimpleRigidity T)
    (hclass : QuasisimpleClassification T) {L H C : Subgroup G}
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L))
    (hH : IsMaximalTwoLocal H) (hTH : (T : Subgroup G) ≤ H)
    (hne : H ≠ normalizer (L : Set G))
    (hC : C ∈ cComponentsIn H) (hAC : canonicalSupplement T L ≤ C) : False := by
  obtain ⟨j,hj,_,_,hN⟩ := controlledIndex_exists h hmany hs hL hn
  exact candidate_false_of_controlled_index h hmany hs hrig hclass hL hn hH hTH hne hC hAC hj hN

/-- Apply the FF contradiction to an actual contrary maximal overgroup of
an original radical supplement. All canonical geometry is constructed. -/
theorem supplement_candidate_false (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hs : CanonicalStars T) (hrig : QuasisimpleRigidity T)
    (hclass : QuasisimpleClassification T) {L B H : Subgroup G}
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L))
    (hB : B ∈ radicalSupplements T L) (hH : IsMaximalTwoLocal H)
    (hBH : B ⊔ (T : Subgroup G) ≤ H) (hne : H ≠ normalizer (L : Set G)) : False := by
  obtain ⟨C,_,hC,hAC,_,_⟩ := canonical_escape_for_supplement h hmany hs hrig hclass
    hL hn hB hH hBH hne
  exact candidate_false h hmany hs hrig hclass hL hn hH (le_sup_right.trans hBH) hne hC hAC
end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction

namespace CFSG.Quasithin.Chapter14.Section03.FaithfulSource
open Chapter1 Chapter12.Section02 Chapter13.Section01
open Chapter13.Section01.SourceNonquasisimple.Supplements
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L₀ : Subgroup G}

/-- The literal 13.3.2 maximal counterexample has no contrary supplement
overgroup, by the completed FF contradiction and constructed canonical geometry. -/
theorem Hypothesis1331.canonical_ff_exclusion_of_many (h : Hypothesis1331 T L₀)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ IsQuasisimple (XiQuotient L₀))
    (hs : Escape.CanonicalStars T) (hrig : Escape.QuasisimpleRigidity T)
    (hclass : Escape.QuasisimpleClassification T) :
    ∃ L : Subgroup G, L₀ ≤ L ∧ FaithfulMaximalLocal T L ∧
      ¬ IsQuasisimple (XiQuotient L) ∧
      ∀ B ∈ radicalSupplements T L, ∀ H : Subgroup G, IsMaximalTwoLocal H →
        B ⊔ (T : Subgroup G) ≤ H → H ≠ normalizer (L : Set G) → False := by
  obtain ⟨L,_,hL₀,hL,hLn,_,_⟩ := h.maximal_counterexample_of_many hmany hn
  exact ⟨L,hL₀,hL,hLn.2,fun B hB H hH hBH hne =>
    FFContradiction.supplement_candidate_false h.hypothesis1311 hmany hs hrig hclass
      hL hLn.2 hB hH hBH hne⟩
end CFSG.Quasithin.Chapter14.Section03.FaithfulSource
