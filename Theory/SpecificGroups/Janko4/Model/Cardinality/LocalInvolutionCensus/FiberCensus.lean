module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Labels
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.KernelRows
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.RepresentativeMatrices

/-!
# Assembling the concrete max2 fiber census from finite certificates

The labelled source forest transfers through the actual source-to-local group
isomorphism to a positive conjugacy cover inside H. In a fixed quotient fiber,
the two displacement ranks identify the forest label. Exhaustive kernel
coordinates then inject a representative's class fiber into its checked mask
list, giving the required upper bound without any class-distinctness table,
centralizer-generation premise or exact class cardinality assertion.

`coverage` and `classFiber_card_le` discharge the finite premises using the
certified source forest, the eleven actual representative rank pairs and the
seven required square-one equations. `certificates` packages both conclusions.
Only the local order upper bound remains in these final statements.

Source motivation: Aschbacher--Smith, refs/quasithin.pdf, printed pp.64--65,
A.6.1--4. ATLAS witness provenance is in FiberCensus/source/README.md.
-/

set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency true

public section
namespace Janko4.Cardinality.LocalInvolutionCensus.FiberCensus
open Coordinates
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound

attribute [local irreducible] sourceSubgroupEquivLocal

theorem representative_rankPair_of_source
    (hr : ∀ k : Fin 11, sourceRankPair (sourceRepresentative k) = expectedRanks k)
    (k : Fin 11) : rankPair (representative k) = expectedRanks k := by
  rw [← sourceEquiv_representative, rankPair_sourceEquiv, hr]

theorem representative_square_one_of_source
    (k : Fin 11) (hs : (sourceRepresentative k) ^ 2 = 1) :
    (representative k) ^ 2 = 1 := by
  rw [← sourceEquiv_representative, ← map_pow, hs, map_one]

/-- Transfer the labelled source forest through the actual group equivalence. -/
theorem local_forest_of_source
    (hf : ∀ (j : Fin 4) (m : Fin 8192), (sourceElement j m) ^ 2 = 1 →
      ∃ k : Fin 11, fiberIndex k = j ∧ m ∈ masks k ∧
        IsConj (sourceRepresentative k) (sourceElement j m))
    (j : Fin 4) (m : Fin 8192) (hs : (element j m) ^ 2 = 1) :
    ∃ k : Fin 11, fiberIndex k = j ∧ m ∈ masks k ∧
      IsConj (representative k) (element j m) := by
  have hs' : (sourceElement j m) ^ 2 = 1 := by
    apply sourceSubgroupEquivLocal.injective
    rw [map_pow, sourceEquiv_element, hs, map_one]
  obtain ⟨k, hk, hm, hc⟩ := hf j m hs'
  refine ⟨k, hk, hm, ?_⟩
  have he : IsConj (sourceSubgroupEquivLocal (sourceRepresentative k))
      (sourceSubgroupEquivLocal (sourceElement j m)) :=
    sourceSubgroupEquivLocal.toMonoidHom.map_isConj hc
  rw [sourceEquiv_representative, sourceEquiv_element] at he
  exact he

/-- The forest proves the requested positive conjugacy cover inside H. -/
theorem coverage_of_source_forest
    (hf : ∀ (j : Fin 4) (m : Fin 8192), (sourceElement j m) ^ 2 = 1 →
      ∃ k : Fin 11, fiberIndex k = j ∧ m ∈ masks k ∧
        IsConj (sourceRepresentative k) (sourceElement j m))
    (j : Fin 4) (m : Fin 8192)
    (hs : (localKernelProduct m * lift j) ^ 2 = 1) :
    ∃ k : Fin 11, IsConj (representative k) (localKernelProduct m * lift j) := by
  obtain ⟨k, _, _, hc⟩ := local_forest_of_source hf j m hs
  exact ⟨k, hc⟩

/-- Ranks identify the forest label of a conjugate within a fixed fiber. -/
theorem mem_masks_of_isConj
    (hf : ∀ (j : Fin 4) (m : Fin 8192), (element j m) ^ 2 = 1 →
      ∃ k : Fin 11, fiberIndex k = j ∧ m ∈ masks k ∧
        IsConj (representative k) (element j m))
    (hr : ∀ k : Fin 11, rankPair (representative k) = expectedRanks k)
    (i : Fin 11) (hs : (representative i) ^ 2 = 1) (m : Fin 8192)
    (hc : IsConj (representative i) (element (fiberIndex i) m)) : m ∈ masks i := by
  have hm : (element (fiberIndex i) m) ^ 2 = 1 := by
    have h := IsConj.pow 2 hc
    rw [hs, isConj_one_right] at h
    exact h
  obtain ⟨k, hk, hmem, hkc⟩ := hf (fiberIndex i) m hm
  have he : expectedRanks k = expectedRanks i := by
    rw [← hr k, ← hr i]
    exact rankPair_of_isConj (hkc.trans hc.symm)
  have hki := expectedRanks_separate k i hk he
  simpa only [hki] using hmem

/-- The permitted local order bound makes the coordinates exhaustive; rank
separation then injects a class fiber into one of the checked finite lists. -/
theorem classFiber_card_le_of_forest
    (hH : Nat.card H ≤ 21799895040)
    (hf : ∀ (j : Fin 4) (m : Fin 8192), (element j m) ^ 2 = 1 →
      ∃ k : Fin 11, fiberIndex k = j ∧ m ∈ masks k ∧
        IsConj (representative k) (element j m))
    (hr : ∀ k : Fin 11, rankPair (representative k) = expectedRanks k)
    (i : Fin 11) (hs : (representative i) ^ 2 = 1) :
    Nat.card (classFiber (representative i)) ≤ fiberBound i := by
  classical
  have hcoord (u : classFiber (representative i)) :
      ∃ m : Fin 8192, u.val = element (fiberIndex i) m ∧ m ∈ masks i := by
    have hq : localQuotientMap u.val = localQuotientMap (lift (fiberIndex i)) := by
      have he := u.property.2.trans (q_representative i)
      exact congrArg (fun w : Q => (w : QuotientMatrixˣ)) he
    obtain ⟨m, hm⟩ := local_fiber hH u.val (lift (fiberIndex i)) hq
    have hc : IsConj (representative i) (element (fiberIndex i) m) := by
      change IsConj (representative i) (localKernelProduct m * lift (fiberIndex i))
      rw [← hm]
      exact u.property.1
    exact ⟨m, hm, mem_masks_of_isConj hf hr i hs m hc⟩
  choose c hc hm using hcoord
  let f : classFiber (representative i) → {m : Fin 8192 // m ∈ masks i} :=
    fun u => ⟨c u, hm u⟩
  have hinj : Function.Injective f := by
    intro u v he
    have he' : c u = c v := congrArg Subtype.val he
    apply Subtype.ext
    rw [hc u, hc v, he']
  exact (Nat.card_le_card_of_injective f hinj).trans (masks_card_le i)

/-- Assembly from two independent finite certificates. Neither the labelled
forest nor the representative matrix facts is asserted by this theorem. -/
theorem certificates_of_source_forest_and_ranks
    (hH : Nat.card H ≤ 21799895040)
    (hf : ∀ (j : Fin 4) (m : Fin 8192), (sourceElement j m) ^ 2 = 1 →
      ∃ k : Fin 11, fiberIndex k = j ∧ m ∈ masks k ∧
        IsConj (sourceRepresentative k) (sourceElement j m))
    (hr : ∀ k : Fin 11, sourceRankPair (sourceRepresentative k) = expectedRanks k)
    (hs : ∀ k : Fin 11, Required k → (sourceRepresentative k) ^ 2 = 1) :
    (∀ (j : Fin 4) (m : Fin 8192), (localKernelProduct m * lift j) ^ 2 = 1 →
      ∃ k : Fin 11, IsConj (representative k) (localKernelProduct m * lift j)) ∧
    (∀ i : Fin 11, Required i → Nat.card (classFiber (representative i)) ≤ fiberBound i) := by
  refine ⟨coverage_of_source_forest hf, fun i hi => ?_⟩
  exact classFiber_card_le_of_forest hH (local_forest_of_source hf)
    (representative_rankPair_of_source hr) i (representative_square_one_of_source i (hs i hi))

/-- Every square-one coordinate in the four prescribed fibers is conjugate
inside the literal H to one of the eleven fixed representatives. -/
theorem coverage (hH : Nat.card H ≤ 21799895040)
    (j : Fin 4) (m : Fin 8192)
    (hs : (localKernelProduct m * lift j) ^ 2 = 1) :
    ∃ k : Fin 11, IsConj (representative k) (localKernelProduct m * lift j) :=
  coverage_of_source_forest (source_forest hH) j m hs

/-- The seven required class fibers have their prescribed upper bounds:
1386, 2772, 128, 64, 96, 192 and 16 at indices 2, 3, 4, 6, 7, 8 and 9. -/
theorem classFiber_card_le (hH : Nat.card H ≤ 21799895040)
    (i : Fin 11) (hi : Required i) :
    Nat.card (classFiber (representative i)) ≤ fiberBound i :=
  classFiber_card_le_of_forest hH (local_forest_of_source (source_forest hH))
    (representative_rankPair_of_source sourceRepresentative_rankPair) i
    (representative_square_one_of_source i (sourceRepresentative_square_one i hi))

/-- Both concrete fiber certificates, with all finite proof obligations
discharged and only the permitted local order upper bound remaining. -/
theorem certificates (hH : Nat.card H ≤ 21799895040) :
    (∀ (j : Fin 4) (m : Fin 8192), (localKernelProduct m * lift j) ^ 2 = 1 →
      ∃ k : Fin 11, IsConj (representative k) (localKernelProduct m * lift j)) ∧
    (∀ i : Fin 11, Required i → Nat.card (classFiber (representative i)) ≤ fiberBound i) :=
  ⟨coverage hH, classFiber_card_le hH⟩

end Janko4.Cardinality.LocalInvolutionCensus.FiberCensus
