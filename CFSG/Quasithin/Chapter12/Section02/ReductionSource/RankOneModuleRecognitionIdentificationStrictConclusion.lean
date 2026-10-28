module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentification
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationStrictConclusion

/-!
# The strict branch is excluded on the whole reduced Chapter 12 subgroup

Apply the original strict contradiction to R₂(LT), with its actual commutator
layer and the original sourceClosure. The resulting equality supplies the
intersection premise for the equality-recognition branch. All classification,
exceptional-action and whole-component premises have been discharged inside
the strict proof. The common LocalAnalysis and the remaining equality geometry
stay with the identification assembly.

Source: Aschbacher--Smith, 6.2.15--19 and 12.2.2(3d), printed pp.688--691,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
open Chapter6.Source Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L : Subgroup G} {n : ℕ} {z : G}

/-- The literal whole reduced layer cannot satisfy the strict branch. -/
theorem false_of_local_analysis_of_strict_reduced_intersection
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (A : LocalAnalysis (T : Subgroup G) L (normalizer (L : Set G)) (wholeReduced T L) z)
    (hz : z ∈ ZS (T : Subgroup G) L (wholeReduced T L)) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hstrict : ZS (T : Subgroup G) L (wholeReduced T L) <
      sourceClosure (T : Subgroup G) L (wholeReduced T L) z ⊓ commutatorLayer T L) : False :=
  A.false_of_local_analysis_of_strict_intersection h611 hnatural hz horder hTH hstrict

/-- The equality-recognition branch on R₂(LT) needs no intersection premise. -/
theorem reduced_sourceClosure_intersection_eq_ZS
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (A : LocalAnalysis (T : Subgroup G) L (normalizer (L : Set G)) (wholeReduced T L) z)
    (hz : z ∈ ZS (T : Subgroup G) L (wholeReduced T L)) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    sourceClosure (T : Subgroup G) L (wholeReduced T L) z ⊓ commutatorLayer T L =
      ZS (T : Subgroup G) L (wholeReduced T L) :=
  A.sourceClosure_intersection_eq_ZS h611 hnatural hz horder hTH

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
