module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationStrictCentralCover
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationStrictExceptionalExclusion

/-!
# Excluding the exceptional full-four action on the whole reduced layer

The actual central cover and nontrivial crossed-center image exclude the
exceptional S₈ natural-plus-dual action under the original ambient data.
The old thirteen-row elimination therefore extends to the separately named
corrected alternatives. Exhaustion remains with the G.11 classifier; these
are the literal Chapter12 applications of the ambient exclusion.

Source: Aschbacher--Smith 6.2.15--19 and 12.2.2(3d), printed pp.688--691,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
open Chapter6.Source Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L : Subgroup G} {n : ℕ} {z : G}

/-- No exceptional whole-action model exists on the literal strict quotient. -/
theorem false_of_strict_reduced_whole_full_four
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (A : LocalAnalysis (T : Subgroup G) L (normalizer (L : Set G)) (wholeReduced T L) z)
    (hz : z ∈ ZS (T : Subgroup G) L (wholeReduced T L)) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hstrict : ZS (T : Subgroup G) L (wholeReduced T L) <
      sourceClosure (T : Subgroup G) L (wholeReduced T L) z ⊓ commutatorLayer T L)
    [IsElementaryAbelian 2 (StrictVectorQuotient (T : Subgroup G) L (wholeReduced T L) z)]
    {D : Subgroup (StrictActor (T : Subgroup G) L (wholeReduced T L) z)}
    {I J : Submodule (ZMod 2)
      (Additive (StrictVectorQuotient (T : Subgroup G) L (wholeReduced T L) z))}
    (m : ChapterG.Section11.FullLinearFour.WholeActionModel
      (strictRepresentation (T : Subgroup G) L (wholeReduced T L) z) D I J) : False :=
  A.false_of_strict_whole_full_four h611 hnatural hz horder hTH hstrict m

/-- The complete corrected alternatives contradict the original whole reduced layer. -/
theorem false_of_strict_reduced_corrected_catalogue
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (A : LocalAnalysis (T : Subgroup G) L (normalizer (L : Set G)) (wholeReduced T L) z)
    (hz : z ∈ ZS (T : Subgroup G) L (wholeReduced T L)) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hstrict : ZS (T : Subgroup G) L (wholeReduced T L) <
      sourceClosure (T : Subgroup G) L (wholeReduced T L) z ⊓ commutatorLayer T L)
    {d : G} (hdres : d ∈ strictCrossingResidual (T : Subgroup G) L (wholeReduced T L))
    (hdH : d ∉ centralizer ({z} : Set G))
    (hdS : d ∈ normalizer ((T : Subgroup G) ⊓ L : Set G)) (hd3 : orderOf d = 3)
    [IsElementaryAbelian 2 (StrictVectorQuotient (T : Subgroup G) L (wholeReduced T L) z)]
    [IsElementaryAbelian 2 (strictCrossingImage (T : Subgroup G) L (wholeReduced T L) z d)]
    (B : LinearMap.BilinForm (ZMod 2)
      (Additive (StrictVectorQuotient (T : Subgroup G) L (wholeReduced T L) z)))
    (v : Additive (StrictVectorQuotient (T : Subgroup G) L (wholeReduced T L) z))
    (h : ChapterG.Section10.Hypothesis
      (strictRepresentation (T : Subgroup G) L (wholeReduced T L) z) B v
      (strictHatSpace (T : Subgroup G) L (wholeReduced T L) z
        (strictCrossingIntersection (T : Subgroup G) L (wholeReduced T L) z d))
      (strictCrossingImage (T : Subgroup G) L (wholeReduced T L) z d)
      ((strictCrossingCenterImage (T : Subgroup G) L (wholeReduced T L) z d).subgroupOf
        (strictCrossingImage (T : Subgroup G) L (wholeReduced T L) z d)))
    (hB : ∀ u w : sourceClosure (T : Subgroup G) L (wholeReduced T L) z,
      B (strictHatElement (T : Subgroup G) L (wholeReduced T L) z u)
        (strictHatElement (T : Subgroup G) L (wholeReduced T L) z w) = 0 ↔ Commute u w)
    (hc : ChapterG.Section11.FullLinearFour.ConclusionWithFullLinearFour
      (strictRepresentation (T : Subgroup G) L (wholeReduced T L) z) B v
      (strictHatSpace (T : Subgroup G) L (wholeReduced T L) z
        (strictCrossingIntersection (T : Subgroup G) L (wholeReduced T L) z d))
      (strictCrossingImage (T : Subgroup G) L (wholeReduced T L) z d)
      ((strictCrossingCenterImage (T : Subgroup G) L (wholeReduced T L) z d).subgroupOf
        (strictCrossingImage (T : Subgroup G) L (wholeReduced T L) z d))) :
    False :=
  A.false_of_strict_corrected_catalogue h611 hnatural hz horder hTH hstrict
    hdres hdH hdS hd3 B v h hB hc


end CFSG.Quasithin.Chapter12.Section02.RankOneModule
