module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationStrictInputs
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationStrictMathieu

/-!
# The four-space catalogue reduction on the whole reduced layer

The triple-cover exclusion leaves only G.11.2(2) on the actual Chapter12
strict quotient, with its original form and order-divisibility clauses.
This conditional application still requires the genuine classifier and the
four-space elimination, both retained by qt-d-1222-recognition-strict-elimination.
The final owner qt-d-1222-rankone-recognition-identification supplies LocalAnalysis.

Source: Aschbacher--Smith, 6.2.19 and 12.2.2(3d), printed pp.691,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
open Chapter6.Source Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L : Subgroup G} {n : ℕ} {z : G}

/-- Conditional catalogue elimination for the original whole reduced layer,
retaining the literal action, original form and the four-space order clause. -/
theorem strict_reduced_catalogue_caseTwo
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
    (hc : ChapterG.Section11.Conclusion
      (strictRepresentation (T : Subgroup G) L (wholeReduced T L) z) B
      (strictCrossingImage (T : Subgroup G) L (wholeReduced T L) z d)) :
    ChapterG.Section11.CaseTwo
      (strictRepresentation (T : Subgroup G) L (wholeReduced T L) z) B :=
  A.strict_catalogue_caseTwo h611 hnatural hz horder hTH hstrict
    hdres hdH hdS hd3 B v h hB hc

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
