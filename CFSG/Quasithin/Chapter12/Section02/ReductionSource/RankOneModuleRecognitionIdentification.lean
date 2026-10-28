module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognition
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationContracts

/-!
# Identification inputs on the whole reduced Chapter 12 subgroup

The central involution and intersection dichotomy are constructed on the
literal R₂(LT) layer. The equality recognition no longer needs a supplied
cubic: it is constructed in the normalizer of the original T ∩ L.
In the strict case, earlier local analysis gives exactly the order-eight
intersection with the involution centralizer's two-core (6.2.14).

The earlier local-analysis producer and the two subsequent branch proofs
remain obligations of the identification assembly. These conditional
applications do not assert the full 6.2.19 identification or SmallExit.

Source: Aschbacher--Smith, 6.2.13--19 and 12.2.2(3d), pp.688--691 and 795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
open Chapter6.Source
open Chapter6.Source.RankOneRecognition
open Chapter6.M22Recognition.CentralizerExtension
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L : Subgroup G} {n : ℕ}

/-- Choose an actual proper involution centralizer containing T, retaining
both intersection branches on the whole reduced commutator layer. -/
theorem exists_reduced_centralizer_intersection_cases
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n) :
    ∃ z ∈ ZS (T : Subgroup G) L (wholeReduced T L), orderOf z = 2 ∧
      (T : Subgroup G) ≤ centralizer ({z} : Set G) ∧
      centralizer ({z} : Set G) ≠ ⊤ ∧
      (ZS (T : Subgroup G) L (wholeReduced T L) =
        sourceClosure (T : Subgroup G) L (wholeReduced T L) z ⊓ commutatorLayer T L ∨
      ZS (T : Subgroup G) L (wholeReduced T L) <
        sourceClosure (T : Subgroup G) L (wholeReduced T L) z ⊓ commutatorLayer T L) := by
  obtain ⟨z, hz, ho, hT⟩ := exists_central_involution_in_ZS h611
  exact ⟨z, hz, ho, hT, involution_centralizer_ne_top h611 hnatural hz ho,
    eq_or_lt_of_le (ZS_le_sourceClosure_intersection h611 hz)⟩

/-- Apply the constructed cubic in the actual Chapter 12 equality consumer.
Its quotient, relative normality and core geometry remain source inputs. -/
theorem m22_of_reduced_geometry_without_cubic
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (H : Subgroup G) (z : G) (hH : H = centralizer ({z} : Set G))
    (hTH : (T : Subgroup G) ≤ H)
    [((commutatorLayer T L).subgroupOf (normalizer (L : Set G))).Normal]
    (hq : CompatibleSymmetricFiveQuotient
      ((commutatorLayer T L).subgroupOf (normalizer (L : Set G)))
      (L.subgroupOf (normalizer (L : Set G))))
    (P : Subgroup H) [P.Normal] (hP : CoreData P)
    (ha : NaturalFourOrbit P
      ((ZS (T : Subgroup G) L (wholeReduced T L)).subgroupOf H))
    (hZS : coreCenter P ≤ (ZS (T : Subgroup G) L (wholeReduced T L)).subgroupOf H)
    (hSP : (ZS (T : Subgroup G) L (wholeReduced T L)).subgroupOf H ≤ P)
    (hPT : P.map H.subtype ≤ (T : Subgroup G))
    (hbranch : (sourceEight ((ZS (T : Subgroup G) L (wholeReduced T L)).subgroupOf H)).map
      H.subtype ⊓ commutatorLayer T L = ZS (T : Subgroup G) L (wholeReduced T L)) :
    Nonempty (G ≃* Sporadic.Mathieu.M22) := by
  exact m22_of_source_geometry_without_cubic h611 hnatural H z hH hTH hq P hP ha
    hZS hSP hPT hbranch

/-- The strict branch has the precise source 6.2.14 intersection on R₂(LT).
The common local-analysis producer must discharge A. -/
theorem strict_reduced_intersection_eq_core
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    {z : G}
    (A : LocalAnalysis (T : Subgroup G) L (normalizer (L : Set G)) (wholeReduced T L) z)
    (hstrict : ZS (T : Subgroup G) L (wholeReduced T L) <
      sourceClosure (T : Subgroup G) L (wholeReduced T L) z ⊓ commutatorLayer T L) :
    sourceClosure (T : Subgroup G) L (wholeReduced T L) z ⊓ commutatorLayer T L =
      commutatorLayer T L ⊓ (centralizer ({z} : Set G)).pCoreIn 2 ∧
    Nat.card (sourceClosure (T : Subgroup G) L (wholeReduced T L) z ⊓
      commutatorLayer T L : Subgroup G) = 8 := by
  exact A.strict_intersection_eq_core h611 hnatural hstrict

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
