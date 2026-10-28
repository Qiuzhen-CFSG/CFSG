module

public import CFSG.Quasithin.Chapter3.Section02.ReducedAmbient
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness.Source

/-!
# Fundamental Setup selection from the genuine source A and C theorems

The source 1.2.7 theorem supplies the unique maximal two-local subgroup
for the actual L₀T. A.1.42 selects the homogeneous seed of the same central
quotient type, giving both assertions of 3.2.3. The resulting full orbit
module is contained in R₂(M) and hence is elementary abelian.

The only remaining earlier classification premises are the universal
source Theorems A and C; the A.3.12 containment and noncentral structure
inputs of the older interface have been discharged.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemmas 3.2.2–3.2.3, printed pp.579–580.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open Representation.BinaryOffender Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Both assertions of the original Lemma 3.2.3, including actual module
selection and its central-quotient intertwiner. -/
theorem lemma_3_2_3_of_theoremsAC
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G) (L : Subgroup G)
    (hL : L ∈ Chapter1.LStar G (T : Subgroup G))
    (hf : ChapterA.Section04.IsFaithfulSignalizerType L)
    (hq : IsQuasisimple (L ⧸ pCore 2 L))
    (I : Submodule (ZMod 2) (Additive (ReducedNormal.ModuleGroup (localJoin T L))))
    (hI : IsIrrPlus (ReducedNormal.representation (localJoin T L))
      ((localOrbit T L).subgroupOf (localJoin T L)) I) :
    ∃ D : FundamentalSetup KnownSimple.IsKnownSimple T L,
      IsMaximalTwoLocal D.maximalLocal ∧ localJoin T L ≤ D.maximalLocal ∧
      (∀ M : Subgroup G, IsMaximalTwoLocal M → localJoin T L ≤ M →
        M = D.maximalLocal) ∧
      D.seedSpace ≤ orbitSpan (ReducedNormal.representation (localJoin T L))
        ((T : Subgroup G).subgroupOf (localJoin T L)) I ∧
      Nonempty (Representation.RepEquiv
        (centralQuotientRepresentation (ReducedNormal.representation (localJoin T L))
          ((localOrbit T L).subgroupOf (localJoin T L)) I hI.choose)
        (centralQuotientRepresentation (ReducedNormal.representation (localJoin T L))
          ((localOrbit T L).subgroupOf (localJoin T L)) D.seedSpace
            D.homogeneous.invariant)) := by
  obtain ⟨D, hDI, he⟩ := lemma_3_2_3_constituent hG T L hL hf hq I hI
  obtain ⟨hmax, hjoin, hu⟩ := D.lemma_3_2_3_uniqueness
    (Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC hA hC hG T hL)
  exact ⟨D, hmax, hjoin, hu, hDI, he⟩

namespace FundamentalSetup
variable {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The actual FSU full orbit lies in R₂(M), using only source A and C. -/
theorem fullModule_le_reduced_of_theoremsAC
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X) :
    D.fullModule ≤ (reducedTwoSubgroup D.maximalLocal).map D.maximalLocal.subtype :=
  D.fullModule_le_reduced
    (Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC hA hC D.simpleQTKE T D.maximal)

/-- The source elementary-section conclusion for the original V_M. -/
theorem fullModule_elementary_of_theoremsAC
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X) :
    IsElementaryAbelian 2 D.fullModule :=
  D.fullModule_elementary
    (Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC hA hC D.simpleQTKE T D.maximal)

end FundamentalSetup
end CFSG.Quasithin.Chapter3.Section02
