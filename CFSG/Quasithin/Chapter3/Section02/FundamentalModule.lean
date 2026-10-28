module

public import CFSG.Quasithin.Chapter3.Section02.FundamentalActor
public import CFSG.Quasithin.Chapter3.Section02.InternalFromReducedSeed
public import CFSG.Quasithin.Chapter3.Section02.SourceUniqueness

/-!
# The faithful module belonging to the original Fundamental Setup

The actual FSU actor supplies both structural inputs of D.3.2. A.1.11
embeds its original seed into R₂(M), preserving the same subgroup of G.
The linear M-orbit span is proved to be the original V_M. D.3.3 then
constructs the faithful action satisfying every condition of D.3.1.
The source A and C corollary uses the proved 1.2.7 uniqueness theorem.

Source: Aschbacher–Smith, Hypothesis 3.2.1, Lemma 3.2.2(7) and
Remark 3.2.4, combined manuscript of 1 March 2004, printed pp.579–580.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open Representation.BinaryOffender Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.Chapter3.Section02.FundamentalSetup
open ChapterD.Section03
universe u
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}
  {T : Sylow 2 G} {L : Subgroup G} (D : FundamentalSetup K T L)

/-- The literal seed and orbit subgroup of the FSU satisfy D.3.2's
linear hypotheses; the internal actor and reducedness inputs are proved. -/
theorem exists_internal_seed
    (h127 : Chapter1.Section02.NonsolvableUniquenessConclusion T L) :
    ∃ J : Submodule (ZMod 2) (Additive (ReducedNormal.ModuleGroup D.maximalLocal)),
      ReducedNormal.subspaceImage D.maximalLocal J = D.seed ∧
      ReducedNormal.subspaceImage D.maximalLocal
        (orbitSpan (ReducedNormal.representation D.maximalLocal) ⊤ J) = D.fullModule ∧
      InternalModuleHypotheses K (ReducedNormal.representation D.maximalLocal)
        D.ambientSylow ((localOrbit T L).subgroupOf D.maximalLocal) J := by
  obtain ⟨hmax, _, _⟩ := D.lemma_3_2_3_uniqueness h127
  obtain ⟨J, hJ, hi⟩ := source_reduced_seed_internal T (localOrbit T L) D.maximalLocal
    (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T)
    D.simpleQTKE hmax D.internal_actor_residual D.internal_actor_cases
    D.seedSpace D.homogeneous.isIrrPlus
  refine ⟨J, hJ, ?_, hi⟩
  have hm := ReducedNormal.subspaceImage_orbitSpan D.maximalLocal D.maximalLocal le_rfl J
  rw [subgroupOf_self, hJ] at hm
  exact hm.trans D.fullModule_eq_seed_orbit.symm

/-- The D.3.1 assertion for the original FSU V_M, including its original
seed and the literal faithful action on that orbit span. -/
theorem exists_faithful_seed
    (h127 : Chapter1.Section02.NonsolvableUniquenessConclusion T L) :
    ∃ J : Submodule (ZMod 2) (Additive (ReducedNormal.ModuleGroup D.maximalLocal)),
      ReducedNormal.subspaceImage D.maximalLocal J = D.seed ∧
      ReducedNormal.subspaceImage D.maximalLocal
        (orbitSpan (ReducedNormal.representation D.maximalLocal) ⊤ J) = D.fullModule ∧
      SourceHypotheses K
        (subspaceImageRepresentation (ReducedNormal.representation D.maximalLocal)
          (orbitSpan (ReducedNormal.representation D.maximalLocal) ⊤ J))
        (D.ambientSylow.mapSurjective (invariantActionHom_surjective
          (ReducedNormal.representation D.maximalLocal) _ (orbitSpan_invariant _ ⊤ J)))
        (restrictedSubgroup (ReducedNormal.representation D.maximalLocal)
          (orbitSpan (ReducedNormal.representation D.maximalLocal) ⊤ J)
          ((localOrbit T L).subgroupOf D.maximalLocal))
        (J.comap (orbitSpan (ReducedNormal.representation D.maximalLocal) ⊤ J).subtype) := by
  obtain ⟨J, hJ, hW, hi⟩ := D.exists_internal_seed h127
  exact ⟨J, hJ, hW, hi.faithfulOrbit_source⟩

/-- The source A and C hypotheses discharge the last earlier uniqueness
premise in the original FSU application of D.3.3. -/
theorem exists_internal_seed_of_theoremsAC
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X) :
    ∃ J : Submodule (ZMod 2) (Additive (ReducedNormal.ModuleGroup D.maximalLocal)),
      ReducedNormal.subspaceImage D.maximalLocal J = D.seed ∧
      ReducedNormal.subspaceImage D.maximalLocal
        (orbitSpan (ReducedNormal.representation D.maximalLocal) ⊤ J) = D.fullModule ∧
      InternalModuleHypotheses KnownSimple.IsKnownSimple
        (ReducedNormal.representation D.maximalLocal) D.ambientSylow
        ((localOrbit T L).subgroupOf D.maximalLocal) J :=
  D.exists_internal_seed (Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    hA hC D.simpleQTKE T D.maximal)

end CFSG.Quasithin.Chapter3.Section02.FundamentalSetup
