module

public import CFSG.Quasithin.Chapter3.Section02.FundamentalModule
public import Theory.GroupTheory.ReducedNormal.OrbitReduced

/-!
# Reducedness of the actual full orbit module

The faithful D.3.3 orbit image has trivial two-core by D.3.4(1).
Identify its action kernel with the centralizer of the original orbit
subgroup to obtain membership in the R₂-family, rather than only
containment in R₂(M). The generic theorem retains both original actor
alternatives; the FSU application constructs its actor inputs.

Source: Aschbacher–Smith, Lemma 3.2.2(2), combined manuscript of
1 March 2004, printed p.579.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open Representation.BinaryOffender Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.Chapter3.Section02
open ChapterD.Section03
universe u
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}

/-- The full orbit of the literal reduced-module seed is a member of
R₂(M), for either structural actor alternative of 3.2.2. -/
theorem source_reduced_seed_orbit_reduced
    (T : Sylow 2 G) (X M : Subgroup G) (hXM : X ≤ M) (hTM : (T : Subgroup G) ≤ M)
    [(X.subgroupOf M).Normal]
    (hG : IsSimpleQTKE K G) (hM : IsMaximalTwoLocal M)
    (hX : pResidual 2 (X.subgroupOf M) = ⊤)
    (hc : InternalActorCases (T.subtype hTM) (X.subgroupOf M)
      (by rw [normalizer_eq_top]; exact le_top))
    (I : Submodule (ZMod 2)
      (Additive (ReducedNormal.ModuleGroup (X ⊔ (T : Subgroup G)))))
    (hI : IsIrrPlus (ReducedNormal.representation (X ⊔ (T : Subgroup G)))
      (X.subgroupOf (X ⊔ (T : Subgroup G))) I) :
    IsPReduced 2 ((componentOrbit
      (ReducedNormal.subspaceImage (X ⊔ (T : Subgroup G)) I) M).subgroupOf M) := by
  obtain ⟨J, hJ, hi⟩ := source_reduced_seed_internal T X M hXM hTM hG hM hX hc I hI
  have hr := ReducedNormal.subspaceImage_isPReduced_of_action_core M
    (orbitSpan (ReducedNormal.representation M) ⊤ J)
    (orbitSpan_invariant _ ⊤ J) hi.faithfulOrbit_twoCore_eq_bot
  have hm := ReducedNormal.subspaceImage_orbitSpan M M le_rfl J
  rw [subgroupOf_self, hJ] at hm
  rwa [hm] at hr

namespace FundamentalSetup
variable {T : Sylow 2 G} {L : Subgroup G} (D : FundamentalSetup K T L)

/-- The original FSU V_M is reduced, with no reducedness premise. -/
theorem fullModule_reduced
    (h127 : Chapter1.Section02.NonsolvableUniquenessConclusion T L) :
    IsPReduced 2 (D.fullModule.subgroupOf D.maximalLocal) := by
  obtain ⟨J, _, hW, hi⟩ := D.exists_internal_seed h127
  have hr := ReducedNormal.subspaceImage_isPReduced_of_action_core D.maximalLocal
    (orbitSpan (ReducedNormal.representation D.maximalLocal) ⊤ J)
    (orbitSpan_invariant _ ⊤ J) hi.faithfulOrbit_twoCore_eq_bot
  rwa [hW] at hr

/-- Genuine Theorems A and C suffice for the source reducedness conclusion. -/
theorem fullModule_reduced_of_theoremsAC
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X) :
    IsPReduced 2 (D.fullModule.subgroupOf D.maximalLocal) :=
  D.fullModule_reduced (Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    hA hC D.simpleQTKE T D.maximal)

end FundamentalSetup
end CFSG.Quasithin.Chapter3.Section02
