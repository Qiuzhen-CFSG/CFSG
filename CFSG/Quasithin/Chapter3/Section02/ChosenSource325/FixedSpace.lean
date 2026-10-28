module

public import CFSG.Quasithin.Chapter3.Section02.SourceBaumann
public import CFSG.Quasithin.Chapter3.Section02.FundamentalModule
public import CFSG.Quasithin.Chapter3.Section01.CommonNormalKnownSimple
public import CFSG.Quasithin.Chapter3.Section01.StandingGuard.Cardinality
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete

/-!
# Fixed-space input to the chosen-seed alternatives

A nonzero fixed vector in the original seed remains in its full normalizer
orbit. The multiple-overgroup guard supplies an actual H-star comparison.
The proved common-normal theorem discharges the last earlier premise of the
FSU Thompson argument, giving the actual commutator and FF action on the
Sylow orbit. This supplies the input to D.3.20; it does not assert the
subsequent invariance of the seed.

Source: Aschbacher--Smith 3.2.2(6), 3.2.5 and D.3.20,
combined manuscript of 1 March 2004, printed pp.579--581 and204.
-/

public noncomputable section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open Representation.BinaryOffender Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.Chapter3.Section02.FundamentalSetup
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- Nonzero seed fixed space supplies the actual Thompson commutator and
the FF action on its Sylow orbit. The common-normal premise is discharged. -/
theorem fixedSpace_consequences_of_many
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hfix : D.seed ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥) :
    letI := D.module_elementary
    localOrbit T L = ⁅localOrbit T L, Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆ ∧
      IsFFModule (ChapterD.UniqueFactor.imageRepresentation (localJoin T L)
        D.moduleSubgroup D.join_normalizes_module) := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  obtain ⟨hM, hj, huniq⟩ := D.lemma_3_2_3_uniqueness hu
  obtain ⟨Y,hY⟩ := Chapter3.exists_HStar_of_hasMaximalOutside
    (Chapter3.hasMaximalOutside_of_many T hmany D.maximalLocal hM (le_sup_right.trans hj))
  have hfull : componentOrbit D.seed D.maximalLocal ⊓
      centralizer (localOrbit T L : Set G) ≠ ⊥ := by
    intro he
    apply hfix
    exact le_bot_iff.mp ((inf_le_inf_right _ (le_componentOrbit D.seed D.maximalLocal)).trans he.le)
  exact source_reduced_seed_overgroup_conclusions
    T (localOrbit T L) D.maximalLocal (localOrbit T L).le_normalizer
    (le_normalizer_componentOrbit L T) D.simpleQTKE hM
    D.internal_actor_residual D.internal_actor_cases D.seedSpace D.homogeneous.isIrrPlus
    (Chapter3.source_common_normal_knownSimple D.simpleQTKE T) huniq hfull hY

end CFSG.Quasithin.Chapter3.Section02.FundamentalSetup
