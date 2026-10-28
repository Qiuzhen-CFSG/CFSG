module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.PointKernelAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.CentralizerModule

public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Normalizer
public import Theory.GroupTheory.ReducedNormal.CentralSeedOvergroup
public import Theory.GroupTheory.NonsolvableTwoLocal

/-!
# The original centralizer module for the solvable branch: structure at the original group

Specialize the original proof to `Structural1222At` at the same G,T.
All action maps, full quotient kernels and source hypotheses are retained;
no universal Chapter12 record is inferred. Intrinsic model and group lemmas
are reused from the preserved source module. This family feeds guarded
solvable-centralizer recognition on the actual five-dimensional module.

Source: Aschbacher--Smith 13.4.8--9, printed pp.904--907;
see the original `Solvable/LocalProduct/CentralizerModule` proof for the local step.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The actual two-core of the escaping centralizer is already contained in M. -/
theorem centralizer_core_le_normalizer_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D) {z : G}
    (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1) :
    (centralizer ({z} : Set G)).pCoreIn 2 ≤ normalizer (L : Set G) := by
  apply le_trans _ (LocalGeometry.centralizerOmegaOrbit_centralizer_le_normalizer_at h structural D m z)
  apply le_centralizer_iff.mp
  intro w hw y hy
  obtain ⟨a, ha, rfl⟩ := hy
  exact congrArg Subtype.val ((centralizerOmegaOrbit_reduced h₀ hz hz1).le_centralizer_pCore
    (show (⟨w, centralizerOmegaOrbit_le hz hw⟩ : centralizer ({z} : Set G)) ∈
      (centralizerOmegaOrbit T z).subgroupOf (centralizer ({z} : Set G)) from hw) a ha)

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
