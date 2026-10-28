module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.Held.LocalGeometry
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.Held.Reduction
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.Held.LocalBlocks.CentralCoordinates
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.Held.LocalBlocks.NativeReduction
public import Theory.SpecificGroups.Held.AutomorphismLocalPair.SubnormalLarge

/-!
# Blocks in the constructed Held local family

The first named local is contained in C_G(z). The inner actor fixes the
component Sylow subgroup, hence lies in its center by the checked Held
self-normalizer theorem. The existing fixed-point lifting theorem retains
central two-kernels and proves the asserted ambient containment.

For the second named local, central component-orbit coordinates reduce the
block obstruction to the certified native subnormal calculation for the
normalizer of the join of both elementary order-64 classes. Its coordinate
images have two-core quotient of order three or nine, or are trivial. The
cubic branch has order greater than twelve, excluding the actual cubic
short-group model; order nine excludes the other chi-zero quotient models.
The central kernel then excludes any remaining block.

The final theorem proves the obstruction for the actual `heldLocalGeometry`
from the original local setup and Held quotient input, with no additional
local-calculation premise. Construction of the final centralizer block cover
remains with the parent Held exclusion.

Source: Aschbacher–Smith 2.3.9(7), printed p.526, and GLS3 Table 5.3p.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.ComponentRefinement.HeldCase
variable {G : Type*} [Group G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- Self-normalization of the actual Held Sylow puts the inner actor in its
center, so the model center local is fixed by the source involution. -/
theorem heldModelCenterLocal_le_fixedSubgroup (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) :
    heldModelLocal h d false ≤ (modelAut d d.action).fixedSubgroup := by
  obtain ⟨t, ht⟩ := modelAction_inner d
  have hc : t ∈ centralizer (modelSylow h d : Set Held.He) := by
    intro y hy
    have he := modelSylow_fixed h d y hy
    rw [← ht] at he
    change t * y * t⁻¹ = y at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hn := centralizer_le_normalizer (modelSylow h d : Set Held.He) hc
  rw [Held.LocalPairs.SylowGeometry.Calculations.inner_self_normalizing] at hn
  have htseed : t ∈ Held.AutomorphismLocalPair.centerSeed (modelSylow h d) :=
    (Held.AutomorphismLocalPair.mem_centerSeed _ _).mpr ⟨hn, fun y hy => hc y hy⟩
  intro x hx
  apply (MulAut.mem_fixedSubgroup _ _).mpr
  rw [← ht]
  change t * x * t⁻¹ = x
  have he := (Held.AutomorphismLocalPair.mem_centerLocal _ _).mp hx t htseed
  rw [he, mul_inv_cancel_right]

/-- Fixed points lift through the retained central two-kernel. The entire
first local therefore centralizes the original involution. -/
theorem heldCenterLocal_le_centralizer (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) :
    heldLocal h d false ≤ centralizer ({z} : Set G) := by
  apply sup_le
  · have hp : componentPreimage d (heldModelLocal h d false) ≤
        componentPreimage d (modelAut d d.action).fixedSubgroup :=
      map_mono (comap_mono (heldModelCenterLocal_le_fixedSubgroup h d))
    rw [componentPreimage_fixed h d] at hp
    exact hp.trans inf_le_right
  · intro s hs
    exact mem_centralizer_singleton_iff.mpr (h.central s hs)

/-- Every subgroup of the first local lies in M; in particular, every
allowed moved block does. -/
theorem heldCenterLocal_blockObstruction (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) :
    BlockObstruction M ((S : Subgroup H).map H.subtype) (heldLocal h d false) := by
  intro B _ _
  exact (map_subtype_le B).trans ((heldCenterLocal_le_centralizer h d).trans h.centralizer_le)

/-- The native calculation excludes all chi-zero blocks in the second
local, including those moved by the literal elementary-abelian-maximal J(S). -/
theorem heldLargeLocal_blockObstruction_of_orders (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he)
    (horders : SubnormalLargeLocalOrders (heldModelLocal h d true)) :
    BlockObstruction M ((S : Subgroup H).map H.subtype) (heldLocal h d true) := by
  intro B hB _
  obtain ⟨n, q, hqc, hqs⟩ := held_block_central_coordinates h d true B hB.1
  exact (not_chiZero_of_central_power_large_orders hB.2 horders q hqc hqs).elim

/-- Conditional assembly for exactly the constructed family. The unconditional
assembly below supplies the certified native large-local calculation. -/
theorem heldLocalGeometry_blockObstruction_of_large_orders
    (h : LocalSetup H L M S z) (d : SporadicQuotientInput L z .he)
    (horders : SubnormalLargeLocalOrders (heldModelLocal h d true)) :
    ∀ K ∈ (heldLocalGeometry h d).locals,
      BlockObstruction M ((S : Subgroup H).map H.subtype) K := by
  intro K hK
  obtain ⟨i, rfl⟩ := (mem_heldLocalGeometry_locals h d K).mp hK
  cases i
  · exact heldCenterLocal_blockObstruction h d
  · exact heldLargeLocal_blockObstruction_of_orders h d horders

/-- Specialize the certified native calculation at the actual image of the
source component Sylow subgroup. This discharges the large-local order premise. -/
theorem heldModelLargeLocal_orders (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) :
    SubnormalLargeLocalOrders (heldModelLocal h d true) :=
  Held.AutomorphismLocalPair.subnormal_largeLocal_orders (modelSylow h d)

/-- Every allowed block in the actual large local is excluded by its native
subnormal coordinates, retaining the central two-kernel throughout. -/
theorem heldLargeLocal_blockObstruction (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) :
    BlockObstruction M ((S : Subgroup H).map H.subtype) (heldLocal h d true) :=
  heldLargeLocal_blockObstruction_of_orders h d (heldModelLargeLocal_orders h d)

/-- All allowed moved blocks in the named Held local family lie in M, under
exactly the source local setup and its actual Held quotient identification. -/
theorem heldLocalGeometry_blockObstruction
    (h : LocalSetup H L M S z) (d : SporadicQuotientInput L z .he) :
    ∀ K ∈ (heldLocalGeometry h d).locals,
      BlockObstruction M ((S : Subgroup H).map H.subtype) K :=
  heldLocalGeometry_blockObstruction_of_large_orders h d (heldModelLargeLocal_orders h d)

end CFSG.Quasithin.Chapter2.ComponentRefinement.HeldCase

end
