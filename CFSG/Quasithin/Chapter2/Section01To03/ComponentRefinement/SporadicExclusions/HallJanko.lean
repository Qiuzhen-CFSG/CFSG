module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.Interface
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.HallJanko.CentralCoordinates
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.Held.LocalBlocks.NativeReduction
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.BlockSubnormalOrders

/-!
# The Hall–Janko local block exclusion

The actual quotient and inner action determine an invariant conjugate of the
full second parabolic. Its full inverse image, adjoined to the supplied Sylow
subgroup, has nontrivial self-centralizing two-core and generates the component
together with the ambient involution centralizer. The order-64 native two-core
and the central kernel of the covering component are retained.

Every subnormal chi-zero block has central-kernel coordinates in a power of
the actual second parabolic. The native subnormal order calculation excludes
these blocks: the nine quotient is not an allowed acting group, while the
cubic branch is too large to be the image of the order-twelve short group.
This uses the actual short-group module theorem, not an abstract module tag.

The checked calculation in `BlockSubnormalOrders` supplies the native premise:
the intrinsic two-residual/core quotient has order nine, and every cubic
element has more than twelve commutators with the actual order-64 radical.
The final cover thus requires only the source local setup and the actual J₂
quotient/action input. The parent retains the seven-case exclusion assembly.
Source: Aschbacher–Smith 2.3.9(7), printed p.526, and C.1.7–13, pp.123–125.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.HallJanko
open Subgroup Theory.GroupTheory
open Sporadic.LeechRelated.J2.ExceptionalParabolics

/-- The native subnormal calculation on the full second normalizer,
proved by `nativeSubnormalOrders`. -/
def NativeSubnormalOrders : Prop :=
  ∀ E : Subgroup Seed.p₂, E.IsSubnormal → IsPPerfect 2 E →
    Nat.card E = 1 ∨
      (Nat.card (E ⧸ pCore 2 E) = 3 ∧ 12 < Nat.card E) ∨
        Nat.card (E ⧸ pCore 2 E) = 9

/-- The concrete degree-100 carrier supplies the native calculation,
with relative subnormality and intrinsic two-cores. -/
theorem nativeSubnormalOrders : NativeSubnormalOrders :=
  BlockSubnormalOrders.subnormal_orders

variable {G : Type*} [Group G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- Apply the native calculation to the literal subnormal coordinates of
the actual blocks, allowing a central two-cover and component permutations. -/
theorem blockObstruction_of_subnormal_orders (ho : NativeSubnormalOrders)
    (h : LocalSetup H L M S z) (d : SporadicQuotientInput L z .j2)
    (g : LocalGeometry ((S : Subgroup H).map H.subtype) d) :
    BlockObstruction M ((S : Subgroup H).map H.subtype)
      (localOvergroup ((S : Subgroup H).map H.subtype) d g.localSubgroup) := by
  intro B hb _
  obtain ⟨n, q, hqc, hqs⟩ := block_central_coordinates h d g B hb.1
  exact (HeldCase.not_chiZero_of_central_power_large_orders hb.2 ho q hqc hqs).elim

/-- The full source cover once the separate native subgroup calculation is proved.
All geometric, Sylow, covering-center and action premises have been discharged. -/
noncomputable def centralizerBlockCover_of_subnormal_orders (ho : NativeSubnormalOrders)
    (h : LocalSetup H L M S z) (d : SporadicQuotientInput L z .j2) :
    CentralizerBlockCover L M ((S : Subgroup H).map H.subtype) z := by
  let g := localGeometry h d
  let K := localOvergroup ((S : Subgroup H).map H.subtype) d g.localSubgroup
  refine { locals := {K}, generated := ?_, within := ?_, even := ?_, obstruction := ?_ }
  · simpa only [sSup_singleton] using generated_of_model_join _ d g.localSubgroup g.generated
  · intro J hJ
    have he : J = K := Set.mem_singleton_iff.mp hJ
    subst J
    exact localOvergroup_le _ d g.localSubgroup
  · intro J hJ
    have he : J = K := Set.mem_singleton_iff.mp hJ
    subst J
    exact localOvergroup_mem_HeOver h d g
  · intro J hJ
    have he : J = K := Set.mem_singleton_iff.mp hJ
    subst J
    exact blockObstruction_of_subnormal_orders ho h d g

/-- Conditional application with exactly the desired output interface. -/
theorem nonempty_centralizerBlockCover_of_subnormal_orders (ho : NativeSubnormalOrders)
    (h : LocalSetup H L M S z) (d : SporadicQuotientInput L z .j2) :
    Nonempty (CentralizerBlockCover L M ((S : Subgroup H).map H.subtype) z) :=
  ⟨centralizerBlockCover_of_subnormal_orders ho h d⟩

/-- The actual J₂ local cover, retaining the central two-kernel and the
supplied Sylow subgroup, with its native block calculation discharged. -/
noncomputable def centralizerBlockCover (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .j2) :
    CentralizerBlockCover L M ((S : Subgroup H).map H.subtype) z :=
  centralizerBlockCover_of_subnormal_orders nativeSubnormalOrders h d

/-- The J₂ calculation required by Aschbacher–Smith 2.3.9(7), with no
additional geometry, subgroup-order or block-module premise. -/
theorem nonempty_centralizerBlockCover (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .j2) :
    Nonempty (CentralizerBlockCover L M ((S : Subgroup H).map H.subtype) z) :=
  ⟨centralizerBlockCover h d⟩

end CFSG.Quasithin.Chapter2.ComponentRefinement.HallJanko

end
