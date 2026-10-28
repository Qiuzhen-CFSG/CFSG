module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.G2.RelativeBlocks.CoreAction
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.G2.RelativeBlocks.Sections
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.G2.RelativeBlocks.FirstActor
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.G2.RelativeBlocks.SecondActor
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.G2.RelativeBlocks.OrbitSections
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.Blocks
public import Theory.AtlasPort.LinearGroups.G2.LieShortParabolic.Core

/-!
# Relative G₂ parabolic block obstructions

In a normal coordinate domain with two-group quotient, a short subgroup
lies in the domain by two-perfection. Each coordinate image is subnormal
and two-perfect, and its action on the coordinate two-core has commutators
of square one. This uses the full external core action, with no restriction
on individual coordinate kernels. If the coordinate actor calculation
forces these images to vanish, the common two-group kernel forces the
short subgroup to vanish, contradicting its nonzero module.

The component-orbit construction and both concrete actor calculations now
give the two block obstructions for the literal parabolic overgroups. This
retains component permutations, arbitrary central two-covers and the actual
derived-model intersections at field order two. No unknown block is identified
with a whole parabolic or residual.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, proof of 2.3.9(7), printed p.526. The only extra
premise of the first actor calculation is discharged by the proved short-local
core equality from `LieShortParabolic.Core`. The paired theorem therefore has
only the local setup, literal inner action and parabolic coordinates as inputs.
Construction of those coordinates and the final component exclusion remain
with the source assembly.
-/

public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.G2.RelativeBlocks

open Subgroup ChapterC
open scoped commutatorElement

variable {K P : Type*} [Group K] [Group P] [Finite K]

/-- The coordinate calculation rules out every short subnormal subgroup.
The hypothesis is about all subnormal two-perfect coordinate groups acting
on the ambient core, not an identification of the unknown block. -/
theorem not_short_of_coreSection (d : CoreSection K P)
    (hrigid : ∀ X : Subgroup P, X.IsSubnormal → IsPPerfect 2 X →
      (∀ q ∈ pCore 2 P, ∀ x ∈ X, (⁅q, x⁆ : P) ^ 2 = 1) → X = ⊥)
    (B : Subgroup K) (hs : B.IsSubnormal) : ¬ IsShort B := by
  intro hb
  have hBN := d.le_base B hb.twoPerfect
  have hpBN : IsPPerfect 2 (B.subgroupOf d.base) :=
    hb.twoPerfect.of_surjective (subgroupOfEquivOfLe hBN).symm.toMonoidHom
      (subgroupOfEquivOfLe hBN).symm.surjective
  have himage (i : Fin d.count) : (B.subgroupOf d.base).map (d.projection i) = ⊥ := by
    apply hrigid _ (hs.subgroupOf.map (d.surjective i))
      (hpBN.of_surjective ((d.projection i).subgroupMap (B.subgroupOf d.base))
        ((d.projection i).subgroupMap_surjective (B.subgroupOf d.base)))
    intro q hq x hx
    exact subnormal_short_overgroup_image_square B d.base hs hb hBN (d.projection i)
      ((d.core_image i).symm ▸ hq) hx
  have hker : B.subgroupOf d.base ≤ ⨅ i, (d.projection i).ker := by
    apply le_iInf
    intro i b hb'
    apply MonoidHom.mem_ker.mpr
    exact mem_bot.mp (himage i ▸ mem_map_of_mem (d.projection i) hb')
  have hpB : IsPGroup 2 B :=
    (d.kernel_two.to_le hker).of_equiv (subgroupOfEquivOfLe hBN)
  have hone := hb.twoPerfect.hom_eq_one_of_isPGroup hpB (MonoidHom.id B)
  apply hb.blockU_ne_bot
  apply eq_bot_iff.mpr
  intro b _
  exact mem_bot.mpr (DFunLike.congr_fun hone b)

/-- This structural reduction retains the original relative-subnormal
block interface, including its movement hypothesis. -/
theorem blockObstruction_of_coreSection {G : Type*} [Group G] [Finite G]
    (M S H : Subgroup G) (d : CoreSection H P)
    (hrigid : ∀ X : Subgroup P, X.IsSubnormal → IsPPerfect 2 X →
      (∀ q ∈ pCore 2 P, ∀ x ∈ X, (⁅q, x⁆ : P) ^ 2 = 1) → X = ⊥) :
    BlockObstruction M S H := by
  intro B hb _
  exact (not_short_of_coreSection d hrigid B hb.1.subnormal hb.1.short).elim

variable {G : Type*} [Group G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- No allowed moved block escapes from the first actual parabolic overgroup.
The short-local core equality, coordinate core images and actor membership
are supplied by the model, orbit and root calculations. -/
theorem first_blockObstruction (h : LocalSetup H L M S z)
    (d : ParabolicCoordinates L ((S : Subgroup H).map H.subtype)) :
    BlockObstruction M ((S : Subgroup H).map H.subtype) d.firstOvergroup := by
  let := h.finite
  obtain ⟨c⟩ := first_coreSection h d
  exact blockObstruction_of_coreSection M _ _ c
    (first_actor_eq_bot Atlas.G2.LieParabolicSetup.local₁_pCore)

/-- No allowed moved block escapes from the second actual parabolic overgroup.
The long-local and binary calculations discharge every model premise. -/
theorem second_blockObstruction (h : LocalSetup H L M S z)
    (d : ParabolicCoordinates L ((S : Subgroup H).map H.subtype)) :
    BlockObstruction M ((S : Subgroup H).map H.subtype) d.secondOvergroup := by
  let := h.finite
  obtain ⟨c⟩ := second_coreSection h d
  exact blockObstruction_of_coreSection M _ _ c second_actor_eq_bot

/-- The paired obstruction for the literal inner-action branch of 2.3.9(7).
The final source assembly supplies the coordinates; all core, actor and
central-kernel premises are discharged here. -/
theorem blockObstructions (h : LocalSetup H L M S z)
    (_hinner : ∃ t : L, IsConjugationProjection L z t)
    (d : ParabolicCoordinates L ((S : Subgroup H).map H.subtype)) :
    BlockObstruction M ((S : Subgroup H).map H.subtype) d.firstOvergroup ∧
      BlockObstruction M ((S : Subgroup H).map H.subtype) d.secondOvergroup :=
  ⟨first_blockObstruction h d, second_blockObstruction h d⟩

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.G2.RelativeBlocks

end
