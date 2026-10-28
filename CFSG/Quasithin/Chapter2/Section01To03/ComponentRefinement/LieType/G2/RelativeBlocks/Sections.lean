module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.G2.Parameters
public import Theory.GroupTheory.PPerfectHom

/-!
# Coordinate sections for the relative G₂ parabolic argument

The target coordinate group is a parabolic inside the actual derived G₂
model. In particular at field order two it is a subgroup of G₂(2)′.

`CoreSection` describes a normal subgroup with two-group quotient mapping
onto copies of that coordinate group. The common kernel is a two-group,
and each coordinate maps its two-core onto the target two-core. These are
group-structural obligations for the commuting component orbit; the record
contains no block, module classification, or block obstruction.

The construction from `ParabolicCoordinates` is separate from the local
actor calculation. Together they are intended to justify the relative-block
step in Aschbacher–Smith 2.3.9(7), printed p.526, while retaining both
component permutations and central two-cover kernels.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.G2.RelativeBlocks

open Subgroup

/-- The first parabolic restricted to the derived model, at every parameter. -/
def firstModel (F : Type*) [Field F] : Subgroup (commutator (Atlas.G2.Model F)) :=
  Atlas.G2.LieParabolicSetup.parabolic₁.subgroupOf (commutator (Atlas.G2.Model F))

/-- The second parabolic restricted to the derived model, at every parameter. -/
def secondModel (F : Type*) [Field F] : Subgroup (commutator (Atlas.G2.Model F)) :=
  Atlas.G2.LieParabolicSetup.parabolic₂.subgroupOf (commutator (Atlas.G2.Model F))

/-- The precise coordinate structure needed from the orbit of a parabolic
under the ambient Sylow subgroup. A coordinate kernel can contain other
components; only the common kernel is required to be a two-group. -/
structure CoreSection (K P : Type*) [Group K] [Group P] where
  base : Subgroup K
  normal : base.Normal
  quotient_two : @IsPGroup 2 (K ⧸ base) (@QuotientGroup.Quotient.group K _ base normal)
  count : ℕ
  projection : Fin count → base →* P
  surjective : ∀ i, Function.Surjective (projection i)
  core_image : ∀ i, (pCore 2 base).map (projection i) = pCore 2 P
  kernel_two : IsPGroup 2 (⨅ i, (projection i).ker : Subgroup base)

attribute [instance] CoreSection.normal

namespace CoreSection

variable {K P : Type*} [Group K] [Group P] (d : CoreSection K P)

/-- Two-perfection places the block in the normal coordinate domain, even
if the Sylow subgroup permutes the individual components. -/
theorem le_base (B : Subgroup K) (hp : IsPPerfect 2 B) : B ≤ d.base := by
  have hh := hp.hom_eq_one_of_isPGroup d.quotient_two
    ((QuotientGroup.mk' d.base).comp B.subtype)
  intro b hb
  exact (QuotientGroup.eq_one_iff b).mp (DFunLike.congr_fun hh ⟨b, hb⟩)

end CoreSection

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.G2.RelativeBlocks

end
