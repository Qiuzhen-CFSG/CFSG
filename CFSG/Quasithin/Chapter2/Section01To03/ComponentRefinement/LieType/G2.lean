module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.Setup
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.Blocks
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.BlockObstructions
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.G2.Parameters
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.G2.RootObstructions
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.G2.BinaryResidual
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.G2.Geometry
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.G2.RelativeBlocks

/-!
# Exclusion of G₂ components and central two-covers

The G₂ cases of Aschbacher–Smith 1.1.5(3)(a),(b), printed pp.501–502,
use actual derived-group and central-quotient isomorphisms. The inner action
is supplied separately as `IsConjugationProjection L z t`; in a central
cover its implementing element is not assumed to be an involution.

For the two-parabolic argument of 2.3.9(7), printed p.526, coordinates
record the actual map from L to G₂, its kernel, the Sylow intersection,
and invariance under N_S(L). The two local overgroups are generated with
all of S. No assertion that S normalizes L is made.

The geometry constructs both overgroups in HeOver and proves that they
generate L. The relative-block calculation uses their component-orbit
coordinates: the actual external two-core acts on a short subnormal block
with square-one commutators, whereas the concrete parabolic root calculations
force each two-perfect coordinate image to vanish. The common two-group
kernel then contradicts the block's nonzero commutator module.

Thus both overgroups satisfy `BlockObstruction`. Applying the source block
generation input forces L ≤ M, contradicting `LocalSetup.outside`. All
short-local, coordinate and actor premises are discharged by the imported
proofs. The exclusion covers G₂(2)′, rather than full G₂(2), and every central
two-cover allowed by 1.1.5(3)(b).
-/

public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.G2

open Subgroup

variable {G : Type*} [Group G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The G₂ cases of 1.1.5(3)(a,b) are incompatible with the local block
decompositions in the two-parabolic argument of 2.3.9(7). -/
theorem not_isModelCase (h : LocalSetup H L M S z)
    (hinner : ∃ t : L, IsConjugationProjection L z t) : ¬ IsModelCase L := by
  intro hmodel
  obtain ⟨d, hgen, he₁, he₂⟩ := exists_parabolicCoordinates_HeOver h hmodel hinner
  obtain ⟨ho₁, ho₂⟩ := RelativeBlocks.blockObstructions h hinner d
  exact h.outside (le_of_pair_blockObstruction h.blocks hgen
    d.firstOvergroup_le d.secondOvergroup_le he₁ he₂ ho₁ ho₂)

/-- The actual derived G₂ model is excluded over every field of order 2ⁿ
with n ≥ 1, including the proper derived subgroup G₂(2)′. -/
theorem not_derived_model (h : LocalSetup H L M S z)
    (hinner : ∃ t : L, IsConjugationProjection L z t)
    (F : Type) [Field F] [Finite F] (n : ℕ) (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ n) :
    ¬ Nonempty (L ≃* commutator (Atlas.G2.Model F)) := by
  intro he
  exact not_isModelCase h hinner (Or.inl ⟨F, inferInstance, inferInstance, n, hn, hF, he⟩)

/-- Every source-permitted central two-cover of G₂(4) is excluded, with
its full central two-core retained and no restriction on the kernel order. -/
theorem not_central_quotient_model (h : LocalSetup H L M S z)
    (hinner : ∃ t : L, IsConjugationProjection L z t)
    (hcenter : center L = pCore 2 L) (hcore : pCore 2 L ≠ ⊥)
    (F : Type) [Field F] [Finite F] (hF : Nat.card F = 4) :
    ¬ Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.G2.Model F) := by
  intro he
  exact not_isModelCase h hinner
    (Or.inr ⟨hcenter, hcore, F, inferInstance, inferInstance, hF, he⟩)

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.G2

end
