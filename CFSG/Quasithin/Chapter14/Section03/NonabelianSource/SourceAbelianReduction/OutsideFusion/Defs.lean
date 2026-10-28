module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.Defs

/-!
# The two core-return cases in original 14.3.21(2)

For a hypothetical outside conjugate t = z^y, the source proves z ∈ Q^y
by separate centralizer arguments according as t fixes the seed V or moves
it. These interfaces retain the literal Q = O₂(H), the original RQ, and
right conjugation. Neither case assumes factor self-centralization or Q=U.

Source: Aschbacher--Smith, Quasithin Groups, 14.3.21(2), printed p.998.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G}

/-- The core-return claim in the case [V,t]=1. -/
def FixedSeedCoreReturn (F : InvariantFlag T V 2) (L : Subgroup G) : Prop :=
  ∀ z ∈ F.Vi 1, z ≠ 1 → ∀ t ∈ (T : Subgroup G), orderOf t = 2 →
    t ∉ (F.I₂ L).pCoreIn 2 ⊔ F.H.pCoreIn 2 →
    t ∈ centralizer (V : Set G) →
    ∀ y : G, y⁻¹ * z * y = t → z ∈ conjugate (F.H.pCoreIn 2) y

/-- The core-return claim in the case [V,t]≠1. -/
def MovedSeedCoreReturn (F : InvariantFlag T V 2) (L : Subgroup G) : Prop :=
  ∀ z ∈ F.Vi 1, z ≠ 1 → ∀ t ∈ (T : Subgroup G), orderOf t = 2 →
    t ∉ (F.I₂ L).pCoreIn 2 ⊔ F.H.pCoreIn 2 →
    t ∉ centralizer (V : Set G) →
    ∀ y : G, y⁻¹ * z * y = t → z ∈ conjugate (F.H.pCoreIn 2) y

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction
