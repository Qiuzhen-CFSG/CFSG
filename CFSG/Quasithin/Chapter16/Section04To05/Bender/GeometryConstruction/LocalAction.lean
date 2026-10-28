module

public import CFSG.Quasithin.Chapter16.Section04To05.Bender.Contracts

/-!+# The outstanding local-action construction

`LocalAction` is a precise prerequisite contract for the first paragraph of
Proposition 16.5.1 and the equality X⁺ = N_L(V)⁺ in its third paragraph.
It is not a theorem asserting existence. The geometry assembly must construct
this data from the actual rank-one component and its permitted central cover.

In particular, the elementary factors are not asserted to be disjoint.
The direct decomposition is with [V,X], which retains the exceptional Suzuki
cover. The image equality concerns the actual normalizer representation.
The moving-conjugator construction is independent of this contract.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Proposition
16.5.1, printed p.1194; the cover exception uses 16.1.2 and I.2.2(4).
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction
open Subgroup
variable {G : Type*} [Group G]

/-- The model calculation still to be constructed. This record does not assert its existence. -/
structure LocalAction (T : Sylow 2 G) (L R : Subgroup G) (n : ℕ) where
  actor : Subgroup G
  actor_le : actor ≤ L ⊓ normalizer (componentSylow T L : Set G)
  actor_cyclic : IsCyclic actor
  actor_card : Nat.card actor = 2 ^ n - 1
  commuting_elementary : IsElementaryAbelian 2 (omegaOneAmbient (commutingSylow T L))
  component_elementary : IsElementaryAbelian 2 (omegaOneAmbient (componentSylow T L))
  fixed_eq : benderSpace T L ⊓ centralizer (actor : Set G) =
    omegaOneAmbient (commutingSylow T L)
  disjoint : Disjoint (omegaOneAmbient (commutingSylow T L)) ⁅benderSpace T L, actor⁆
  span : omegaOneAmbient (commutingSylow T L) ⊔ ⁅benderSpace T L, actor⁆ = benderSpace T L
  moved_card : Nat.card ↥(⁅benderSpace T L, actor⁆ : Subgroup G) = 2 ^ n
  regular : ∀ v ∈ ⁅benderSpace T L, actor⁆, v ≠ 1 →
    ∀ w ∈ ⁅benderSpace T L, actor⁆, w ≠ 1 → ∃! x : actor, MulAut.conj (x : G) v = w
  image_eq : inducedActor (benderSpace T L) actor = inducedActor (benderSpace T L) L
  omega_le : omegaOneAmbient R ≤ benderSpace T L

end CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction
