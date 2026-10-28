module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.Actions
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.Elementary
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.Geometry

/-!
# The parabolic positions needed at the end of 15.3.49

The local data below retain `Y₀ = θ(M ∩ H)`, `H = LY₀T`, relative
normality, and the solvable-overgroup conclusion (j). These are inputs
from (i)–(l), not new proofs of those conclusions.

A binary minimal parabolic is a transported flag stabilizer whose flag
contains every proper dimension except one specified node. The exceptional
degree-four middle node is recorded together with an isomorphism of the
whole star quotient to `S₈` that sends the component to the actual `A₈`.
This specifies the group and position, without assuming a module exclusion.

The small overgroup family uses literal `K/O₂(K)`, independently of the
star quotient for `H`. In particular no identification of these different
quotients is implicit in its definition.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
pp.1144–1145, especially (j), (k), (l), and the `L₄(2), L₅(2)` paragraph.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions

open Subgroup

namespace BinaryGeometry

open Chapter2.ComponentRefinement.LieType.Binary

variable {K : Type*} [Group K]

/-- A minimal parabolic of the concrete binary component, with its deleted
node specified by an actual flag. -/
structure Position (L P : Subgroup K) (n : ℕ) [NeZero n] where
  model : L ≃* PSL n
  flag : Flag n
  node : ℕ
  node_pos : 0 < node
  node_lt : node < n
  types_eq : flag.types = ((Finset.range n).erase 0).erase node
  parabolic_eq : P = ambientFlagStabilizer model flag

/-- The exceptional extension and component are compatibly identified as
`S₈` and its alternating subgroup; the flag omits dimension two. -/
structure MiddleNodeEight (L P : Subgroup K) where
  position : Position L P 4
  middle : position.node = 2
  extension : K ≃* Equiv.Perm (Fin 8)
  component_image : L.map extension.toMonoidHom = alternatingGroup (Fin 8)

end BinaryGeometry

variable {G : Type*} [Group G]

/-- The two genuinely different quotients of the smaller overgroups. -/
def SmallQuotient (K : Subgroup G) : Prop :=
  Nonempty ((K ⧸ pCore 2 K) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∨
  Nonempty ((K ⧸ pCore 2 K) ≃*
    Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2))

/-- The overgroups in the generation paragraph on p.1145. -/
def smallOvergroups (H Y₀ T : Subgroup G) : Set (Subgroup G) :=
  {K | Y₀ ⊔ T ≤ K ∧ K ≤ H ∧ SmallQuotient K}

/-- The exact local inputs used in the parabolic-generation reduction.
All normality and Sylow assertions are relative to `H`. -/
structure ReducedLocalData (H M L Y₀ T : Subgroup G) : Prop where
  factorization : H = (L ⊔ Y₀) ⊔ T
  cubic_in_component : Y₀ ≤ L
  cubic_eq_theta : Y₀ = theta (M ⊓ H)
  sylow : Chapter1.IsSylowIn 2 T H
  sylow_in_M : T ≤ M
  normalizes_component : H ≤ normalizer (L : Set G)
  outside : ¬ H ≤ M
  solvable_overgroups : ∀ K : Subgroup G, Y₀ ⊔ T ≤ K → K ≤ H →
    Group.IsSolvable K → K ≤ M ⊓ H

theorem ReducedLocalData.factorization_LT {H M L Y₀ T : Subgroup G}
    (d : ReducedLocalData H M L Y₀ T) : H = L ⊔ T := by
  rw [d.factorization, sup_eq_left.mpr d.cubic_in_component]

theorem ReducedLocalData.cubic_le_M {H M L Y₀ T : Subgroup G}
    (d : ReducedLocalData H M L Y₀ T) : Y₀ ≤ M := by
  rw [d.cubic_eq_theta]
  exact (theta_le _).trans inf_le_left

/-- The minimal parabolic in the component, retaining the intersection
`T₀ = T ∩ L` before taking its star image. -/
def componentParabolic (H L Y₀ T : Subgroup G) : Subgroup (H ⧸ pCore 2 H) :=
  starImage H Y₀ ⊔ starImage H (T ⊓ L)

/-- The precise binary geometry input from (l). Generation by smaller
overgroups and the exceptional-extension alternative are conclusions still
to be proved from these data. -/
structure BinaryLocalData (H M L Y₀ T : Subgroup G) (n : ℕ) [NeZero n] where
  reduced : ReducedLocalData H M L Y₀ T
  dimension : n = 4 ∨ n = 5
  position : BinaryGeometry.Position (starImage H L) (componentParabolic H L Y₀ T) n
  invariant : starImage H T ≤ normalizer (componentParabolic H L Y₀ T : Set (H ⧸ pCore 2 H))

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions
