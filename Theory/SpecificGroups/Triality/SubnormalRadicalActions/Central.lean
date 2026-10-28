module

public import Theory.SpecificGroups.Triality.FullParabolicActions
public import Theory.SpecificGroups.Triality.SubnormalRadicalActions.CentralRootSquare
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# Subnormal actors in the central triality parabolic

The ambient parabolic is retained throughout these results. Its full Levi
contains the original torus, and the radical is the relative subgroup of the
parabolic. The structural reductions identify the intrinsic two-core and the
full-Levi image of a subnormal actor. The unconditional final theorem uses the
checked root-coordinate rigidity: an exponent-two radical commutator has zero
image in the first cubic-field layer, so the faithful full-parabolic action
places the actor in the radical.

The root calculation retains arbitrary radical factors and the full torus.
It includes the binary `PSL₂(2)` case, where the genuine order-three actor
moves the first layer and hence cannot satisfy the commutator-square condition.
No perfectness assertion for `PSL₂(2)` or restriction `q > 2` is needed.

Sources: Aschbacher–Smith C.1.7/C.1.12, E.6.8 and F.1.11–12
(`refs/quasithin.pdf`, printed pp.123–124, 247–248 and 262–264);
GLS3 §§2.4 and 2.6 (`refs/KGroup/GLS3/chapter2.tex`).
-/

public section
noncomputable section

open Subgroup
open scoped commutatorElement

namespace Triality.Standard.Parabolics

variable (P : Parameters)

/-- The intrinsic two-core of a subnormal central-parabolic actor is its
intersection with the genuine root radical. -/
theorem central_candidate_twoCore (hp : P.prime = 2)
    (X : Subgroup (parabolic P .central)) (hsub : X.IsSubnormal) :
    pCore 2 X =
      ((radical P .central).subgroupOf (parabolic P .central)).comap X.subtype := by
  rw [pCore_subnormal_eq_comap 2 hsub, parabolic_twoCore_eq P hp .central]

/-- The full-Levi image of a subnormal actor has trivial two-core. -/
theorem central_candidate_fullLeviImage_twoCore
    (hp : P.prime = 2) (X : Subgroup (parabolic P .central))
    (hsub : X.IsSubnormal) :
    pCore 2 (X.map (fullLeviProjection P hp .central)) = ⊥ := by
  rw [pCore_subnormal_eq_comap 2
    (hsub.map (fullLeviProjection_surjective P hp .central)),
    fullLevi_twoCore_eq_bot P hp .central, MonoidHom.comap_bot]
  exact (MonoidHom.ker_eq_bot_iff _).mpr (Subgroup.subtype_injective _)

/-- The quotient by the intrinsic two-core is the actual image in the full
Levi complement. -/
def central_candidate_quotientEquivFullLeviImage
    (hp : P.prime = 2) (X : Subgroup (parabolic P .central))
    (hsub : X.IsSubnormal) :
    X ⧸ pCore 2 X ≃* X.map (fullLeviProjection P hp .central) := by
  let f := (fullLeviProjection P hp .central).subgroupMap X
  have hk : f.ker = pCore 2 X := by
    rw [Subgroup.ker_subgroupMap, fullLeviProjection_ker,
      central_candidate_twoCore P hp X hsub]
    rfl
  exact (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f
      ((fullLeviProjection P hp .central).subgroupMap_surjective X))

/-- Subnormality survives projection to the full Levi image. -/
theorem central_candidate_fullLeviImage_subnormal
    (hp : P.prime = 2) (X : Subgroup (parabolic P .central))
    (hsub : X.IsSubnormal) :
    (X.map (fullLeviProjection P hp .central)).IsSubnormal :=
  hsub.map (fullLeviProjection_surjective P hp .central)

/-- The radical commutator is forced into the intrinsic two-core commutator
layer of the actor. -/
theorem central_radical_commutator_le_core_commutator
    (hp : P.prime = 2) (X : Subgroup (parabolic P .central))
    (hsub : X.IsSubnormal) (hperfect : IsPPerfect 2 X) :
    ⁅(radical P .central).subgroupOf (parabolic P .central), X⁆ ≤
      (⁅pCore 2 X, (⊤ : Subgroup X)⁆).map X.subtype := by
  apply commutator_le_core_commutator_of_isSubnormal X
    ((radical P .central).subgroupOf (parabolic P .central))
    hsub hperfect
    (RadicalCoordinates.radical_isPGroup P hp .central).comap_subtype
  exact le_normalizer_of_normal

/-- The final central actor statement after the root-coordinate rigidity
calculation. The latter is kept as an explicit premise so that the binary
order-three branch and arbitrary radical factors cannot be discarded. -/
theorem central_subnormal_radical_le_of_root_rigidity
    (hroot : ∀ X : Subgroup (parabolic P .central), X.IsSubnormal →
      IsPPerfect 2 X →
      (∀ z ∈ ⁅(radical P .central).subgroupOf (parabolic P .central), X⁆,
        (z : parabolic P .central) ^ 2 = 1) →
      X ≤ (radical P .central).subgroupOf (parabolic P .central))
    (X : Subgroup (parabolic P .central)) (hsub : X.IsSubnormal)
    (hperfect : IsPPerfect 2 X)
    (hsq : ∀ z ∈ ⁅(radical P .central).subgroupOf (parabolic P .central), X⁆,
      (z : parabolic P .central) ^ 2 = 1) :
    X ≤ (radical P .central).subgroupOf (parabolic P .central) :=
  hroot X hsub hperfect hsq

/-- Every subnormal two-perfect actor whose entire radical commutator has
exponent at most two lies in the genuine central-parabolic radical. All root
action premises are discharged, including the binary order-three case. -/
theorem central_subnormal_radical_le (hp : P.prime = 2)
    (X : Subgroup (parabolic P .central)) (hsub : X.IsSubnormal)
    (hperfect : IsPPerfect 2 X)
    (hsq : ∀ z ∈ ⁅(radical P .central).subgroupOf (parabolic P .central), X⁆,
      (z : parabolic P .central) ^ 2 = 1) :
    X ≤ (radical P .central).subgroupOf (parabolic P .central) :=
  CentralRootSquare.le_radical_of_subnormal_of_isPPerfect P hp X hsub hperfect hsq

end Triality.Standard.Parabolics

end
