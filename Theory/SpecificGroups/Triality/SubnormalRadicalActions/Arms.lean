module

public import Theory.SpecificGroups.Triality.SubnormalRadicalActions.Arms.SquareTransfer
public import Theory.SpecificGroups.Triality.SubnormalRadicalActions.Arms.CentralTorusSquare
public import Theory.GroupTheory.PResidual.Defs

/-!
# Arms-parabolic subnormal radical action

The checked restrictions show that every candidate with elementary radical
commutator is solvable, and that its full-Levi image centralizes the simple
PSL₂(q³) subsystem. Displacement squares survive the full Levi projection,
including arbitrary radical factors. The central-torus square calculation
then makes every full-Levi image element trivial, placing the original
candidate in the radical.

The conditional assembly interface is preserved, and its root-calculation
premise is discharged in the unconditional theorems below. The argument
needs only subnormality; the final specialization gives the requested
two-perfect interface. The full torus and q = 2 are retained throughout.

Sources: Aschbacher--Smith C.1.7/C.1.12, E.6.8, F.1.11--12
(`refs/quasithin.pdf`, pp.123--124, 247--248, 262--264);
GLS3 §2.6 (`refs/KGroup/GLS3/chapter2.tex`).
-/

public section
noncomputable section
open Subgroup
open scoped commutatorElement
namespace Triality.Standard.Parabolics

/-- Assembly from the remaining central-torus square calculation. The proved
reduction needs only subnormality; two-perfection is not required here. -/
theorem arms_subnormal_radical_le_of_centralizer_square_rigidity
    (P : Parameters) (hp : P.prime = 2)
    (hroot : ∀ g : fullLevi P .arms,
      g ∈ centralizer ((levi P .arms).subgroupOf (fullLevi P .arms) :
        Set (fullLevi P .arms)) →
      (∀ r ∈ radical P .arms, ⁅r, g.val⁆ ^ 2 = 1) → g = 1)
    (X : Subgroup (parabolic P .arms)) (hsub : X.IsSubnormal)
    (hsq : ∀ z ∈ ⁅(radical P .arms).subgroupOf (parabolic P .arms), X⁆,
      (z : parabolic P .arms) ^ 2 = 1) :
    X ≤ (radical P .arms).subgroupOf (parabolic P .arms) := by
  intro x hx
  apply (fullLeviProjection_ker P hp .arms).le
  apply MonoidHom.mem_ker.mpr
  have hg := mem_map_of_mem (fullLeviProjection P hp .arms) hx
  exact hroot _ (arms_candidate_fullLeviImage_centralizes_levi P hp X hsub hsq hg)
    (arms_fullLeviImage_commutator_squares P hp X hsq _ hg)

/-- A subnormal subgroup with square-one radical commutator lies in the arms
radical. The hypothesis covers the whole commutator subgroup; all full-Levi
torus factors and original radical factors are retained, including at q = 2. -/
theorem arms_subnormal_radical_le_of_commutator_squares
    (P : Parameters) (hp : P.prime = 2)
    (X : Subgroup (parabolic P .arms)) (hsub : X.IsSubnormal)
    (hsq : ∀ z ∈ ⁅(radical P .arms).subgroupOf (parabolic P .arms), X⁆,
      (z : parabolic P .arms) ^ 2 = 1) :
    X ≤ (radical P .arms).subgroupOf (parabolic P .arms) :=
  arms_subnormal_radical_le_of_centralizer_square_rigidity P hp
    (arms_fullLevi_centralizer_square_rigidity P hp) X hsub hsq

/-- The subnormal two-perfect contract for the arms radical-action
application, with every concrete root-calculation premise discharged. -/
theorem arms_le_radical_of_subnormal_of_isPPerfect
    (P : Parameters) (hp : P.prime = 2)
    (X : Subgroup (parabolic P .arms))
    (hsub : X.IsSubnormal) (_hperfect : IsPPerfect 2 X)
    (hsq : ∀ z ∈ ⁅(radical P .arms).subgroupOf (parabolic P .arms), X⁆,
      (z : parabolic P .arms) ^ 2 = 1) :
    X ≤ (radical P .arms).subgroupOf (parabolic P .arms) :=
  arms_subnormal_radical_le_of_commutator_squares P hp X hsub hsq

end Triality.Standard.Parabolics
