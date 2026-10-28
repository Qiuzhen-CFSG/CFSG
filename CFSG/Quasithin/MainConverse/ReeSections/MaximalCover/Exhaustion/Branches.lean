module

public import CFSG.Quasithin.MainConverse.ReeSections.MaximalCover.Exhaustion.Transport
public import Theory.GroupTheory.SolvableRadical.AbelianCharacteristic
public import Theory.GroupTheory.CComponent.RadicalFreePairs

/-!
# Remaining intrinsic branches of Ree maximal-subgroup exhaustion

After handling solvable maximal subgroups, there are three independent inputs:
the branch with a characteristic abelian subgroup, the branch with trivial
solvable radical and a nonabelian simple normal subgroup, and the branch with
trivial radical and two distinct commuting components. All normality and
subnormality here refer to the maximal subgroup, not to the ambient Ree group.

These are proof obligations, not assertions of Malle's theorem. Their geometric
and carrier-identification proofs must come from the genuine `ReeF4.Model`.
The finite-group reduction to these inputs is in the parent `Exhaustion` module.

Source: Malle, J. Algebra 139 (1991), 52–69; the unconditional list reproduced
inside the proof of Theorem 5 of arXiv:0910.4758, pp.2–3. The three-way reduction
uses the solvable radical and component calculus, not that paper's
representation-theoretic hypothesis.
-/

@[expose] public section

namespace CFSG.Quasithin.MainConverse.ReeSections

open Subgroup

/-- The local branch: an actual characteristic abelian subgroup is supplied.
The conclusion still requires the full source carrier identifications. -/
def AbelianCharacteristicMaximals : Prop :=
  ∀ m, 1 ≤ m → ∀ M : Subgroup (ReeF4.Model m), IsCoatom M →
    ¬ Group.IsSolvable M → ∀ A : Subgroup M,
      A.Characteristic → IsMulCommutative A → A ≠ ⊥ → MaximalAlternative m M

/-- The branch with a nonabelian simple normal subgroup of the maximal
subgroup. No classification of that simple subgroup is assumed. -/
def SimpleNormalMaximals : Prop :=
  ∀ m, 1 ≤ m → ∀ M : Subgroup (ReeF4.Model m), IsCoatom M →
    ¬ Group.IsSolvable M → solvableRadical M = ⊥ → ∀ S : Subgroup M,
      S.Normal → IsSimpleGroup S → ¬ IsMulCommutative S → MaximalAlternative m M

/-- The multiple-component branch. Triviality of the radical makes the
supplied C-components nonabelian simple; their actual carriers remain to be
identified. Commutation is explicit. -/
def CommutingComponentMaximals : Prop :=
  ∀ m, 1 ≤ m → ∀ M : Subgroup (ReeF4.Model m), IsCoatom M →
    ¬ Group.IsSolvable M → solvableRadical M = ⊥ → ∀ L K : Subgroup M,
      L.IsCComponent → K.IsCComponent → L ≠ K → ⁅L, K⁆ = ⊥ → MaximalAlternative m M

end CFSG.Quasithin.MainConverse.ReeSections
