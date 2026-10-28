module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.Local
public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.FixedHeptad
public import Theory.GroupTheory.AlternatingPowerTwoExtension

/-!
# The local overgroup needed for the M23 intersection

The projected involution determines a concrete heptad subgroup of L. To apply
the local block generation hypothesis, one needs a characteristic-two group
containing this subgroup and the whole supplied S. The definition below states
that construction's contract. Its alternating factors come from the orbit of
L under S; it does not identify S with its normalizer of L.

No containment in M or intersection conclusion is part of this definition.
Construction of this witness and exclusion of chi-zero blocks from its
extension shape are separate prerequisites of the source-theorem assembly.

Source: Aschbacher–Smith, 2.3.9(7)(f), printed pp.525–526, combined manuscript
of 1 March 2004, with the inner action from 1.1.5(3)(f), printed p.502.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement

open Subgroup Sporadic.Mathieu Sporadic.Mathieu.M23Geometry Theory.GroupTheory
open scoped Pointwise

variable {G : Type*} [Group G]

/-- The full-S local overgroup and its actual normal-series structure. -/
def MathieuTwentyThreeLocalEnvelope (L S : Subgroup G) (e : L ≃* M23)
    (t : L) (X : Subgroup G) : Prop :=
  X ≤ L ⊔ S ∧
    X ∈ Chapter1.HeOver G (S : Set G) ∧
    ((MulAction.stabilizer M23 (fixedHeptad (e t))).comap e.toMonoidHom).map L.subtype ≤ X ∧
    AlternatingPowerTwoExtension X 7

end CFSG.Quasithin.Chapter2.ComponentRefinement

end
