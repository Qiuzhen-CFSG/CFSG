module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.ModelSieve.QuotientInputs

/-!
# The residual input for comparing the C.2.7 stabilizers

The image M* of H ∩ Lᵤ should have a perfect normal subgroup, namely the
image of K, whose two-core quotient is A₅ and whose quotient in M* is a
two-group. This local extension property is independent of the model of Lᵤ*.
It can therefore be proved separately from the Borel, alternating-stabilizer,
and parabolic calculations that consume it.

This file defines that intermediate property; it does not assert it for the
fixed centralizer. The producer must construct the literal K-image witness.
The final comparison owner must discharge this premise before deriving
`Nonquasisimple.ReducedModels`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
14.7.68(2), pp.1071–1072; the geometric alternatives in C.2.7, pp.145–147.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Nonquasisimple
open Subgroup

/-- A perfect normal A₅-by-two-core subgroup with two-group quotient.
This is a property of the local stabilizer, with no model assertion about
its containing component. -/
def HasA5TwoResidual (M : Type*) [Group M] : Prop :=
  ∃ B : Subgroup M, ∃ _ : B.Normal,
    Group.IsPerfect B ∧
      Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) ∧
      IsPGroup 2 (M ⧸ B)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Nonquasisimple
