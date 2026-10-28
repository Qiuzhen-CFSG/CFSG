module

public import CFSG.Quasithin.ChapterI.Section01.SQTKMultipliers.Catalogue

/-!
# I.1.3: source statement and conditional complete assembly

`table_of_model_inputs` analyses every constructor of the complete known-simple
catalogue and proves both exhaustiveness and the six actual multiplier values.
This module quantifies that result over the original finite perfect simple
SQTK domain. Its remaining inputs are individual concrete kernel calculations
and family-specific rank restrictions, with the finished cases already inserted.
The source theorem remains open until every input is instantiated.

There is no Chapter B import. The separate B.5 adapter maps this exact neutral
statement to its existing multiplier interface without changing either table.
Source: Aschbacher--Smith I.1.3, printed p.407.
-/

public section
namespace CFSG.Quasithin.ChapterI.SQTKMultipliers
universe u

/-- Universal conditional source assembly. This is not the unconditional I.1.3
assertion: the two producers must discharge every listed model input. -/
theorem sourceStatement_of_model_inputs
    (hK : ∀ (S : Type u) [Group S] [Finite S] [Group.IsPerfect S] [IsSimpleGroup S],
      IsSQTK KnownSimple.IsKnownSimple S → KernelInputs S)
    (hR : ∀ (S : Type u) [Group S] [Finite S] [Group.IsPerfect S] [IsSimpleGroup S],
      IsSQTK KnownSimple.IsKnownSimple S → RankInputs S) : SourceStatement.{u} := by
  intro S _ _ _ _ hS
  exact table_of_model_inputs (hK S hS) (hR S hS) hS

end CFSG.Quasithin.ChapterI.SQTKMultipliers
