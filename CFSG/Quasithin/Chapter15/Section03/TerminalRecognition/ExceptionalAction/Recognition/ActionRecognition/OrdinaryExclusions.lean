module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.Reduction
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.ExceptionalCase
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.Classification
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.G2
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.Permutation
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.TripleCover

/-!
# Ordinary-module exclusions in the terminal recognition

The proved initial reduction excludes the trivial, S₃ and hyperplane cases
of B.5.6 using the source's full commutator generation and four-dimensional
seed. It retains all remaining action and extension data, together with
transport of the fixed-space bound on the actual marked local core.

The marked residual-action calculations exclude the S₆, S₇ and G₂(2)
full quotients, passing the seed injectively through any central kernel.
In the surviving triple-cover branch, the offender image is the even cover
and the original module is irreducible of dimension six. Thus
`exceptionalCase_of_alternatives` constructs the intermediate recognition
witness from the two supplied classifications, with no further action or
module-recovery premise. The offender actor remains distinct from the full
quotient throughout.

`SourceInput.exceptionalCase_of_classification` applies this result to the
genuine SQTK offender cover. The complete universal classification input
and the full-quotient alternative remain explicit; proving those earlier
inputs and constructing vector coordinates belong to the source assembly.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, B.5.1
and B.5.6, printed pp.99 and 105, and the final proof of 15.3.1, printed
p.1155 (combined manuscript, 1 March 2004).
-/

public section

open Subgroup
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition

open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

universe u

variable {H : Type u} [Group H] [Finite H]
  {V : Subgroup H} [IsElementaryAbelian 2 (moduleClosure V)]

/-- The final ordinary-module exclusion in 15.3.1. The four full-quotient
possibilities and the complete FF alternative concern their respective
actual actors. The three ordinary quotients are impossible, and the
triple-cover branch recovers the irreducible original module of dimension six. -/
theorem exceptionalCase_of_alternatives (d : SourceInput V)
    (quotient : FullQuotientAlternative (coreQuotient H))
    (classification : SourceAlternative d.offenderAction) :
    Nonempty (ExceptionalCase d) := by
  cases quotient with
  | symmetricSix e =>
      exact (OrdinaryExclusions.Permutation.not_symmetric_six d classification e).elim
  | tripleSymmetricSix e =>
      exact ⟨exceptionalCase_of_tripleCover d e classification⟩
  | symmetricSeven e =>
      exact (OrdinaryExclusions.Permutation.not_symmetric_seven d classification e).elim
  | g2Two e =>
      exact (OrdinaryExclusions.not_g2 d classification e).elim

/-- Apply the exclusions to B.5.6 on the actual offender-generated subgroup.
The SQTK quotient, faithfulness, trivial two-core and offender generation
are supplied by the source input; no specialized classification is assumed. -/
theorem SourceInput.exceptionalCase_of_classification (d : SourceInput V)
    {K : GroupClass.{u}} (hH : IsSQTK K H)
    (quotient : FullQuotientAlternative (coreQuotient H))
    (classification : CompleteClassificationInput.{u,u} K) :
    Nonempty (ExceptionalCase d) :=
  exceptionalCase_of_alternatives d quotient (d.sourceAlternative hH classification)

end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition
