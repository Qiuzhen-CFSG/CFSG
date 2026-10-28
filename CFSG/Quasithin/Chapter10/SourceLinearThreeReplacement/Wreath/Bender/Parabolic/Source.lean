module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Wreath.Bender.Parabolic.Recognition

/-!
# The source H-star recognition and seed placement

The original diagonal overlap supplies the nontrivial two-residual inside H.
The source component sieve recognizes the literal H/O₂(H) as S₅ wr C₂.
This discharges HStarRecognitionAt with exactly its permitted Hall-faithfulness
premise; the independent faithfulness producer remains necessary for 10.3.3.
Source: Aschbacher--Smith 10.2.3(3) and 10.3.3, pp.744--745,756.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Bender.Parabolic
variable {G : Type*} [Group G] [Finite G]

/-- The exact H-star source contract, including the literal seed and quotient. -/
theorem hstarRecognition (T : Sylow 2 G) : HStarRecognitionAt T := by
  intro hmany L D s d H hH hHC hf
  exact ⟨hstar_quotient hmany D s d hH hHC hf,seed_placement hmany D s d hH hHC hf⟩

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Bender.Parabolic
