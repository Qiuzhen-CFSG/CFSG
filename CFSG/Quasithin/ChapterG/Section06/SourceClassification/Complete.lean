module

public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.IrreducibleReconstruction.Complete
public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.TwoFactorReconstruction.Complete
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.Complete

/-!
# The complete original rank-one classification G.6.4

The proved known-simple Theorems A and C and corrected B.4 classification
supply the earlier source inputs to B.5. Its actual normal-closure action
then reduces to the reconstructed irreducible row or the reconstructed
two-factor row. Both include the ambient extension and central-Sylow clause.
No module reconstruction, quotient faithfulness, or classification conclusion
is assumed in addition to the original G.6.1 and rank-one hypotheses.

Source: Aschbacher–Smith, G.6.4, printed pp.345–346.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterG.Section06
open ChapterB.SourceInduction
universe u v
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {a : G}
  {Cover : Type u} [Group Cover] {q : Cover →* G}

/-- All four clauses of the original G.6.4, over the full known-simple catalogue. -/
theorem lemma_G_6_4
    (h : Hypotheses KnownSimple.IsKnownSimple ρ a q)
    (ht : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1) :
    Conclusion ρ a := by
  have hA := fun (G : Type u) [Group G] [Finite G] =>
    ChapterA.Section02.theoremA_knownSimple (G := G)
  have h36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC hA
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  rcases h.rank_one_irreducible_source_reduction hA h36
      ChapterB.SourceClassification.irreducibleClassification_knownSimple ht with hc | hi | hd
  · exact hc
  · exact h.conclusion_of_irreducible_source ht hi
  · obtain ⟨d⟩ := hd
    exact h.conclusion_of_twoFactor_source ht d

end CFSG.Quasithin.ChapterG.Section06
