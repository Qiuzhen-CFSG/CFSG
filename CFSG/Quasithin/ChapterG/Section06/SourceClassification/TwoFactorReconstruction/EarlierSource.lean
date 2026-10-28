module

public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.TwoFactorReconstruction.Complete
public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.EarlierSourceReduction

/-!
# The G.6.4 source frontier after reconstructing the two-factor branch

Apply the completed original two-factor theorem to the genuine B.5 source
dispatcher. The only remaining rank-one row is the full quasisimple action
list. The independent earlier A.2, A.3.6, and B.4 source inputs are unchanged.

Source: Aschbacher–Smith, G.6.4, printed pp.345–346.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterG.Section06
open ChapterB.SourceInduction HighThreeRank.CoverCentralizer.SourceConstruction
universe u v
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {a : G}
  {Cover : Type u} [Group Cover] {q : Cover →* G}

/-- The unrestricted original G.6 rank-one domain now leaves only the quasisimple row. -/
theorem Hypotheses.rank_one_quasisimple_source_reduction
    (hA : SemisimpleInput.{u} KnownSimple.IsKnownSimple)
    (h36 : Chapter1.Section02.A36Input.{u} KnownSimple.IsKnownSimple)
    (h4 : ProjectiveLine.IrreducibleClassificationInput.{u,v} KnownSimple.IsKnownSimple)
    (h : Hypotheses KnownSimple.IsKnownSimple ρ a q)
    (ht : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1) :
    Conclusion ρ a ∨
      (IsQuasisimple (generalizedFitting (normalClosure ({a} : Set G))) ∧
        Nonempty (ProjectiveLine.QuasisimpleSourceConclusion
          (ρ.comp (normalClosure ({a} : Set G)).subtype)
          (generalizedFitting (normalClosure ({a} : Set G))))) := by
  rcases h.rank_one_source_reduction hA h36 h4 ht with hc | hq | hd
  · exact Or.inl hc
  · exact Or.inr hq
  · obtain ⟨d⟩ := hd
    exact Or.inl (h.conclusion_of_twoFactor_source ht d)

end CFSG.Quasithin.ChapterG.Section06
