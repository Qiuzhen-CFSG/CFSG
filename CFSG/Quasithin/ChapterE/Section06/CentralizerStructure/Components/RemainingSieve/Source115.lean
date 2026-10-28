module
public import CFSG.Quasithin.Chapter1.SourceInputs.KnownSimple
public import CFSG.Quasithin.Chapter1.Section01.ModelActions115.Transport
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.RemainingSieve.SourceInputs
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.SourceLocal
/-!
# Original 1.1.5(3) on the embedded E.6 component

Apply the complete known-simple marked involution theorem to the actual
component subtype in H, then transport its automorphism and all six model/action
alternatives along the canonical subgroup equivalence. Its ambient conjugation
remains literally conjugation by the original z. This discharges Earlier115Three
for the E.6.8 source dispatcher without adding a classification input.
Source: Aschbacher–Smith, 1.1.5(3) and E.6.8, pp.501–503,247.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components.RemainingSieve
open Chapter15.Section03.Candidates.ComponentStructure
universe u
variable {G : Type u} [Group G] [Finite G]

theorem source_earlier115Three : Earlier115Three KnownSimple.IsKnownSimple G := by
  intro hG H S B z hin L hL
  obtain ⟨he,hnot,α,hα,hmodel⟩ := Chapter1.lemma_1_1_5_three_knownSimple hG H S B z hin
    (L.subgroupOf H) hL.2
  rw [map_subgroupOf_eq_of_le hL.1] at he hnot
  let e : L.subgroupOf H ≃* L := subgroupOfEquivOfLe hL.1
  refine ⟨he,hnot,MulAut.congr e α,?_,hmodel.of_mulEquiv e.symm⟩
  intro x
  exact hα (e.symm x)
end CFSG.Quasithin.ChapterE.Section06.Components.RemainingSieve
