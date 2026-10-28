module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.NormalOrdinaryRecognition
public import CFSG.Quasithin.Chapter13.Section05.A5Source.NormalDoubledAmalgam
public import CFSG.Quasithin.ChapterF.Section05.SourceRecognition

/-!
# The original normal A₅ recognition branch

The ordinary branch gives PSU₄(2). In the doubled branch, the actual source
inclusion amalgam supplies the F.5 hypotheses in the original ambient group;
F.5 ambient recognition gives PSL₄(3). The case split therefore supplies
13.5.17 and the precise degree-five model alternative used by the subsequent
component-selection argument. Only the genuine earlier A.3.12 source input
remains; no amalgam, marking or completion-recognition premise is retained.
Source: Aschbacher--Smith13.5.17, printed p.922.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open Section06.TerminalContradiction.Ratio Section08
open ChapterF.GreenBook.LieModels.UnitaryFour
open ChapterF.UnitaryTwo
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G} [IsElementaryAbelian 2 V]
  (d : Context T L V V₁ V₂ V₃)
  (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
    IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
    B ∈ ChapterA.Section03.localCComponents S → Chapter1.Section02.A312Conclusion B)
  (hH : H ∈ Source.Hz (residualCentralizer L V₁) (T : Subgroup G)
    (centralizer (V₁ : Set G)) (normalizer (L : Set G)))
  (hU : ¬ IsMulCommutative (Source.UH H V₃))
  (hn : ((residualCentralizer L V₁).subgroupOf H).Normal)
include d hA312 hH hU hn


theorem source_normal_doubled_isPSL
    (hdoubled : L ⊔ (T : Subgroup G) ≠ L) : ClassicalGroup.IsPSL G 4 3 := by
  obtain ⟨c,z,h,_,_,_,_⟩ := source_normal_doubled_completion d hA312 hH hU hn hdoubled
  exact ⟨ZMod 3,inferInstance,inferInstance,Nat.card_zmod 3,
    ChapterF.Section05.source_ambient_equiv c (H ⊔ (L ⊔ (T : Subgroup G))).subtype z h⟩

theorem source13_5_17 : ClassicalGroup.IsPSU G 4 2 ∨ ClassicalGroup.IsPSL G 4 3 := by
  by_cases ho : L ⊔ (T : Subgroup G) = L
  · exact Or.inl (source_normal_ordinary_isPSU d hA312 hH hU hn ho)
  · exact Or.inr (source_normal_doubled_isPSL d hA312 hH hU hn ho)

theorem source_normal_modelConclusion : ModelConclusion G 5 :=
  Or.inl ⟨rfl,source13_5_17 d hA312 hH hU hn⟩

end CFSG.Quasithin.Chapter13.Section05.A5Source
