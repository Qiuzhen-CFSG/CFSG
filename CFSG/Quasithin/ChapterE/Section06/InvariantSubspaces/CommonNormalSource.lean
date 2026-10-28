module
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.Reduction
public import CFSG.Quasithin.Chapter3.Section01.CommonNormalSource
/-!
# The original E.6.13 common-normal input from C.5.8

The actual simple QTKE hypotheses in E.6.1 give the ambient domain of 3.1.1.
Its subgroup, residual-Sylow and relative-normality conventions agree
literally with CommonNormalInput. The centralizer consequence therefore
retains only the genuine earlier A.3.12 implication.
Source: Aschbacher–Smith E.6.13, printed p.250, and 3.1.1, pp.571–572.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces
universe u
variable {G : Type u} [Group G] [Finite G]

theorem source_commonNormalInput_of_A312 (T : Sylow 2 G)
    (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
      IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
      B ∈ ChapterA.Section03.localCComponents S → Chapter1.Section02.A312Conclusion B) : CommonNormalInput KnownSimple.IsKnownSimple T :=
  fun hG => Chapter3.source_common_normal_of_A312 hG hA312 T

theorem centralizer_le_of_normal_in_sylow_of_A312
    {T : Sylow 2 G} {M V W : Subgroup G}
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V)
    (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
      IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
      B ∈ ChapterA.Section03.localCComponents S → Chapter1.Section02.A312Conclusion B)
    (hne : W ≠ ⊥) (hWV : W ≤ V) (hodd : oddCentralizerCondition M V W)
    (hnormal : (W.subgroupOf (T : Subgroup G)).Normal) :
    centralizer (W : Set G) ≤ M :=
  centralizer_le_of_normal_in_sylow h (source_commonNormalInput_of_A312 T hA312)
    hne hWV hodd hnormal
end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces
