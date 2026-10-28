module
public import CFSG.Quasithin.Chapter3.Section01.CommonNormalKnownSimple
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.Reduction

/-!
# The genuine common-normal source in E.6.13

The completed known-simple Theorem 3.1.1 uses exactly the ambient Sylow,
residual-Sylow and relative-normality conventions of `CommonNormalInput`.
Its direct application supplies the common-normal step in E.6.13 and hence
the invariant-subspace exclusion used in E.6.18.

Source: Aschbacher–Smith E.6.13, printed p.250, and 3.1.1, pp.571–572.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces
universe u
variable {G : Type u} [Group G] [Finite G]

theorem source_commonNormalInput_knownSimple (T : Sylow 2 G) :
    CommonNormalInput KnownSimple.IsKnownSimple T :=
  fun hG => Chapter3.source_common_normal_knownSimple hG T

/-- E.6.13 with the original common-normal theorem instantiated. -/
theorem centralizer_le_of_normal_in_sylow_knownSimple
    {T : Sylow 2 G} {M V W : Subgroup G}
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V)
    (hne : W ≠ ⊥) (hWV : W ≤ V) (hodd : oddCentralizerCondition M V W)
    (hnormal : (W.subgroupOf (T : Subgroup G)).Normal) :
    centralizer (W : Set G) ≤ M :=
  centralizer_le_of_normal_in_sylow h (source_commonNormalInput_knownSimple T)
    hne hWV hodd hnormal

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces
