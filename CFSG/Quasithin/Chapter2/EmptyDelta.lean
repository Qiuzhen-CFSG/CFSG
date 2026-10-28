module

public import CFSG.Quasithin.Chapter2.Section01To03.Bender.GoodCentralizers.NativeZD
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete

/-!
# The empty-delta branch of Theorem 2.1.1

The simultaneous A/B/C theorem for the full known-simple catalogue discharges
the last earlier-source premise of the Bender recognition argument. The
conclusion is the literal model predicate used by the forward classification.

Source: Aschbacher--Smith, Theorem 2.1.1 and Section 2.2, printed pp.518--523.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.BenderFusion
universe u

/-- The empty-delta case of 2.1.1, with all earlier source inputs proved. -/
theorem theorem_2_1_1_of_delta_empty
    {G : Type u} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (M : Subgroup G)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hdelta : delta (Chapter1.He G) M = ∅) :
    ClassificationModels.IsTheorem211Model G :=
  theorem_2_1_1_of_delta_empty_and_theoremsABC hG
    (fun X _ _ => ChapterA.Section02.theoremsABC_knownSimple (G := X))
    T M hM hTM hunique hdelta

end CFSG.Quasithin.Chapter2.BenderFusion
