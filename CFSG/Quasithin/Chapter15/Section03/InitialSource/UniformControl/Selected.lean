module
public import CFSG.Quasithin.Chapter15.Section03.InitialSource.UniformControl.Source

/-!
# Source control of an actual ordering maximum when |Z|=2

The full14.1.12 producer selects its maximum from the original fixed pair.
When the central seed has order two, uniqueness identifies every actual
ordering maximum with that selected subgroup. Thus distinction from Mc
and the Baumann-normalizer bound require no separate premise.
Source: Aschbacher--Smith14.1.12(1),(4), printed pp.978--979.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.InitialSource.UniformControl
open ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

theorem source_controls_of_ordering_maximal
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hZ : Nat.card (centralInvolutions T) = 2) :
    Mc ≠ M ∧ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ M ∧
      (∀ N, IsOrderingMaximal T N → N = M) := by
  obtain ⟨D,hD,Mf,hMf,hne,hmax,hBaum,hdom,hoff,hall,hC⟩ :=
    source_lemma_14_1_12_selection hG T hempty hu hmany
  have hMfM : M = Mf := hall hZ M hM
  subst Mf
  exact ⟨Ne.symm hne,hBaum,hall hZ⟩

end CFSG.Quasithin.Chapter15.Section03.InitialSource.UniformControl
