module
public import CFSG.Quasithin.Chapter15.Section03.InitialSource.AlternatingThree
public import CFSG.Quasithin.Chapter13.Section09.Source

/-!
# Applying the proved wreath exclusion at the original source boundary

The genuine 13.9.1 theorem is applied to the literal original configuration.
Its callback is therefore discharged; the earlier public theorem and its
original subgroup, Sylow and module hypotheses are preserved.

Source: Aschbacher--Smith 13.9.1, 14.1.10 and 15.3--15.4.25.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section03.InitialSource
universe u
variable {G : Type u} [Group G] [Finite G]

theorem alternating_three_excluded_from_source
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {M Mc : Subgroup G}
    (hM : M ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (X R : Subgroup M) (hb : ChapterC.IsBlock X)
    (hQR : pCore 2 M ≤ R) (hRT : R ≤ (T.subtype hM.2 : Subgroup M))
    (hm : X = ⁅X,elementaryAbelianMaxJ R⁆)
    (haway : M ≠ Mc ∨ Nat.card (centralInvolutions T) = 2) :
    ¬ ChapterC.IsAlternatingBlock X 3 := by
  exact alternating_three_excluded (fun _ _ _ h d => Chapter13.Section09.source13_9_1 h d) hG T hM hu hmany X R hb hQR hRT hm haway

end CFSG.Quasithin.Chapter15.Section03.InitialSource
