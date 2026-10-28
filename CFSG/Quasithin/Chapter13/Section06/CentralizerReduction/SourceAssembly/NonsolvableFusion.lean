module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.NonsolvableFusion
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly.NonsolvableOneBlock

/-!
# Full omega-center fusion in the surviving original nonsolvable branch

The surviving original outside pair has Sylow omega-center of order four.
The independent Baumann bound puts the Sylow normalizer in N_G(L), so it
preserves the nontrivial fixed line in the original omega splitting.
Its action on the full four-group is trivial. Burnside fusion then shows
that distinct elements of this omega-center are not G-conjugate.

The universal application retains the multiple-overgroup guard through
every original Sylow/component rechoice. These are necessary constraints
on the remaining opposite-normalizer case; they do not yet supply the
residual four-group lift or prove unrestricted n(H)>1. Earlier-source
discharge and full 13.2.7/13.6.7 assembly remain with their original owners.
Source: Aschbacher--Smith 13.2.4(2b), 13.2.8(1), printed pp.879--880.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
open Subgroup Theory.GroupTheory Stellmacher
open Section05.A5Source Section02.A5Outside
open Section02.A5Outside.OriginalCentralization ChapterB ChapterC
open ComponentElimination.SourceContainment.RankTwo.LocalApplication
open TerminalContradiction.Components.SuzukiIsolation
universe u
variable {G : Type u} [Group G] [Finite G]

theorem original_nonsolvable_normalizer_centralizes_omega
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Context T L V V₁ V₂ V₃) (hc : IsA5Counterexample G)
    (hno : ¬ ClassificationModels.IsQTKEModel G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (h1332 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter14.Section03.FaithfulSource.Hypothesis1331 S I →
        (S : Subgroup G) ≤ normalizer (I : Set G))
    (hcontexts : ∀ (S : Sylow 2 G) (I : Subgroup G), SourceHypothesis S I →
      ∃ W W₁ W₂ W₃ : Subgroup G, Nonempty (Context S I W W₁ W₂ W₃))
    (h523 : Source523.EarlierTheorem.{u} KnownSimple.IsKnownSimple)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : ¬ Group.IsSolvable H) :
    normalizer ((T : Subgroup G) : Set G) ≤
      centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) := by
  obtain ⟨D,hfour,-⟩ :=
    original_nonsolvable_opposite_baumann d hc hno hmany h1332 hcontexts h523 hH hZ hs
  exact normalizer_centralizes_omega_of_four d
    (thompson_moves_of_omega_movement d hH hZ)
    ((normalizer_le_normalizer_baumann (T : Subgroup G)).trans
      (baumann_normalizer_of_many d hmany))
    (original_nonsolvable_center_bounds d hc hmany h1332 hcontexts hH hZ hs).2.1 hfour

theorem original_nonsolvable_omega_isConj_iff_eq
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Context T L V V₁ V₂ V₃) (hc : IsA5Counterexample G)
    (hno : ¬ ClassificationModels.IsQTKEModel G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (h1332 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter14.Section03.FaithfulSource.Hypothesis1331 S I →
        (S : Subgroup G) ≤ normalizer (I : Set G))
    (hcontexts : ∀ (S : Sylow 2 G) (I : Subgroup G), SourceHypothesis S I →
      ∃ W W₁ W₂ W₃ : Subgroup G, Nonempty (Context S I W W₁ W₂ W₃))
    (h523 : Source523.EarlierTheorem.{u} KnownSimple.IsKnownSimple)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : ¬ Group.IsSolvable H)
    {x y : G} (hx : x ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hy : y ∈ omegaOneCenterAmbient (T : Subgroup G)) : IsConj x y ↔ x = y :=
  omega_isConj_iff_eq_of_normalizer_centralizes
    (original_nonsolvable_normalizer_centralizes_omega d hc hno hmany
      h1332 hcontexts h523 hH hZ hs) hx hy

theorem universal_original_nonsolvable_omega_fusion
    (T : Sylow 2 G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : IsA5Counterexample G) (hno : ¬ ClassificationModels.IsQTKEModel G)
    (h1332 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter14.Section03.FaithfulSource.Hypothesis1331 S I →
        (S : Subgroup G) ≤ normalizer (I : Set G))
    (hcontexts : ∀ (S : Sylow 2 G) (I : Subgroup G), SourceHypothesis S I →
      ∃ W W₁ W₂ W₃ : Subgroup G, Nonempty (Context S I W W₁ W₂ W₃))
    (h523 : Source523.EarlierTheorem.{u} KnownSimple.IsKnownSimple)
    (S : Sylow 2 G) (I : Subgroup G) (standing : SourceHypothesis S I)
    (H : Subgroup G)
    (hH : H ∈ Chapter3.HStar (S : Subgroup G) (normalizer (I : Set G)))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (S : Subgroup G) : Set G))
    (hs : ¬ Group.IsSolvable H) :
    normalizer ((S : Subgroup G) : Set G) ≤
        centralizer (omegaOneCenterAmbient (S : Subgroup G) : Set G) ∧
      ∀ x ∈ omegaOneCenterAmbient (S : Subgroup G),
        ∀ y ∈ omegaOneCenterAmbient (S : Subgroup G), IsConj x y ↔ x = y := by
  obtain ⟨V,V₁,V₂,V₃,⟨d⟩⟩ := hcontexts S I standing
  have hmanyS : 1 < (maximalTwoLocalOvergroups (S : Subgroup G)).ncard := by
    rwa [maximalTwoLocalOvergroups_ncard_sylow S T]
  have hn := original_nonsolvable_normalizer_centralizes_omega d hc hno hmanyS
    h1332 hcontexts h523 hH hZ hs
  exact ⟨hn, fun _ hx _ hy => omega_isConj_iff_eq_of_normalizer_centralizes hn hx hy⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
