module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.Nonsolvable
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly.OutsideBranches

/-!
# The actual nonsolvable outside branch in the terminal A5 consumer

The original 13.3.2 normalization premise applies to every faithful local
component by retaining the same ambient hypotheses. The nonsolvable outside
argument then supplies the actual maximal faithful residual, its A5 quotient,
and the equality of its omega-action kernel with O₂(H). Thus the remaining
numerical step can use these proved source facts. The solvable branch remains
the original Borel-join/amalgam argument.

This is a conditional application, not source 13.2.7 or 13.6.7. Both local
branches remain with qt-d-1367-assembly. The existing producers of Context,
13.3.2, C.1.32 and 5.2.3 retain their earlier inputs; qt-d-1361-source owns
final classification assembly. In particular, a quotient identification alone
does not prove the original generation-parameter lower bound.

Source: Aschbacher--Smith 13.2.8(1), p.880, and 13.6.7, p.928.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
open ComponentSelection ComponentElimination.SourceContainment.RankTwo.LocalApplication
open ComponentElimination.SourceSmallModels.OriginalAssembly.C132
open Section05.A5Source Section02.A5Outside
open TerminalContradiction.Components.SuzukiIsolation
open ChapterC Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original source normalization theorem applies to all faithful
components in the same Context, with no new ambient exclusions. -/
theorem normalizes_faithful_of_source1332
    {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
    (d : Context T L V V₁ V₂ V₃)
    (h1332 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter14.Section03.FaithfulSource.Hypothesis1331 S I →
        (S : Subgroup G) ≤ normalizer (I : Set G)) :
    ∀ K ∈ MainForward.faithfulLocalComponents T,
      (T : Subgroup G) ≤ normalizer (K : Set G) := by
  intro K hK
  exact h1332 T K { d.hypothesis with
    local_component := hK
    five_minimal := fun _ => d.uniform_A5 }

/-- Feed the proved nonsolvable residual and kernel data to the actual
Main-Theorem consumer. The two remaining local source arguments are explicit. -/
theorem terminal_model_of_solvable_outside_and_nonsolvable_parameter
    {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
    (d : Context T L V V₁ V₂ V₃)
    (hc : IsA5Counterexample G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (h1332 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter14.Section03.FaithfulSource.Hypothesis1331 S I →
        (S : Subgroup G) ≤ normalizer (I : Set G))
    (hcontexts : ∀ (S : Sylow 2 G) (I : Subgroup G), SourceHypothesis S I →
      ∃ W W₁ W₂ W₃ : Subgroup G, Nonempty (Context S I W W₁ W₂ W₃))
    (rankTwo : ∀ (J : Type u) [Group J] [Finite J] (B R : Subgroup J),
      SmallMSPair KnownSimple.IsKnownSimple B R → RankTwoAlternatives B R)
    (h523 : Source523.EarlierTheorem.{u} KnownSimple.IsKnownSimple)
    (hsolvable : ∀ (S : Sylow 2 G) (I W W₁ W₂ W₃ : Subgroup G),
      Context S I W W₁ W₂ W₃ →
      ∀ H ∈ Chapter3.HStar (S : Subgroup G) (normalizer (I : Set G)),
        ¬ elementaryAbelianMaxJ (S : Subgroup G) ≤ centralizer (W : Set G) →
        ChapterE.generationParameter H ≤ 1 → Group.IsSolvable H →
        H ≤ centralizer (omegaOneCenterAmbient (S : Subgroup G) : Set G))
    (hparameter : ∀ (S : Sylow 2 G) (I W W₁ W₂ W₃ : Subgroup G),
      Context S I W W₁ W₂ W₃ →
      ∀ H ∈ Chapter3.HStar (S : Subgroup G) (normalizer (I : Set G)),
        ¬ H ≤ centralizer (omegaOneCenterAmbient (S : Subgroup G) : Set G) →
        ¬ Group.IsSolvable H →
        (pResidual 2 H).map H.subtype ∈ MainForward.faithfulLocalComponents S →
        (pResidual 2 H).map H.subtype ∈ Chapter1.LStar G (S : Subgroup G) →
        Nonempty ((pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃*
          alternatingGroup (Fin 5)) →
        centralizer ((omegaOrbit S H).subgroupOf H : Set H) = pCore 2 H →
        1 < ChapterE.generationParameter H) :
    ClassificationModels.IsQTKEModel G := by
  apply terminal_model_of_low_generation_outside d hc hmany h1332 hcontexts rankTwo h523
  intro S I W W₁ W₂ W₃ e H hH hJ hlow
  by_contra hZ
  by_cases hs : Group.IsSolvable H
  · exact hZ (hsolvable S I W W₁ W₂ W₃ e H hH hJ hlow hs)
  · have hn := normalizes_faithful_of_source1332 e h1332
    obtain ⟨hfaith,hquot⟩ := OriginalCentralization.nonsolvable_residual_faithful_A5 e hn hH hZ hs
    have hmax := OriginalCentralization.nonsolvable_residual_mem_LStar e hn hH hZ hs
    have hker := OriginalCentralization.nonsolvable_omega_centralizer_eq_twoCore e hn hH hZ hs
    exact (not_lt_of_ge hlow)
      (hparameter S I W W₁ W₂ W₃ e H hH hZ hs hfaith hmax hquot hker)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
