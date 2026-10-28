module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.PairedBorel
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly.NonsolvableOutside

/-!
# The paired Borel calculation in the terminal A5 source argument

The actual solvable quotient alternatives split the remaining outside branch.
For the paired alternative, the proved Borel calculation supplies centrality
of the full omega orbit, equality with the join orbit, and the commutator
bound in the literal two-core. These facts feed the remaining 13.2.13
contradiction, while the single-factor case retains the final Goldschmidt
argument. The original nonsolvable parameter branch is preserved.

This conditional application does not assert 13.2.7. Independent Baumann
control, source 13.2.12, the 13.2.13 contradiction, the single-factor argument,
and the nonsolvable parameter bound remain with qt-d-1367-assembly. Context,
13.3.2, C.1.32 and 5.2.3 retain their existing producers; qt-d-1361-source
owns final classification assembly.

Source: Aschbacher--Smith 13.2.12--14, pp.881--883, and 13.2.7, pp.883--884.
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

/-- The proved paired centrality calculation supplies the actual input to
its remaining contradiction in the universal terminal source application. -/
theorem terminal_model_of_borel_join_cases
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
    (hBaumann : ∀ (S : Sylow 2 G) (I W W₁ W₂ W₃ : Subgroup G),
      Context S I W W₁ W₂ W₃ →
        normalizer (ChapterB.baumann (S : Subgroup G) : Set G) ≤ normalizer (I : Set G))
    (hjoin : ∀ (S : Sylow 2 G) (I W W₁ W₂ W₃ : Subgroup G),
      Context S I W W₁ W₂ W₃ →
      ∀ H ∈ Chapter3.HStar (S : Subgroup G) (normalizer (I : Set G)),
        ¬ H ≤ centralizer (omegaOneCenterAmbient (S : Subgroup G) : Set G) →
        Group.IsSolvable H → (H ⊔ borelResidual S I).pCoreIn 2 ≠ ⊥)
    (hsingle : ∀ (S : Sylow 2 G) (I W W₁ W₂ W₃ : Subgroup G),
      Context S I W W₁ W₂ W₃ →
      ∀ H ∈ Chapter3.HStar (S : Subgroup G) (normalizer (I : Set G)),
        Group.IsSolvable H →
        Nonempty ((H ⧸ pCore 2 H) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) →
        (H ⊔ borelResidual S I).pCoreIn 2 ≠ ⊥ →
        H ≤ centralizer (omegaOneCenterAmbient (S : Subgroup G) : Set G))
    (hpaired : ∀ (S : Sylow 2 G) (I W W₁ W₂ W₃ : Subgroup G),
      Context S I W W₁ W₂ W₃ →
      ∀ H ∈ Chapter3.HStar (S : Subgroup G) (normalizer (I : Set G)),
        ¬ H ≤ centralizer (omegaOneCenterAmbient (S : Subgroup G) : Set G) →
        Group.IsSolvable H →
        Nonempty ((H ⧸ pCore 2 H) ≃* WreathTwoResidual.Actor) →
        (H ⊔ borelResidual S I).pCoreIn 2 ≠ ⊥ →
        borelResidual S I ≤ centralizer (omegaOrbit S H : Set G) →
        omegaOrbit S (H ⊔ borelResidual S I) = omegaOrbit S H →
        ⁅borelResidual S I,(pResidual 2 H).map H.subtype⁆ ≤
          ((pResidual 2 H).map H.subtype).pCoreIn 2 → False)
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
  apply terminal_model_of_solvable_outside_and_nonsolvable_parameter
    d hc hmany h1332 hcontexts rankTwo h523 ?_ hparameter
  intro S I W W₁ W₂ W₃ e H hH _ _ hs
  by_contra hZ
  have hB := hBaumann S I W W₁ W₂ W₃ e
  have hcore := hjoin S I W W₁ W₂ W₃ e H hH hZ hs
  rcases source_residual_core_quotient_models e hH hB hZ hs with ⟨hmodel,_⟩ | ⟨hmodel,_⟩
  · exact hZ (hsingle S I W W₁ W₂ W₃ e H hH hs hmodel hcore)
  · obtain ⟨hcentral,horbit,hcomm⟩ := OriginalCentralization.paired_borel_join_control
      e (normalizes_faithful_of_source1332 e h1332) hH hB hZ hs hmodel hcore
    exact hpaired S I W W₁ W₂ W₃ e H hH hZ hs hmodel hcore hcentral horbit hcomm

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
