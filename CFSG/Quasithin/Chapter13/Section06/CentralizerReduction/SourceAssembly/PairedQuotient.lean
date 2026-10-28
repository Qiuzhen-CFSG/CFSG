module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.PairedQuotient
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly.NonsolvableOutside

/-!
# The original Borel-join residual exclusion in the terminal A5 argument

The paired outside case now contradicts the exact source 13.2.13 assertion
that O²(H₀/O₃′(H₀)) is not a three-group. The checked original quotient
calculation supplies this contradiction without an extra paired centrality,
action, or commutator callback. The surviving actual quotient is S₃ and its
intrinsic residual quotient is C₃, so only the single-factor amalgam branch
is passed to the terminal source consumer.

This remains a conditional application, not a proof of 13.2.7. Independent
Baumann control, source 13.2.12--13, the single-factor argument, and the
nonsolvable generation bound remain with qt-d-1367-assembly. The existing
Context, 13.3.2, C.1.32 and 5.2.3 producers retain their source obligations;
qt-d-1361-source owns the final classification assembly.

Source: Aschbacher--Smith 13.2.13--14 and 13.2.7, printed pp.883--884.
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

/-- Apply the completed paired quotient calculation to every original source
Context required by the universal omega-centralizer consumer. -/
theorem terminal_model_of_borel_join_residual_exclusion
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
    (h1313 : ∀ (S : Sylow 2 G) (I W W₁ W₂ W₃ : Subgroup G),
      Context S I W W₁ W₂ W₃ →
      ∀ H ∈ Chapter3.HStar (S : Subgroup G) (normalizer (I : Set G)),
        ¬ H ≤ centralizer (omegaOneCenterAmbient (S : Subgroup G) : Set G) →
        Group.IsSolvable H →
        (H ⊔ borelResidual S I).pCoreIn 2 ≠ ⊥ →
        let J := H ⊔ borelResidual S I
        ¬ IsPGroup 3 (pResidual 2 (J ⧸ pPrimeCore 3 J)))
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
  have hquot := OriginalCentralization.single_quotients_of_non_three_borel_join
    e (normalizes_faithful_of_source1332 e h1332) hH hB hZ hs hcore
    (h1313 S I W W₁ W₂ W₃ e H hH hZ hs hcore)
  exact hZ (hsingle S I W W₁ W₂ W₃ e H hH hs hquot.1 hcore)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
