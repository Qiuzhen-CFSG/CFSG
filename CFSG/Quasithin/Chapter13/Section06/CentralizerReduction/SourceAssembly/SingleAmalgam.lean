module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.SingleAmalgam
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly.PairedQuotient

/-!
# The literal single-factor amalgam in the terminal A5 argument

The single S₃ branch has nontrivial Borel-join core: a trivial core would
force the paired quotient of order72. The actual Borel supplement and H
have S₃ two-core quotients and intersect in the original Sylow subgroup.
They therefore give a Goldschmidt triple in the SQTK join. Source13.2.13
excludes the collapsed quotient in F.6.11, preserving the original Sylow
intersection after quotienting by the prime-to-three core.

The terminal consumer now needs source13.2.12 only for the paired branch,
and passes the constructed original and quotient triples to the remaining
single-factor argument. This is conditional progress, not13.2.7: independent
Baumann control, the paired core argument,13.2.13, the nonsolvable generation
bound and the final amalgam exclusion remain with qt-d-1367-assembly.
The earlier Context,13.3.2,C.1.32 and5.2.3 producers retain their premises;
qt-d-1361-source owns final classification assembly.

Source: Aschbacher--Smith13.2.12--14 and the final13.2.7 argument, pp.881--884.
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

/-- Supply the actual single-factor amalgams, leaving the paired core
argument and the remaining source exclusions explicit. -/
theorem terminal_model_of_original_single_amalgam
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
    (hpairCore : ∀ (S : Sylow 2 G) (I W W₁ W₂ W₃ : Subgroup G),
      Context S I W W₁ W₂ W₃ →
      ∀ H ∈ Chapter3.HStar (S : Subgroup G) (normalizer (I : Set G)),
        ¬ H ≤ centralizer (omegaOneCenterAmbient (S : Subgroup G) : Set G) →
        Group.IsSolvable H →
        Nonempty ((H ⧸ pCore 2 H) ≃* WreathTwoResidual.Actor) →
        (H ⊔ borelResidual S I).pCoreIn 2 ≠ ⊥)
    (hsingle : ∀ (S : Sylow 2 G) (I W W₁ W₂ W₃ : Subgroup G),
      Context S I W W₁ W₂ W₃ →
      ∀ H ∈ Chapter3.HStar (S : Subgroup G) (normalizer (I : Set G)),
        ¬ H ≤ centralizer (omegaOneCenterAmbient (S : Subgroup G) : Set G) →
        let J := H ⊔ borelResidual S I
        let P := (borelResidual S I ⊔ (S : Subgroup G)).subgroupOf J
        let Q := H.subgroupOf J
        let q := QuotientGroup.mk' (pPrimeCore 3 J)
        IsSQTK KnownSimple.IsKnownSimple J →
        ChapterF.IsGoldschmidtTriple P Q →
        ChapterF.IsGoldschmidtTriple (P.map q) (Q.map q) →
        P.map q ⊓ Q.map q = ((S : Subgroup G).subgroupOf J).map q →
        pCore 2 (J ⧸ pPrimeCore 3 J) = ⊥ → False)
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
  apply terminal_model_of_borel_join_residual_exclusion d hc hmany h1332 hcontexts
    rankTwo h523 hBaumann ?_ ?_ h1313 hparameter
  · intro S I W W₁ W₂ W₃ e H hH hZ hs
    have hB := hBaumann S I W W₁ W₂ W₃ e
    rcases source_residual_core_quotient_models e hH hB hZ hs with h | h
    · obtain ⟨f⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
      exact OriginalCentralization.single_borel_join_core_ne_bot e hH hB hZ
        ⟨h.1.some.trans f⟩
    · exact hpairCore S I W W₁ W₂ W₃ e H hH hZ hs h.1
  · intro S I W W₁ W₂ W₃ e H hH hs he hcore
    by_contra hZ
    obtain ⟨f⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
    have he' := Nonempty.intro (he.some.trans f)
    have hB := hBaumann S I W W₁ W₂ W₃ e
    have hq := OriginalCentralization.single_borel_quotient_amalgam e hH hZ he'
      (h1313 S I W W₁ W₂ W₃ e H hH hZ hs hcore)
    exact hsingle S I W W₁ W₂ W₃ e H hH hZ
      (OriginalCentralization.single_borel_join_sqtk e hH hB hZ he')
      (OriginalCentralization.single_borel_goldschmidt_triple e hH hZ he')
      hq.2.1 hq.1 hq.2.2.1

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
