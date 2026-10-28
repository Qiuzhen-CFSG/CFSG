module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootCore.Decomposition
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootSecondary
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootFF.Complete
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRecognitionComplete

/-!
# Completion of the ordinary-component exclusion

The intrinsic long-root calculation supplies the root-normalizer span, its
reducedness and the root-core decomposition. The actual secondary component
of the root centralizer then satisfies every premise of the completed FF
comparison. Its two subgroup conclusions give the terminal contradiction,
without identifying the secondary component with the point-local residual
before that argument.

The original ordinary hypotheses supply the simultaneous symplectic marking,
so no marking, root-core, secondary-component or classification premise remains.
The source component dichotomy finally gives the literal conclusion
F*(K) = O₂(K).

Source: Aschbacher–Smith 4.3.6, printed pp.614–615.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.SourceConfiguration
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The marked root-normalizer contradiction, with all core and FF premises proved. -/
theorem ordinary_false_of_marking (c : SourceConfiguration T L)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {n : ℕ} (hn : 1 < n) (m : OrdinarySymplecticMarking c n) : False := by
  obtain ⟨KZ, hK, hcomp, _, hquasi, hnormal, hKZ⟩ :=
    m.exists_secondary_component hn h.simpleQTKE
  exact OrdinaryRootFF.false_of_core_and_secondary m D hn h
    (m.rootSpan_isPReduced hn D h) (m.rootSpan_le_rootNormalizer hn)
    (m.second_core_le_rootSpan hn) (m.sylow_le_rootNormalizer hn D)
    (m.fullModule_conjugateSpan_second hn) (m.rootCore_decomposition hn D h)
    KZ hK hcomp hKZ hquasi hnormal

/-- Original 4.3.6 excludes an ordinary component using the constructed marking. -/
theorem false_of_ordinary (c : SourceConfiguration T L)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (ho : IsComponent c.H c.K) : False := by
  obtain ⟨m⟩ := c.ordinarySymplecticMarking D ho hn hpsl
  exact c.ordinary_false_of_marking D h hn m

/-- The literal conclusion of original 4.3.6 for the source configuration. -/
theorem generalizedFitting_eq_pCore (c : SourceConfiguration T L)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) :
    generalizedFitting c.K = pCore 2 c.K :=
  c.component_cases.resolve_left (c.false_of_ordinary D h hn hpsl)

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.SourceConfiguration
