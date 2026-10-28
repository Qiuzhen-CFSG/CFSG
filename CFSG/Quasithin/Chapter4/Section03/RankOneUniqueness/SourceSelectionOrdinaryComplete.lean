module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.SourceSelectionOrdinaryRootFF.Comparison
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalLocalUniquenessRoot

/-!
# Completing source selection before ordinary full-normalizer identification

The secondary component and the complete FF action comparison give the two
terminal identities on the original root span and root-normalizer core.
Normal generation then forces the secondary component to equal the second
residual, contradicting the previously proved failure of T-normalization.
Thus the raw ordinary branch is impossible. This proves its full-normalizer
obligation and completes the aligned SourceConfiguration constructor.

The separate nonblock exclusion remains with its existing source producer;
uniqueness below is conditional only on that exclusion. The final owner is
qt-d-1222-rankone-global-uniqueness, with the nonbinary C.1.34 input retained
at qt-c134-nonbinary-linear-three-source. Neither conditional uniqueness nor
source selection alone is the unconditional theorem 4.3.2.
Source: Aschbacher–Smith 4.3.2–6, printed pp.613–615.
-/

public section
open Subgroup Theory.GroupTheory ClassicalGroup
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
open Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The actual secondary component satisfies both terminal comparison identities,
without requiring the full normalizer of the original ordinary component. -/
theorem OutsideSymplecticMarking.root_comparison
    {c : OutsideChoice T L} {K : Subgroup c.H} {n : ℕ}
    (m : OutsideSymplecticMarking c K n)
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hn : 1 < n) :
    ∃ KZ : Subgroup G,
      m.rootSpan = m.second.pCoreIn 2 ∧
      conjugateSpanBy m.second KZ = KZ ∧
      KZ ≤ m.second ⊔ m.rootNormalizer.pCoreIn 2 ∧
      m.rootNormalizer ≤ normalizer (KZ : Set G) := by
  obtain ⟨KZ,hK,hcomp,_,hquasi,hnormal,hgen⟩ :=
    m.exists_secondary_component hn h.simpleQTKE
  obtain ⟨hU,hle⟩ := OutsideRootFF.module_and_containment m hn h
    (m.rootSpan_isPReduced hn D h) (m.rootSpan_le_rootNormalizer hn)
    (m.second_core_le_rootSpan hn) (m.fullModule_conjugateSpan_second hn)
    (m.rootCore_decomposition hn D h) KZ hK hcomp hgen hquasi hnormal
  exact ⟨KZ,hU,hgen,hle,hnormal⟩

/-- The ordinary contradiction at the original outside-choice boundary.
All marking, secondary-component, core and FF premises are constructed. -/
theorem OutsideChoice.ordinary_false
    (c : OutsideChoice T L)
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {n : ℕ} (hn : 1 < n) (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (K : Subgroup c.H) (ho : IsComponent c.H K)
    (hLK : L ≤ K.map c.H.subtype)
    (hout : ¬ K.map c.H.subtype ≤ normalizer (L : Set G))
    (hKN : K.Normal) : False := by
  obtain ⟨m⟩ := c.ordinarySymplecticMarking D h.toHypothesis1221 hn hpsl K ho hLK hout hKN
  obtain ⟨KZ,hU,hgen,hle,hnormal⟩ := m.root_comparison D h hn
  exact m.false_of_root_comparison D h.toHypothesis1221 hn hpsl ho hout hKN
    KZ hU (m.rootCore_decomposition hn D h) hgen hle hnormal

/-- The outstanding ordinary full-normalizer input is discharged by excluding
that branch before invoking the constructor that requires this equality. -/
theorem OutsideChoice.ordinary_normalizer
    (c : OutsideChoice T L)
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {n : ℕ} (hn : 1 < n) (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (K : Subgroup c.H) (ho : IsComponent c.H K)
    (hLK : L ≤ K.map c.H.subtype)
    (hout : ¬ K.map c.H.subtype ≤ normalizer (L : Set G))
    (hKN : K.Normal) : c.H = normalizer (K.map c.H.subtype : Set G) :=
  (c.ordinary_false D h hn hpsl K ho hLK hout hKN).elim

/-- Construct the aligned source configuration from failure of uniqueness over
L itself. Both containing-component quotient and ordinary normalizer inputs
are proved, preserving the original T and full module. -/
theorem exists_sourceConfiguration
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {n : ℕ} (hn : 1 < n) (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hnot : ¬ UniqueMaximalOvergroup L (normalizer (L : Set G))) :
    Nonempty (SourceConfiguration T L) :=
  exists_sourceConfiguration_of_ordinary_normalizer D h.toHypothesis1221 hpsl
    (fun c K ho hLK hout hKN => c.ordinary_normalizer D h hn hpsl K ho hLK hout hKN) hnot

/-- The literal uniqueness statement over L with source selection, ordinary and
block branches discharged. The independent nonblock branch remains explicit. -/
theorem uniqueness_of_nonblock_exclusion
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n) (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hnonblock : ∀ c : SourceConfiguration T L,
      generalizedFitting c.K = pCore 2 c.K → ¬ ChapterC.IsBlock c.K → False) :
    ∀ X : Subgroup G, IsMaximalTwoLocal X → L ≤ X → X = normalizer (L : Set G) :=
  uniqueness_of_selection_and_nonblock_exclusion D h hmany hn hpsl
    (exists_sourceConfiguration D h hn hpsl) hnonblock

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
