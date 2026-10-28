module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.SourceSelectionOrdinaryRootCore
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootConsumer
public import Theory.GroupTheory.ConjugateSpanFixedFactor

/-!
# Source selection through the original ordinary root comparison

The constructed raw-choice marking and root-core decomposition let the
terminal normal-generation calculation precede full-normalizer identification.
Once the actual span equals O₂(K₂) and the secondary component lies in K₂Q_Z,
normal generation gives K_Z = K₂, contradicting T not≤ N_G(K₂).

The source constructor and literal Chapter 12 application retain the remaining
secondary/FF comparison explicitly. It is still owned by
qt-d-1222-rankone-global-uniqueness; this conditional adapter does not prove
unconditional 4.3.2. The nonblock exclusion remains with
qt-d-1222-rankone-uniqueness-nonblock and qt-c134-nonbinary-linear-three-source.
The independent right factor stays with the final preparation owner.
No existing dependency is discharged by this conditional route.
Source: Aschbacher–Smith 4.3.2–6, pp.613–615, and 12.2, p.795.
-/

public section
open Subgroup Theory.GroupTheory ClassicalGroup
open Theory.SpecificGroups.SymplecticFour
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
namespace OutsideSymplecticMarking
variable {c : OutsideChoice T L} {K : Subgroup c.H} {n : ℕ}

/-- The literal terminal comparison can be applied before normalizer
identification. The remaining comparison identities concern the actual
root-normalizer core and secondary component, rather than N_G(K). -/
theorem false_of_root_comparison (m : OutsideSymplecticMarking c K n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hn : 1 < n) (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (ho : IsComponent c.H K)
    (hout : ¬ K.map c.H.subtype ≤ normalizer (L : Set G)) (hKN : K.Normal)
    (KZ : Subgroup G)
    (hU : m.rootSpan = m.second.pCoreIn 2)
    (hQ : m.rootNormalizer.pCoreIn 2 = m.second.pCoreIn 2 ⊔
      (m.rootNormalizer.pCoreIn 2 ⊓ centralizer (c.ordinaryModule : Set G)))
    (hKZ : conjugateSpanBy m.second KZ = KZ)
    (himage : KZ ≤ m.second ⊔ m.rootNormalizer.pCoreIn 2)
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G)) : False := by
  let J := m.second
  let Q := m.rootNormalizer.pCoreIn 2
  let U := J.pCoreIn 2
  have hJN : J ≤ m.rootNormalizer := (map_subtype_le _).trans inf_le_right
  have hJQ : J ≤ normalizer (Q : Set G) := hJN.trans
    (m.rootNormalizer.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  have hJgen : conjugateSpanBy c.ordinaryModule J = J := m.fullModule_conjugateSpan_second hn
  have hQJ : Q ≤ normalizer (J : Set G) := by
    have hJU : J ≤ normalizer (U : Set G) := J.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image J (pCore 2 J))
    have hNU : m.rootNormalizer ≤ normalizer (U : Set G) := by
      rw [show U = m.rootSpan from hU.symm]
      exact le_normalizer_conjugateSpanBy _ _
    exact normalizes_of_fixed_factor_and_conjugate_generation
      c.ordinaryModule J Q U hJU hJQ ((pCoreIn_le 2 _).trans hNU)
      (pCoreIn_le 2 J) hQ hJgen
  have hKJ : KZ ≤ normalizer (J : Set G) := himage.trans (sup_le J.le_normalizer hQJ)
  have he : KZ = J := le_antisymm
    (hKZ ▸ conjugateSpanBy_le le_rfl hKJ)
    ((le_conjugateSpanBy _ _).trans_eq hKZ)
  exact m.second_not_normalized D h hn hpsl ho hout hKN
    (show (T : Subgroup G) ≤ normalizer (J : Set G) by
      rw [←he]
      exact (m.sylow_le_rootNormalizer hn D).trans hnormal)
end OutsideSymplecticMarking
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
open Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The normalizer prerequisite is replaced by the literal root comparison
in the raw ordinary choice. This is conditional source selection: its root
comparison is still discharged by the global uniqueness owner. -/
theorem exists_sourceConfiguration_of_ordinary_root_comparison
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {n : ℕ} (hn : 1 < n) (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hcompare : ∀ (c : OutsideChoice T L) (K : Subgroup c.H),
      IsComponent c.H K → L ≤ K.map c.H.subtype →
      ¬ K.map c.H.subtype ≤ normalizer (L : Set G) → K.Normal →
      ∀ m : OutsideSymplecticMarking c K n,
      ∃ KZ : Subgroup G,
        m.rootSpan = m.second.pCoreIn 2 ∧
        conjugateSpanBy m.second KZ = KZ ∧
        KZ ≤ m.second ⊔ m.rootNormalizer.pCoreIn 2 ∧
        m.rootNormalizer ≤ normalizer (KZ : Set G))
    (hnot : ¬ UniqueMaximalOvergroup L (normalizer (L : Set G))) :
    Nonempty (SourceConfiguration T L) := by
  apply exists_sourceConfiguration_of_ordinary_normalizer D h.toHypothesis1221 hpsl ?_ hnot
  intro c K ho hLK hout hKN
  obtain ⟨m⟩ := c.ordinarySymplecticMarking D h.toHypothesis1221 hn hpsl K ho hLK hout hKN
  obtain ⟨KZ,hU,hgen,himage,hnormal⟩ := hcompare c K ho hLK hout hKN m
  exact (m.false_of_root_comparison D h.toHypothesis1221 hn hpsl ho hout hKN
    KZ hU (m.rootCore_decomposition hn D h) hgen himage hnormal).elim

/-- The original uniqueness over L, conditional only on the earlier-boundary
root comparison and the independently owned nonblock exclusion. -/
theorem uniqueness_of_ordinary_root_comparison_and_nonblock_exclusion
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n) (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hcompare : ∀ (c : OutsideChoice T L) (K : Subgroup c.H),
      IsComponent c.H K → L ≤ K.map c.H.subtype →
      ¬ K.map c.H.subtype ≤ normalizer (L : Set G) → K.Normal →
      ∀ m : OutsideSymplecticMarking c K n,
      ∃ KZ : Subgroup G,
        m.rootSpan = m.second.pCoreIn 2 ∧
        conjugateSpanBy m.second KZ = KZ ∧
        KZ ≤ m.second ⊔ m.rootNormalizer.pCoreIn 2 ∧
        m.rootNormalizer ≤ normalizer (KZ : Set G))
    (hnonblock : ∀ c : SourceConfiguration T L,
      generalizedFitting c.K = pCore 2 c.K → ¬ ChapterC.IsBlock c.K → False) :
    ∀ X : Subgroup G, IsMaximalTwoLocal X → L ≤ X → X = normalizer (L : Set G) :=
  uniqueness_of_selection_and_nonblock_exclusion D h hmany hn hpsl
    (exists_sourceConfiguration_of_ordinary_root_comparison D h hn hpsl hcompare) hnonblock
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter4.Section03.RankOneUniqueness
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}

/-- Literal Chapter 12 application of the raw-choice root comparison.
The root inputs remain with this uniqueness owner, nonblock with its existing
producer, and the independent right factor with the final preparation owner. -/
theorem rankOne_global_preparation_of_ordinary_root_comparison_and_nonblock_exclusion
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n) (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hcompare : ∀ (c : OutsideChoice T L) (K : Subgroup c.H),
      IsComponent c.H K → L ≤ K.map c.H.subtype →
      ¬ K.map c.H.subtype ≤ normalizer (L : Set G) → K.Normal →
      ∀ m : OutsideSymplecticMarking c K n,
      ∃ KZ : Subgroup G,
        m.rootSpan = m.second.pCoreIn 2 ∧
        conjugateSpanBy m.second KZ = KZ ∧
        KZ ≤ m.second ⊔ m.rootNormalizer.pCoreIn 2 ∧
        m.rootNormalizer ≤ normalizer (KZ : Set G))
    (hnonblock : ∀ c : SourceConfiguration T L,
      generalizedFitting c.K = pCore 2 c.K → ¬ ChapterC.IsBlock c.K → False)
    (hright : ∀ A B : Subgroup G, CartanPair T L H A B →
      ∃ L₂ : Subgroup G, Global.RightFactor T L H A B L₂) :
    ∃ A B L₂ : Subgroup G, Global.Preparation T L H A B L₂ :=
  D.rankOne_global_preparation_of_selection_and_nonblock_exclusion h hmany hn hpsl
    hH hgen hN (exists_sourceConfiguration_of_ordinary_root_comparison D h hn hpsl hcompare)
    hnonblock hright
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
