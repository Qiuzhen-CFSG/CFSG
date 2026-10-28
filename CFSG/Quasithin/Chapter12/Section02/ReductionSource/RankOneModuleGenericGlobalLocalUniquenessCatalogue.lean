module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.SourceSelectionOrdinarySporadic
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootConsumer

/-!+# The symplectic ordinary remainder in global source selection

The original OutsideChoice now has a genuine nonbinary symplectic central
quotient whenever its escaping containing component is ordinary. Thus only
that case remains in the full-normalizer premise of the source constructor.
The actual quotient proof for constrained components, the ordinary exclusion
after configuration selection, and the block exclusion are already discharged.

The literal Chapter 12 application below retains the symplectic normalizer,
the independent nonblock exclusion, and the independent right-factor input.
The normalizer and final source selection remain with
qt-d-1222-rankone-global-uniqueness. The nonblock branch remains with
qt-d-1222-rankone-uniqueness-nonblock and its nonbinary source producer.
These conditional consumers do not assert the unconditional theorem 4.3.2.

Source: Aschbacher–Smith 4.3.2–7, pp.613–616, and 12.2, p.795.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
open Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- All nonsymplectic ordinary cases are discharged in the aligned constructor.
The remaining normalizer input concerns the original H and K, with an actual
nonbinary symplectic central quotient, not an unrelated model tag. -/
theorem exists_sourceConfiguration_of_symplectic_normalizer
    (D : ChosenModule T L V) (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hnormalizer : ∀ (c : OutsideChoice T L) (K : Subgroup c.H),
      IsComponent c.H K → L ≤ K.map c.H.subtype →
      ¬ K.map c.H.subtype ≤ normalizer (L : Set G) → K.Normal →
      ∀ m : ℕ, 1 < m → ClassicalGroup.IsPSp (K ⧸ center K) 2 (2 ^ m) →
      c.H = normalizer (K.map c.H.subtype : Set G))
    (hnot : ¬ UniqueMaximalOvergroup L (normalizer (L : Set G))) :
    Nonempty (SourceConfiguration T L) := by
  apply exists_sourceConfiguration_of_ordinary_normalizer D h hpsl ?_ hnot
  intro c K ho hLK hout hKN
  obtain ⟨m,hm,hrow⟩ := c.ordinary_symplectic_quotient D h K ho hLK hout hKN hn hpsl
  exact hnormalizer c K ho hLK hout hKN m hm hrow

/-- Actual uniqueness over L from the remaining symplectic normalizer case
and the independently owned nonblock source exclusion. -/
theorem uniqueness_of_symplectic_normalizer_and_nonblock_exclusion
    (D : ChosenModule T L V)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hnormalizer : ∀ (c : OutsideChoice T L) (K : Subgroup c.H),
      IsComponent c.H K → L ≤ K.map c.H.subtype →
      ¬ K.map c.H.subtype ≤ normalizer (L : Set G) → K.Normal →
      ∀ m : ℕ, 1 < m → ClassicalGroup.IsPSp (K ⧸ center K) 2 (2 ^ m) →
      c.H = normalizer (K.map c.H.subtype : Set G))
    (hnonblock : ∀ c : SourceConfiguration T L,
      generalizedFitting c.K = pCore 2 c.K → ¬ ChapterC.IsBlock c.K → False) :
    ∀ X : Subgroup G, IsMaximalTwoLocal X → L ≤ X → X = normalizer (L : Set G) :=
  uniqueness_of_selection_and_nonblock_exclusion D h hmany hn hpsl
    (exists_sourceConfiguration_of_symplectic_normalizer D h.toHypothesis1221 hn hpsl hnormalizer)
    hnonblock

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter4.Section03.RankOneUniqueness
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}

/-- Literal preparation application with every nonsymplectic ordinary source
case discharged. The right factor remains with its independent producer. -/
theorem rankOne_global_preparation_of_symplectic_normalizer_and_nonblock_exclusion
    (D : ChosenModule T L V)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hnormalizer : ∀ (c : OutsideChoice T L) (K : Subgroup c.H),
      IsComponent c.H K → L ≤ K.map c.H.subtype →
      ¬ K.map c.H.subtype ≤ normalizer (L : Set G) → K.Normal →
      ∀ m : ℕ, 1 < m → ClassicalGroup.IsPSp (K ⧸ center K) 2 (2 ^ m) →
      c.H = normalizer (K.map c.H.subtype : Set G))
    (hnonblock : ∀ c : SourceConfiguration T L,
      generalizedFitting c.K = pCore 2 c.K → ¬ ChapterC.IsBlock c.K → False)
    (hright : ∀ A B : Subgroup G, CartanPair T L H A B →
      ∃ L₂ : Subgroup G, Global.RightFactor T L H A B L₂) :
    ∃ A B L₂ : Subgroup G, Global.Preparation T L H A B L₂ :=
  D.rankOne_global_preparation_of_selection_and_nonblock_exclusion h hmany hn hpsl
    hH hgen hN
    (exists_sourceConfiguration_of_symplectic_normalizer D h.toHypothesis1221 hn hpsl hnormalizer)
    hnonblock hright

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
