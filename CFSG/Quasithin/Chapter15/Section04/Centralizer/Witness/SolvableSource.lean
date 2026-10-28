module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.SolvableOvergroup
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Witness.SourceCompletion

/-!
# The source centralizer conclusion from solvable maximal two-locals

The original 15.4.2(2) makes every maximal two-local over the selected Sylow
subgroup solvable. Sylow conjugacy gives this property for every Sylow
subgroup. The solvable Ξ embedding argument therefore supplies the full
universal 1.3.7 interface used by `SourceCompletion`, including its literal
normalizer and unique maximal-overgroup set.

The cubic quotient, nonempty normal-centralizer family, action control and
centralizer equality now retain only the earlier implications 15.4.2(1–3),
15.4.2(4) and C.2.6. All original groups, quotient maps and source hypotheses
are those of the existing completion theorems.

Source: Aschbacher–Smith 15.4.8–10, printed pp.1159–1160, using
15.4.2(2) and the solvable case of 1.3.7, pp.1157 and 512.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.CentralizerWitness.SolvableSource
open MaximalPrimeSource MaximalPrimeFive FamilySource CentralizerNormalClosureCubic
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original source solvability implication supplies 1.3.7 universally in G. -/
theorem earlier137_of_source (T : Sylow 2 G) (h : SourceHypotheses T)
    (h42 : Earlier1542 (G := G)) : SourceCompletion.Earlier137 (G := G) := by
  intro hG U Y hY
  exact Chapter1.XiEmbedding.normalizer_unique_of_solvable_maximalTwoLocals hG U
    (Chapter1.XiEmbedding.solvable_maximalTwoLocals_of_sylow T U (h42 T h).solvable)
    (Chapter1.XiStar_subset_Xi _ hY)

/-- Every member of the original normal-centralizer family has its literal cubic quotient. -/
theorem source_cubic_quotient (T : Sylow 2 G) (h : SourceHypotheses T)
    (h42 : Earlier1542 (G := G)) (h26 : EarlierC26.{u})
    (h44 : Earlier1542Four (G := G))
    {X : Subgroup G} (hX : X ∈ NormalCentralizerXi (T : Subgroup G)
      (Stellmacher.omegaOneCenterAmbient (T : Subgroup G))) :
    Nat.card (X ⧸ pCore 2 X) = 3 :=
  SourceCompletion.source_cubic_quotient T h h42 h26 h44 hX

/-- Source 15.4.9, preserving the original noncentralizer-equality hypothesis. -/
theorem source_lemma_15_4_9 (T : Sylow 2 G) (h : SourceHypotheses T)
    (h42 : Earlier1542 (G := G)) (h26 : EarlierC26.{u})
    (h44 : Earlier1542Four (G := G))
    (hne : centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G) ≠
      (T : Subgroup G)) :
    (NormalCentralizerXi (T : Subgroup G)
      (Stellmacher.omegaOneCenterAmbient (T : Subgroup G))).Nonempty :=
  SourceCompletion.source_lemma_15_4_9 T h h42 h26 h44 hne

/-- Source 15.4.10 with its uniqueness input discharged by solvable overgroups. -/
theorem source_lemma_15_4_10 (T : Sylow 2 G) (h : SourceHypotheses T)
    (h42 : Earlier1542 (G := G)) (h26 : EarlierC26.{u})
    (h44 : Earlier1542Four (G := G))
    {X M : Subgroup G}
    (hX : X ∈ NormalCentralizerXi (T : Subgroup G)
      (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)))
    (hM : IsMaximalTwoLocal M) (hXM : X ⊔ (T : Subgroup G) ≤ M) :
    X ≤ M ⊓ centralizer (localV (T : Subgroup G) M : Set G) :=
  SourceCompletion.source_lemma_15_4_10 T h h42 h26 h44
    (earlier137_of_source T h h42) hX hM hXM

/-- The source centralizer equality requires no separate universal 1.3.7 premise. -/
theorem source_lemma_15_4_8 (T : Sylow 2 G) (h : SourceHypotheses T)
    (h42 : Earlier1542 (G := G)) (h26 : EarlierC26.{u})
    (h44 : Earlier1542Four (G := G)) :
    centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G) =
      (T : Subgroup G) :=
  SourceCompletion.source_lemma_15_4_8 T h h42 h26 h44 (earlier137_of_source T h h42)

end CFSG.Quasithin.Chapter15.Section04.CentralizerWitness.SolvableSource
