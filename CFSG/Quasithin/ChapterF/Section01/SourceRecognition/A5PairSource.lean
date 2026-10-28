module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairCatalogue.Sieve
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairCatalogue.G2

/-!
# Original A5-pair core control from the full reduced catalogue

For the original F.1.1 pair, the two A5 quotient markings exclude every
exceptional and binary clause. The twisted regular rows are excluded by
their actual Borel indices and quotient orders, using quasithinness only
of the generated subgroup. In the three surviving ordinary rows, reduced
core and residual transport constructs the original factor markings;
the native automorphism calculations give both original join-core
equalities. A single normalized original Borel then gives both Sylow
containments.

This proves the complete reduced-catalogue implication, without original
perfectness, splitting, original markings or a kernel-control premise.
Existence of the reduced catalogue remains the genuine earlier source
obligation owned by qt-dgs85-source-assembly; the unconditional A5-pair
and Chapter10 tensor assembly remain with qt-d-tensor-a5-amalgam.

Source: Aschbacher–Smith F.1.12, pp.262–264, especially the original
core equality and one-normalized-Borel argument on p.264; DGS Theorem A
and (15.2)–(15.3), pp.99–100 and 226–231.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source

/-- The full genuine reduced catalogue gives BOTH original join-core
equalities and containments, under the unchanged original A5-pair hypotheses. -/
theorem a5_pair_core_and_containment_of_reduced_catalogue
    {G : Type*} [Group G] [Finite G] {K R S : Subgroup G}
    (h : HypothesisF11 ![K,R] S)
    (hqt : IsQuasithin (generated ![K,R] S))
    (a : ∀ i, Nonempty ((![K,R] i ⧸ pCore 2 (![K,R] i)) ≃* alternatingGroup (Fin 5)))
    (hnorm : ∃ j, borel (![K,R] j) S ≤ normalizer (S : Set G))
    (ha : Chapter6.Source.RankOneGeneric.Global.OriginalExtension.ReducedAlternatives K R S) :
    (∀ i, twoCore (![K,R] i ⊔ S) = twoCore (![K,R] i)) ∧
      (∀ i, S ≤ ![K,R] i) := by
  rcases A5PairCatalogue.core_and_containment_or_g2 h hqt a hnorm ha with hc | hg
  · exact hc
  · obtain ⟨F, _, _, _, b, e⟩ := hg
    exact A5PairCatalogue.G2.core_and_containment F h a hnorm b e.some

end CFSG.Quasithin.ChapterF.Source
