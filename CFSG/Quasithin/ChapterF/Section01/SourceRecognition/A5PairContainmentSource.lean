module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairBTwoG2Source
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairOriginalReduction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairCatalogue.G2

/-!
# Original A5-pair containment from the genuine source

Choose the actual critical pair in the original F.1.1 graph. The source
excludes commuting critical pairs, and the intrinsic distance-one comparison
already controls both original joins. In the remaining distance-two case,
the source constructs the full Cartan, natural smaller actors, reflections,
apartment exchange and root signs. The two original field-four markings
then yield the actual native G2 reduced amalgam. Native restoration controls
the original quotient-action kernels and proves both join-core equalities.
One normalized original Borel consequently puts S in both original factors.

No critical pair, natural module, exchange, reduced catalogue, original
marking, perfectness or kernel-control premise is supplied. The actual
whole Borel and both original factor inclusions are retained throughout.
Source: DGS, Groups and Graphs (1985), Theorem A and (14.9)–(15.3);
Aschbacher–Smith F.1.12, pp.262–264.
-/

public noncomputable section
open Subgroup Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.Source
open _root_.CFSG.Quasithin.ChapterF.Source.DGS85
open _root_.CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
variable {G : Type*} [Group G] [Finite G] {K R S : Subgroup G}

/-- The genuine distance-two A5 source controls the original joins and
containments in either critical orientation. -/
theorem a5_pair_core_and_containment_of_critical_bTwo
    (h : HypothesisF11 ![K,R] S)
    (a : ∀ j, Nonempty ((![K,R] j ⧸ pCore 2 (![K,R] j)) ≃*
      alternatingGroup (Fin 5)))
    (hnorm : ∃ j, borel (![K,R] j) S ≤ normalizer (S : Set G))
    (i : Bool) {w : Vertex (reducedFamily ![K,R] S)}
    (hc : IsCriticalPair (reducedFamily ![K,R] S)
      (base (reducedFamily ![K,R] S) i) w)
    (hne : ⁅Z (reducedFamily ![K,R] S) (base (reducedFamily ![K,R] S) i),
      Z (reducedFamily ![K,R] S) w⁆ ≠ ⊥)
    (hb : b (reducedFamily ![K,R] S) = 2)
    (hmw : (graph (reducedFamily ![K,R] S)).Adj
      (base (reducedFamily ![K,R] S) (!i)) w) :
    (∀ j, twoCore (![K,R] j ⊔ S) = twoCore (![K,R] j)) ∧
      (∀ j, S ≤ ![K,R] j) := by
  cases i
  · obtain ⟨short,⟨e⟩⟩ := h.a5_bTwo_reduced_g2_comparison a hc hne hb hmw
    exact A5PairCatalogue.G2.core_and_containment (GaloisField 2 2) h a hnorm short e
  · obtain ⟨w',hc',hne',hmw'⟩ :=
      CriticalReorientation.original_noncommuting_critical_swap K R S hc hne hmw
    have a' : ∀ j, Nonempty ((![R,K] j ⧸ pCore 2 (![R,K] j)) ≃*
        alternatingGroup (Fin 5)) := by
      intro j
      fin_cases j
      · exact a 1
      · exact a 0
    have hn' : ∃ j, borel (![R,K] j) S ≤ normalizer (S : Set G) := by
      obtain ⟨j,hj⟩ := hnorm
      fin_cases j
      · exact ⟨1,hj⟩
      · exact ⟨0,hj⟩
    have hb' : b (reducedFamily ![R,K] S) = 2 := (pair_b_swap K R S).trans hb
    obtain ⟨short,⟨e⟩⟩ := h.swap.a5_bTwo_reduced_g2_comparison a' hc' hne' hb' hmw'
    obtain ⟨hcores,hcontain⟩ :=
      A5PairCatalogue.G2.core_and_containment (GaloisField 2 2) h.swap a' hn' short e
    constructor
    · intro j
      fin_cases j
      · exact hcores 1
      · exact hcores 0
    · intro j
      fin_cases j
      · exact hcontain 1
      · exact hcontain 0

/-- The original pair itself supplies all critical and recognition data.
Both literal join-core equalities and both containments follow from F.1.1,
the two A5 quotient marks and one normalized Borel. -/
theorem a5_pair_core_and_containment_from_source
    {L : Fin 2 → Subgroup G}
    (h : HypothesisF11 L S)
    (a : ∀ j, Nonempty ((L j ⧸ pCore 2 (L j)) ≃* alternatingGroup (Fin 5)))
    (hnorm : ∃ j, borel (L j) S ≤ normalizer (S : Set G)) :
    (∀ j, twoCore (L j ⊔ S) = twoCore (L j)) ∧ (∀ j, S ≤ L j) := by
  have hL : L = ![L 0,L 1] := by
    funext j
    fin_cases j <;> rfl
  rw [hL] at h a hnorm ⊢
  rcases a5_pair_original_bTwo_reduction h a hnorm with hdone |
    ⟨i,w,hc,hb,hmw,hne,_⟩
  · exact hdone
  · exact a5_pair_core_and_containment_of_critical_bTwo h a hnorm i hc hne hb hmw

end CFSG.Quasithin.ChapterF.Source
