module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFusionComplete
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalContainedConjugateFusionModel

/-!
# Corank and mutual-conjugate fusion on the Chapter 12 layer

These are the source 6.1.10(3) and 6.1.11 conclusions for the literal
B=[R₂(LT),L]. The natural-action rank and offender inputs have been proved;
the original chosen module supplies the required 6.1.9 normalizer control.
Thus only the permitted earlier E.6.1 and global-s inputs remain explicit.
The arguments need only 12.2.1, which is inherited by 12.2.3.

The final theorem supplies both contracts consumed by the contained-conjugate
assembly. The parent retains the independent fixed-space and field-escape
branches of 6.1.15; neither is used to prove these two contracts.

Source: Aschbacher--Smith, printed pp.669--670 (PDF pp.686--687).
-/

public section

open Subgroup
open CFSG.Quasithin.Chapter6.Source.RankOneRecognition
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- The original action corank, before inverse-conjugation transport. -/
theorem source_lemma_6_1_10_3
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T
      (normalizer (L : Set G)) (commutatorLayer T L))
    (hs : letI := h611.layer_elementary; ChapterE.globalS (commutatorLayer T L) = n)
    (g : G)
    (hg : (commutatorLayer T L).map (MulAut.conj g).toMonoidHom ≤
      normalizer (commutatorLayer T L : Set G))
    (hnon : ¬ (commutatorLayer T L).map (MulAut.conj g).toMonoidHom ≤
      centralizer (commutatorLayer T L : Set G)) :
    ChapterE.subgroupCorank ((commutatorLayer T L).map (MulAut.conj g).toMonoidHom)
      ((commutatorLayer T L).map (MulAut.conj g).toMonoidHom ⊓
        centralizer (commutatorLayer T L : Set G)) = n :=
  conjugate_action_corank_eq_of_natural h611 hnatural hE hs g hg hnon

/-- The full printed conclusion, with the original nonzero-commutator
hypothesis. In particular, the intersection assertion is retained. -/
theorem source_lemma_6_1_11
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T
      (normalizer (L : Set G)) (commutatorLayer T L))
    (hs : letI := h611.layer_elementary; ChapterE.globalS (commutatorLayer T L) = n)
    (hI : centralizer (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L) : Set G) ≤
      normalizer (L : Set G))
    (g : G) (hg : (commutatorLayer T L).map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G))
    (hnon : ⁅commutatorLayer T L, (commutatorLayer T L).map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥)
    (hcomm : ⁅commutatorLayer T L, (commutatorLayer T L).map (MulAut.conj g).toMonoidHom⁆ ≤
      commutatorLayer T L ⊓ (commutatorLayer T L).map (MulAut.conj g).toMonoidHom) :
    let B := commutatorLayer T L
    let A := B.map (MulAut.conj g).toMonoidHom
    let Z := Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L)
    B ⊓ centralizer (A : Set G) = Z ∧ A ⊓ centralizer (B : Set G) = Z ∧
      ⁅B, A⁆ = Z ∧ B ⊓ A = Z ∧
      ∃ c ∈ centralizer (Z : Set G), A = B.map (MulAut.conj c).toMonoidHom :=
  mutual_conjugate_source_of_natural h611 hnatural hE hs
    (source_central_line_normalizer_factorization D h h611 hI) g hg hnon hcomm

/-- Both published contracts for the actual Chapter 12 assembly, with
the natural-action and normalizer premises discharged. -/
theorem source_conjugate_corank_and_fusion
    (D : ChosenModule T L V)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T
      (normalizer (L : Set G)) (commutatorLayer T L))
    (hs : letI := h611.layer_elementary; ChapterE.globalS (commutatorLayer T L) = n)
    (hI : centralizer (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L) : Set G) ≤
      normalizer (L : Set G)) :
    ConjugateCorankFormula (T : Subgroup G) (commutatorLayer T L) n ∧
      MutualConjugateFusion (T : Subgroup G) (commutatorLayer T L)
        (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L)) :=
  ⟨source_conjugateCorankFormula_of_natural_action h611 hnatural hE hs,
    source_mutualConjugateFusion_of_natural_action D h.toHypothesis1221
      h611 hnatural hE hs hI⟩

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
