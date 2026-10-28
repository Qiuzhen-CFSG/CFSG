module
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.KnownCarrierCases.McLComplete
public import CFSG.Quasithin.ChapterA.Section02.Sporadic.SourceAssembly.OriginalFischer
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.RankTwoSieve.Fi24Reduction
/-!
# Final simultaneous A.2 induction with its two concrete sporadic producers

Every full-catalogue source branch and every nonsemisimple reduction is
assembled here. The remaining inputs are exactly an actual Fi24 involution-
centralizer quotient onto Fi22 and an original-context compatible O'Nan
central-cover lift. In particular, no numerical Fi24 two-rank assertion,
carrier comparison, family classifier, or independent induction premise
is retained. The two source producers still need their own proofs before
this conditional assembly becomes the unconditional book theorem.
Source: Aschbacher--Smith A.2.1--3 and A.2.8--19, printed pp.33--41.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {G S : Type u} [Group G] [Group S] [Finite G] [Finite S] {p : ℕ}

/-- The actual Fischer section closes the complete nonsemisimple source branch. -/
theorem CounterexampleToTheoremA.isSemisimple_of_fi24_source
    (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p)
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (d24 : InvolutionCentralizerQuotientData _root_.Sporadic.Fischer.Fi24Prime.Carrier
      _root_.Sporadic.Fischer.Fi22.Carrier) : IsSemisimple G := by
  by_contra hn
  obtain ⟨e⟩ := h.centralQuotient_fi24_of_not_semisimple ih hn
  exact h.centralQuotient_no_fischer_of_source_data ih e d24

/-- Full-catalogue A/B/C induction; only the two stated concrete source producers remain. -/
theorem theoremsABC_of_fi24_onan
    (d24 : InvolutionCentralizerQuotientData _root_.Sporadic.Fischer.Fi24Prime.Carrier
      _root_.Sporadic.Fischer.Fi22.Carrier)
    (hON : ∀ (X Y : Type u) [Group X] [Group Y] [Finite X] [Finite Y] [IsQuasisimple X]
      (p : ℕ) (_h : CounterexampleToTheoremA KnownSimple.IsKnownSimple X Y p)
      (_ih : TheoremsOnProperSections KnownSimple.IsKnownSimple X)
      (e : X ⧸ center X ≃* ONan.Model),
      ∃ F : ONan.Cover.linearSubgroup →* X,
        (Sporadic.SourceAssembly.projection e).comp F = ONan.Cover.projection) :
    TheoremsABC KnownSimple.IsKnownSimple G := by
  apply simultaneous_induction
  intro X _ _ ih
  by_contra hn
  have hm : MinimalCounterexample KnownSimple.IsKnownSimple X := ⟨hn,ih⟩
  by_cases hs : IsSimpleGroup X
  · let : IsSimpleGroup X := hs
    exact hm.simple_false_of_fi24_section d24
  · obtain ⟨Y,hY,hfinY,p,h⟩ := hm.nonsimple_case hs
    let : Group Y := hY
    let : Finite Y := hfinY
    have hsemi := h.isSemisimple_of_fi24_source ih d24
    let : IsQuasisimple X := h.quasisimple_of_semisimple ih hsemi
    exact h.quasisimple_false_of_fi24_onan ih d24 (hON X Y p h ih)
/-- A genuine original-context O'Nan exclusion also closes the same induction.
This form lets a local source proof avoid constructing an unnecessary global cover map. -/
theorem theoremsABC_of_fi24_onan_source
    (d24 : InvolutionCentralizerQuotientData _root_.Sporadic.Fischer.Fi24Prime.Carrier
      _root_.Sporadic.Fischer.Fi22.Carrier)
    (hON : ∀ (X Y : Type u) [Group X] [Group Y] [Finite X] [Finite Y] [IsQuasisimple X]
      (p : ℕ) (_h : CounterexampleToTheoremA KnownSimple.IsKnownSimple X Y p)
      (_ih : TheoremsOnProperSections KnownSimple.IsKnownSimple X)
      (_e : X ⧸ center X ≃* ONan.Model), False) :
    TheoremsABC KnownSimple.IsKnownSimple G := by
  apply theoremsABC_of_fi24_onan d24
  intro X Y _ _ _ _ _ p h ih e
  exact (hON X Y p h ih e).elim
end CFSG.Quasithin.ChapterA.Section02
