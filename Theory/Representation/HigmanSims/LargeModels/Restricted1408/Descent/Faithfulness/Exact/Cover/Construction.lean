module
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.Exact.Cover.Output
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.Exact.Cover.Context
public import Theory.GroupTheory.GeneratorCosetCoverFiniteIndex

/-!
# Constructing the centralizer cover from checked deductions

All four signed generator transitions have actual subgroup witnesses. Word
induction therefore covers the abstract presentation, without assuming it
finite. The two finite Boolean checking obligations are discharged by the
sibling `Deductions` and `Shape` modules in `Exact.Cover`.
Source: the centralizer enumeration in ATLAS HSG1-P1.M.
-/

namespace Sporadic.LeechRelated.HS.AtlasPresentation.Exact.Cover
open Subgroup.CosetWordCertificate

@[expose] public def cover_of_checked
    (hf : ∀ n, n < 331989 → Holds centralizer certGenerator (definitions.repr certGenerator) (facts n))
    (hs : ∀ n, n < 23100 → shapeAt n = true) :
    Subgroup.GeneratorCosetCover centralizer generator (Fin 5775) := by
  have transitions (i : Fin 5775) (a : Fin 4) :
      Holds centralizer certGenerator (definitions.repr certGenerator)
        ⟨i.val, [decode a.val], (destination (4*i.val+a.val)).val⟩ := by
    have hh := (factBEq_eq_true_iff _ _).mp (hs (4*i.val+a.val) (by omega))
    have hd : (4*i.val+a.val) / 4 = i.val := by omega
    have hm : (4*i.val+a.val) % 4 = a.val := by omega
    change facts (output (4*i.val+a.val)) = _ at hh
    rw [hd, hm] at hh
    rw [← hh]
    exact hf _ (output_lt _)
  exact {
    repr := fun i => definitions.repr certGenerator i.val
    initial := 0
    initial_eq := definitions.repr_zero certGenerator
    step := by
      intro i a
      cases a
      · obtain ⟨h, hh⟩ := transitions i 0
        refine ⟨h, destination (4*i.val+0), ?_⟩
        simpa [decode, certGenerator, tracePair, extendedPair] using hh
      · obtain ⟨h, hh⟩ := transitions i 2
        refine ⟨h, destination (4*i.val+2), ?_⟩
        simpa [decode, certGenerator, tracePair, extendedPair] using hh
    inv_step := by
      intro i a
      cases a
      · obtain ⟨h, hh⟩ := transitions i 1
        refine ⟨h, destination (4*i.val+1), ?_⟩
        simpa [decode, certGenerator, tracePair, extendedPair] using hh
      · obtain ⟨h, hh⟩ := transitions i 3
        refine ⟨h, destination (4*i.val+3), ?_⟩
        simpa [decode, certGenerator, tracePair, extendedPair] using hh }

end Sporadic.LeechRelated.HS.AtlasPresentation.Exact.Cover
