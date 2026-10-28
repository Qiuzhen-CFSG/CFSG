module

public import CFSG.Quasithin.ChapterG.Section03.Source
public import CFSG.Quasithin.ChapterG.Section03.Decomposition.InternalProducts

/-!
# The internal orbit decompositions in G.3.1

Assuming full linear action on the canonical orbit spans, this module proves
all the internal decomposition clauses of G.3.1(1). The TI-pair argument gives
cross-fixation and commutation; full linear action gives independence; the
canonical multiplication and summation maps give compatible equivalences.

This is a conditional helper. The recognition and local-structure assertions
of G.3.1 remain the responsibility of the source theorem's assembly.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, G.3.1, printed pp. 337--338 (PDF pp. 348--349).
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterG.Section03

open BinaryLinear DecompositionProof

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- G.3.1(1), conditional on the full actions supplied by the recognition argument. -/
theorem decomposition_of_fullAction (G : Subgroup (GL V)) [Finite G] (Δ : Set V)
    (h : Hypotheses G Δ) (hfull : FullAction G Δ) : Decomposition G Δ := by
  have hspace := blocks_space_independent h hfull
  exact
    { space_span := blocks_span h
      space_independent := hspace
      group_join := blocks_join h
      group_independent := blocks_group_independent hspace
      cross_fix := fun _ _ hij => blocks_cross_fix h hij
      groups_commute := fun _ _ hij => blocks_commute h hij
      groups_conjugate := block_groups_conjugate h
      spaces_conjugate := block_spaces_conjugate h
      group_equiv := blocks_group_equiv h hspace
      space_equiv := blocks_space_equiv h hspace }

end CFSG.Quasithin.ChapterG.Section03
