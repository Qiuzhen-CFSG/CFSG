module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.BrauerTree.PathRealization.Construction.Inputs
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.BrauerTree.PathRealization.Construction.Contracts
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.BrauerTree.PathRealization.Construction.Pairing
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.BrauerTree.PathRealization.Construction.LocalIndex

/-!
# Assembly interface for the genuine principal eleven-block real stem

A module-valued cyclic-defect line is transported through the identification
of the actual principal congruence block with the eleven nonzero-defect rows.
The resulting `RealStem` uses the same simple modules and root correspondence.
Its projective edges retain actual projectivity, ready for the regular scalar
product theorem.

This is conditional assembly, not the existence theorem: principal-block
identification, cyclic-defect line construction and projective reciprocity
remain to be proved. The source route is Feit VII.2.11--15, VII.6.8 and
VII.9.2, applied to Janko's ordinary character table.
-/

namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree.Construction

open Representation

private theorem incidence_ten {A : Type*} [AddCommMonoid A] (v : Fin 10 → A) (i : Fin 11) :
    CyclicDefect.incidence v i = lineIncidence v i := by
  fin_cases i <;> simp [CyclicDefect.incidence, Fin.sum_univ_succ, lineIncidence]

variable {G : Type*} [Group G] [Finite G] {d : OrdinaryData G}

/-- Convert a genuine line for the identified congruence block to the existing
source contract. This does not assert existence of the line. -/
@[expose] public def realStemOfLine (b : PrincipalBlockIdentification d)
    (L : CyclicRootLift ElevenClosure 15960)
    (r : CyclicDefect.RealLine b.data.chi b.data.block b.data.principal 11 10 L) :
    RealStem G d where
  row i := b.rows.symm (r.row i)
  row_injective := b.rows.symm.injective.comp r.row_injective
  row_nonzero_defect i := (b.membership _).mp (by simpa using r.row_mem i)
  first_row := by rw [r.first_row, ← b.principal, b.rows.symm_apply_apply]
  degree := r.degree
  rep := r.rep
  irreducible := r.irreducible
  inequivalent := r.inequivalent
  roots := L
  decomposition g hg i := by
    rw [← b.characters, b.rows.apply_symm_apply, r.decomposition g hg i, incidence_ten]

/-- The adapter preserves genuine projective realizations of every adjacent sum. -/
public def projectiveEdgesOfLine (b : PrincipalBlockIdentification d)
    (L : CyclicRootLift ElevenClosure 15960)
    (r : CyclicDefect.RealLine b.data.chi b.data.block b.data.principal 11 10 L) :
    ProjectiveEdges (realStemOfLine b L r) := fun k => {
  degree := (r.projective k).degree
  rep := (r.projective k).rep
  projective := (r.projective k).projective
  character_eq := by
    intro g hg
    change L.value (r.projective k).rep g =
      d.chi (b.rows.symm (r.row k.castSucc)) (ConjClasses.mk g) +
        d.chi (b.rows.symm (r.row k.succ)) (ConjClasses.mk g)
    rw [(r.projective k).character_eq g hg, ← b.characters, ← b.characters]
    simp only [b.rows.apply_symm_apply] }

end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree.Construction
