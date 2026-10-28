module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnOrbit.Edges.Transposes.Arithmetic

/-!
# Concatenating short rectangle certificates

Numerical checks traverse only short literal lists of column blocks. This lemma
assembles those checks without recomputing a long Boolean traversal. The concrete
applications are the row certificates in `First/` and `Second/`.
Source and the measured traversal cost: `source/README.md`.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnEdges.Transposes

theorem checkRow_append (rs : List Nat) (q : Nat) (as bs : Blocks) :
    checkRow rs q (as ++ bs) = (checkRow rs q as && checkRow rs q bs) := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    rcases a with ⟨p, ts⟩
    simp only [List.cons_append, checkRow, ih, Bool.and_assoc]

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnEdges.Transposes
