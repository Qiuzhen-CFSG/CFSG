module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Irreducible
public import Theory.Representation.SpecialLinearNatural.ParabolicRadical

/-!
# The rank of the literal exterior-five offender

The B.4.2 exterior-square row specifies the embedded two-core of a natural
end-node stabilizer. Its binary rank is four, by the order calculation in
the original matrix model. No coordinate marking is required of the subspace.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.4.2(11),
printed p.86; used to exclude this row in G.6.4, printed pp.345–346.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource

/-- Both literal end-node radicals in the B.4.2 exterior-five row have rank four. -/
theorem IsEndNodeRadical.rank {A : Subgroup (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))}
    (hA : IsEndNodeRadical A) : Representation.BinaryOffender.rank A = 4 := by
  obtain ⟨P, hP, rfl⟩ := hA
  exact Representation.SpecialLinearNatural.endNode_five_rank P hP

end CFSG.Quasithin.ChapterB.QuasisimpleSource
