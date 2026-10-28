module

public import CFSG.Quasithin.ChapterG.Section05.Structure.Defs
public import Theory.Representation.BinaryDuadStructure.Universal

/-!
# Checked cover and line-relation structure in G.5.3

The literal quotient U₀/D is a five-dimensional perfect central cover of the
marked natural module, through the polar-vector projection. The equivalent
line-relation quotient has the universal property and nonzero quotient
classification required in clause (6). The middle cover, the radical/chief
identifications, and the deduction of line relations from the source orbit
hypotheses are separate obligations.

Source: Aschbacher–Smith, G.5.3, printed pp.343–345.
-/

public section

namespace CFSG.Quasithin.ChapterG.Section05.Structure

/-- The covering part of G.5.3(3), on the literal source quotient.
The identification D = J²(U₀) is not assumed here. -/
theorem core_quotient_is_five_dimensional_cover :
    Module.finrank (ZMod 2) (U0 ⧸ lineComplementSpan.comap U0.subtype) = 5 ∧
      Representation.OneCohomology.IsCover BinaryDuadStructure.coreNaturalProjection :=
  ⟨quotient_finranks.1, BinaryDuadStructure.coreNaturalProjection_isCover⟩

end CFSG.Quasithin.ChapterG.Section05.Structure
