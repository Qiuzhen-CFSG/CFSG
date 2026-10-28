module

public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.G2
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Orthogonal
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.ExceptionalRestrictions

/-!
# Concrete block-type interfaces

Public entry point for the named block types in Aschbacher--Smith C.1.12,
C.1.22 and C.1.30 (combined manuscript of 1 March 2004, printed pp.124,
129 and 135). This includes the linear, alternating, exceptional alternating,
symplectic, derived G₂(2), and signed orthogonal natural types, together with
χ and χ₀. Ambient block membership is supplied by `IsBlockOfType`.

The standard families identify both the actual quotient by O₂ and its
conjugation module. The exceptional A₇ and triple-cover A₆ definitions retain
the source's dimension and faithfulness clauses; their natural restrictions
to SL₄(F₂) and SL₃(F₄) are proved consequences, re-exported here.

`BlockTypes.G2Source` separately connects the canonical G₂ type to the
octonion-projection formulation used by C.2.7 and Chapter 13.
-/
