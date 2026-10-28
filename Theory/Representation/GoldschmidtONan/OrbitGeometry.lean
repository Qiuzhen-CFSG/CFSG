module

public import Theory.Representation.GoldschmidtONan.OrbitGeometry.Exhaustion

public import Theory.Representation.GoldschmidtONan.OrbitGeometry.Suborbits
public import Theory.Representation.GoldschmidtONan.OrbitGeometry.Transitive
public import Theory.Representation.GoldschmidtONan.OrbitGeometry.Complement

/-!
# TI suborbit geometry for Goldschmidt–O'Nan pairs

The actual Step 1 suborbit dichotomy is proved by `Input.suborbitGeometry`.
The all-second-suborbit branch of Step 2, including the cardinality, exact
nonzero union and moved-space invariance, is proved by
`Input.complementCase_of_disjoint_moved`. The complete exhaustion into singleton, swapped, complement and transitive
geometries is now proved by `Input.geometric_alternatives`; `Input.orbitGeometry`
returns it together with the full suborbit dichotomy.
Source: GLS, Number 2, Chapter C, Proposition 14.2, Steps 1–2
(`refs/KGroup/GLS2/ChapterC.tex`).
-/
