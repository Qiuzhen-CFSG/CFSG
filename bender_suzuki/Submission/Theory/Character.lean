module  -- shake: keep-all --deprecated_module: ignore

public import Submission.Theory.Character.ClassFunction
public import Submission.Theory.Character.Orthogonality
public import Submission.Theory.Character.Integrality
public import Submission.Theory.Character.Induction
public import Submission.Theory.Character.BrauerSuzuki
public import Submission.Theory.Character.ConjClassFunction
public import Submission.Theory.Character.SimpleCriteria
public import Submission.Theory.Character.Completeness
public import Submission.Theory.Character.Divisibility
public import Submission.Theory.Character.BrauerPermutation
public import Submission.Theory.Character.CharacterValues
public import Submission.Theory.Character.DegreeBounds
public import Submission.Theory.Character.Cyclotomic
public import Submission.Theory.Character.CrossCharBrauer

/-!
# Character theory core

Clean, self-contained infrastructure for the character theory of finite groups
over `ℂ`: class functions `G → ℂ`, the scalar product, characters and
irreducible characters (via Mathlib representation theory), generalized
characters, orthonormality of irreducible characters, integrality of character
values, induction of class functions, the Brauer--Suzuki pairing machinery,
and the bridge to class functions on conjugacy classes `ConjClasses G → ℂ`.

This module is the aggregator; the content lives in `Theory/Character/*`:
- `ClassFunction` — class functions and the scalar product
- `Orthogonality` — orthonormality of irreducible characters
- `Integrality` — algebraic integrality of character values
- `Induction` — induction of class functions
- `BrauerSuzuki` — the Brauer--Suzuki scalar-product expansion
- `ConjClassFunction` — class functions on conjugacy classes and the bridges
-/
