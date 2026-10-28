module

public import Theory.SpecificGroups.G2Five.AtlasBoundSubgroup
public import Mathlib.GroupTheory.PresentedGroup

/-!
# A two-generator presentation for the fixed local subgroup

The two generators are the literal words `boundWord false` and
`boundWord true` from `AtlasBoundSubgroup`.  We use the following compact
relator package (the words are written in the same left-to-right convention as
the ATLAS presentation):

```
 x^10, y^20, (xy)^24, (xy⁻¹)^20,
 (x²y)^8, (xy²)^12, [x,y]^15.
```

These are the short two-generator relators obtained from the stabilizer
presentation calculation in `AtlasBoundSource/Verify.g`; the calculation is
only a source of words.  The relation-lifting file proves them in the
22-relator presentation, and the order-certificate file supplies the finite
coset enumeration.  Thus this module contains no identification or finiteness
assumption about `Model`.

Source and attribution: the ATLAS words and the original 22 relators are
retained in `AtlasPresentationSource/` and `AtlasBoundSubgroup.lean`; the
permutation calculation is untrusted discovery data in `AtlasBoundSource/`.
-/

namespace G2Five.AtlasPresentation

public abbrev BoundLocalAlphabet := Bool

/-- A local free-group word from its signed-letter spelling. -/
@[expose] public def boundLocalWord (s : String) : FreeGroup Bool :=
  FreeGroup.mk (boundLetters s)

@[expose] public def boundLocalGeneratorWord (b : Bool) : FreeGroup Bool :=
  FreeGroup.of b

public abbrev boundLocalX : FreeGroup Bool := FreeGroup.of false
public abbrev boundLocalY : FreeGroup Bool := FreeGroup.of true

/-- The seven relators of the compact two-generator local presentation. -/
@[expose] public def boundLocalRelator : Fin 7 → FreeGroup Bool :=
  fun
  | 0 => boundLocalX ^ 10
  | 1 => boundLocalY ^ 20
  | 2 => (boundLocalX * boundLocalY) ^ 24
  | 3 => (boundLocalX * boundLocalY⁻¹) ^ 20
  | 4 => (boundLocalX ^ 2 * boundLocalY) ^ 8
  | 5 => (boundLocalX * boundLocalY ^ 2) ^ 12
  | _ => (boundLocalX⁻¹ * boundLocalY⁻¹ * boundLocalX * boundLocalY) ^ 15

/-- The abstract local presentation on the two fixed subgroup words. -/
@[expose] public def BoundLocalPresentation :=
  PresentedGroup (Set.range boundLocalRelator)
  deriving Group

/-- Its canonical local generators. -/
@[expose] public def boundLocalGenerator (b : Bool) : BoundLocalPresentation :=
  PresentedGroup.of b

@[simp] public theorem boundLocalRelator_zero :
    boundLocalRelator (0 : Fin 7) = boundLocalX ^ 10 := by rfl

@[simp] public theorem boundLocalRelator_one :
    boundLocalRelator (1 : Fin 7) = boundLocalY ^ 20 := by rfl

@[simp] public theorem boundLocalRelator_two :
    boundLocalRelator (2 : Fin 7) = (boundLocalX * boundLocalY) ^ 24 := by rfl

@[simp] public theorem boundLocalRelator_three :
    boundLocalRelator (3 : Fin 7) = (boundLocalX * boundLocalY⁻¹) ^ 20 := by rfl

@[simp] public theorem boundLocalRelator_four :
    boundLocalRelator (4 : Fin 7) = (boundLocalX ^ 2 * boundLocalY) ^ 8 := by rfl

@[simp] public theorem boundLocalRelator_five :
    boundLocalRelator (5 : Fin 7) = (boundLocalX * boundLocalY ^ 2) ^ 12 := by rfl

@[simp] public theorem boundLocalRelator_six :
    boundLocalRelator (6 : Fin 7) =
    (boundLocalX⁻¹ * boundLocalY⁻¹ * boundLocalX * boundLocalY) ^ 15 := by rfl

end G2Five.AtlasPresentation
