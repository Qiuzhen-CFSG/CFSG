module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.RootCurve

/-!
# Split words for the eight positive relative Ree roots

The middle-node longest Weyl element and the commuting end-node reflections
give the two reflections of the relative octagon. Starting from the middle
long simple root and the end long simple root specifies the long roots in
its eight positive root blocks. The odd numbered blocks have type B₂ and
the even numbered blocks have type A₁ × A₁. Indices here are zero based.

These are words in the existing split matrix group, with the type-B₂
correction term included. Fixedness, fixed factorization, and their
commutator identities are separate obligations; the definitions assert none
of these. The eighth word agrees with the already proved end-root curve.

Source: GLS3, §§2.3–2.4, especially Table 2.4 and 2.4.5(d), transcribed in
`refs/KGroup/GLS3/chapter2.tex`. The application is the radical contribution
to Aschbacher–Smith F.1.12(II)(i), printed pp.263–264.
-/

@[expose] public section
noncomputable section

namespace ReeF4.Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem

/-- The longest element of the middle B₂ Weyl group, acting on actual roots. -/
def middleReflection : Equiv.Perm F4Chevalley.Root :=
  typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 1) *
    typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 2) *
    typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 1) *
    typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 2)

/-- The longest element of the end-node A₁ × A₁ Weyl group. -/
def endReflection : Equiv.Perm F4Chevalley.Root :=
  typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 0) *
    typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 3)

/-- Rotation by two positions in the relative octagon. -/
def relativeRotation : Equiv.Perm F4Chevalley.Root := middleReflection * endReflection

/-- A matrix representative of the middle reflection. Its fixedness and
conjugation formula require the B₂ Weyl relations. -/
def middleWeylWord (m : ℕ) : SplitGroup m :=
  weylWord m (typeF4SimpleRootIndex 1) 1 *
    weylWord m (typeF4SimpleRootIndex 2) 1 *
    weylWord m (typeF4SimpleRootIndex 1) 1 *
    weylWord m (typeF4SimpleRootIndex 2) 1

/-- Long root in each positive relative block; position seven is the end root. -/
def longRoot : Fin 8 → F4Chevalley.Root :=
  ![typeF4SimpleRootIndex 1,
    middleReflection (typeF4SimpleRootIndex 0),
    relativeRotation (typeF4SimpleRootIndex 1),
    relativeRotation (middleReflection (typeF4SimpleRootIndex 0)),
    (relativeRotation ^ 2) (typeF4SimpleRootIndex 1),
    (relativeRotation ^ 2) (middleReflection (typeF4SimpleRootIndex 0)),
    (relativeRotation ^ 3) (typeF4SimpleRootIndex 1),
    typeF4SimpleRootIndex 0]

/-- The short partner, with the existing exceptional root permutation. -/
def shortRoot (i : Fin 8) : F4Chevalley.Root := exceptionalRootPermutation (longRoot i)

/-- In a B₂ block this is the root α + β, with α long. -/
def mixedRoot (i : Fin 8) : F4Chevalley.Root :=
  typeF4RootPairing.reflectionPerm (longRoot i) (shortRoot i)

/-- In a B₂ block this is the root α + 2β. -/
def highRoot (i : Fin 8) : F4Chevalley.Root :=
  typeF4RootPairing.reflectionPerm (shortRoot i) (longRoot i)

/-- The main parameter in a relative root block. At even indices (source odd
numbers), the mixed-root factor is essential to the intended fixed word. -/
def rootWord (m : ℕ) (i : Fin 8) (t : CoefficientField m) : SplitGroup m :=
  rootGeneratorInGroup m (longRoot i) t *
    rootGeneratorInGroup m (shortRoot i) (rootFieldEnd m (longRoot i) t) *
    if i.val % 2 = 0 then
      rootGeneratorInGroup m (mixedRoot i) (t * rootFieldEnd m (longRoot i) t)
    else 1

/-- The central parameter in a B₂ block (used only at even indices). -/
def centralWord (m : ℕ) (i : Fin 8) (u : CoefficientField m) : SplitGroup m :=
  rootGeneratorInGroup m (highRoot i) u *
    rootGeneratorInGroup m (mixedRoot i) (rootFieldEnd m (longRoot i) u)

@[simp] theorem rootWord_end (m : ℕ) (t : CoefficientField m) :
    rootWord m 7 t = endRootWord m t := by
  simp [rootWord, longRoot, shortRoot, endRootWord,
    exceptionalRootPermutation_simple, Fin.revPerm, Fin.rev]

end ReeF4.Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
