module

public import Theory.SpecificGroups.Tits.Presentation
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.FixedCoordinates.RootPartition
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.FixedCoordinates.MatrixRelations
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.FixedGeometry.WeylLifts

/-!
# Concrete fixed words for the binary Parrott realization

The eight positive relative root groups are placed in their dihedral order
using the explicit F₄ root table. Their blocks, with zero-based indices in
`FixedCoordinates.RootPartition`, are Q₀, P₁, Q₃, P₃, Q₁, P₂, Q₂, P₀.
A pair contributes its two parameter-one root elements; a quartet ordered
`r,s,r+s,r+2s` contributes `x_r(1) x_s(1) x_{r+2s}(1)`.
The quartet orientation is part of the assignment: replacing this element
by its inverse changes several Parrott relations.

The two Weyl words are the longest words `[1,2,1,2]` and `[0,3]`.
The proved block-twist formulas and integral braid identities show that
all ten assigned elements are fixed by the exceptional twist. Verification
of the 37 presentation relations is a separate obligation.

Source: Parrott (1972), printed p.683, and the scan-checked transcription
`refs/original/n-group-global/parrott-tits-presentation.md`; GLS3 §§2.3–2.4,
particularly Table 2.4. Products follow Parrott's displayed order.
-/

@[expose] public section
noncomputable section
namespace ReeF4.DerivedTits.Realization

open Theory.AlgebraicGroup
open Parabolics.RadicalCoordinates.FixedCoordinates
open Parabolics.Binary.FixedGeometry

/-- The actual roots of a positive commuting pair, in long-short order. -/
def pairRoots (i : Fin 4) (j : Fin 2) : F4Chevalley.Root :=
  ((rootBlocks .positive).roots (.inl (i, j))).val

/-- The actual roots of a positive B₂ quartet, in the order `r,s,r+s,r+2s`. -/
def quartetRoots (i : Fin 4) (j : Fin 4) : F4Chevalley.Root :=
  ((rootBlocks .positive).roots (.inr (i, j))).val

/-- The nonzero parameter in a binary relative root group of pair type. -/
def pairElement (i : Fin 4) : SplitGroup 0 :=
  pairWord 0 (pairRoots i) (pairSolution 0 1)

/-- The chosen orientation in a binary relative root group of quartet type. -/
def quartetElement (i : Fin 4) : SplitGroup 0 :=
  quartetWord 0 (quartetRoots i) (quartetSolution 0 1 0)

theorem pairElement_fixed (i : Fin 4) :
    reeTwist 0 (pairElement i) = pairElement i := by
  exact ((rootBlocks .positive).twist_pair 0 (mixedRootCommutation 0) i
    (pairSolution 0 1)).trans
      (congrArg (pairWord 0 (pairRoots i)) (pairSolution_fixed 0 1))

theorem quartetElement_fixed (i : Fin 4) :
    reeTwist 0 (quartetElement i) = quartetElement i := by
  exact ((rootBlocks .positive).twist_quartet 0 (mixedRootCommutation 0) (b2RootSwap 0)
    i (quartetSolution 0 1 0)).trans
      (congrArg (quartetWord 0 (quartetRoots i)) (quartetSolution_fixed 0 1 0))

/-- The pair is exactly the product of its two parameter-one root matrices. -/
theorem pairElement_eq (i : Fin 4) :
    pairElement i = rootGeneratorInGroup 0 (pairRoots i 0) 1 *
      rootGeneratorInGroup 0 (pairRoots i 1) 1 := by
  simp [pairElement, pairWord, pairSolution]

/-- The quartet has parameters `(1,1,0,1)`, with the zero factor removed. -/
theorem quartetElement_eq (i : Fin 4) :
    quartetElement i = rootGeneratorInGroup 0 (quartetRoots i 0) 1 *
      rootGeneratorInGroup 0 (quartetRoots i 1) 1 *
      rootGeneratorInGroup 0 (quartetRoots i 3) 1 := by
  have hz (r : F4Chevalley.Root) : rootGeneratorInGroup 0 r 0 = 1 := by
    apply Subtype.ext
    exact F4Chevalley.rootCurve_zero r
  simp [quartetElement, quartetWord, quartetSolution, hz]

/-- Eight oriented root elements; `u 0` denotes the source's `u₁`. -/
def u : Fin 8 → SplitGroup 0 :=
  ![quartetElement 0, pairElement 1, quartetElement 3, pairElement 3,
    quartetElement 1, pairElement 2, quartetElement 2, pairElement 0]

theorem u_fixed (i : Fin 8) : reeTwist 0 (u i) = u i := by
  fin_cases i <;> simp [u, pairElement_fixed, quartetElement_fixed]

/-- Parrott's ten generators as explicit root and Weyl words in the split F₄ carrier. -/
def assignment : Tits.ParrottGenerator → SplitGroup 0
  | .r1 => simpleWord 0 (sideWord .suzuki)
  | .r8 => simpleWord 0 (sideWord .linear)
  | .s1 => u 0 * u 0
  | .s2 => u 1
  | .s3 => u 0 * u 2
  | .s4 => u 3
  | .s5 => u 0 * u 4
  | .s6 => u 5
  | .s7 => u 6 * (u 0)⁻¹
  | .s8 => u 7

/-- Every assigned matrix lies in the actual binary exceptional fixed group. -/
theorem assignment_fixed (i : Tits.ParrottGenerator) :
    reeTwist 0 (assignment i) = assignment i := by
  cases i <;> simp only [assignment, map_mul, map_inv, u_fixed, sideWord_fixed]

end ReeF4.DerivedTits.Realization
