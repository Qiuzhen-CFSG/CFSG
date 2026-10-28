module

public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Placement.Geometry
public import Theory.Representation.GeneralLinearNatural
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# Linear frames for the nonabelian odd unitary branch

The intermediate frame is an arbitrary invertible matrix over the original
coefficient field. Its projective column lines must be preserved by the actual
special-unitary subgroup. No orthogonality or existence assertion is included
in this condition. Orthogonalization must preserve these same lines.

Source: GLS4, Chapter 4, Lemma 3.11(a),
`refs/KGroup/GLS4/Chapter4.tex`, lines 585–603.
-/

@[expose] public section

open Matrix BenderSuzuki.MatrixGroups
open scoped Pointwise LinearAlgebra.Projectivization

namespace UnitaryThree.OddTorusNormalizer.NonabelianFrame
variable {E : Type*} [Field E]

/-- The field cardinality in the even-unitary source forces characteristic two. -/
theorem charTwo_of_card [Finite E] (n : ℕ) (hcard : Nat.card E = (2 ^ n) ^ 2) :
    CharP E 2 := by
  let : Fintype E := Fintype.ofFinite E
  have hc : Fintype.card E = 2 ^ (n * 2) := by
    rw [← Nat.card_eq_fintype_card, hcard, pow_mul]
  exact charP_of_card_eq_prime_pow hc

/-- The literal special-unitary action on the three-dimensional vector space. -/
noncomputable def naturalRepresentation (J : HermitianForm 3 E) :
    Representation E J.specialSubgroup (Fin 3 → E) :=
  (Representation.generalLinearNatural 3).comp J.specialSubgroup.subtype

/-- The natural action retains all special-unitary matrices, including scalars. -/
theorem naturalRepresentation_injective (J : HermitianForm 3 E) :
    Function.Injective (naturalRepresentation J) :=
  (Representation.generalLinearNatural_injective 3).comp Subtype.val_injective

/-- The projective column lines of an arbitrary invertible matrix are permuted
by the given subgroup, before imposing any condition on their Gram matrix. -/
def PreservesLines (J : HermitianForm 3 E) (K : Subgroup J.specialSubgroup)
    (C : GL (Fin 3) E) : Prop :=
  ∀ g ∈ K, g.val • (C • Set.range (coordinateLine (E := E))) =
    C • Set.range (coordinateLine (E := E))

end UnitaryThree.OddTorusNormalizer.NonabelianFrame
