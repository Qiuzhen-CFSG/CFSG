module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.OrderBound.Coordinates
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.OrderBound.Blocks

/-!
# The full diagonal action of the literal max4 subgroup

The certified generator flag extends to the actual subgroup closure, including
inverses by finiteness. Taking all fifteen diagonal blocks gives an actual
homomorphism to binary matrix units. Its kernel is a two-group by the faithful
triangular representation criterion. The image is exactly the group generated
by the two explicitly displayed diagonal matrices.

This supplies the kernel part of the local order calculation, independently of
the selected epimorphism onto S5 × SL3(2). Bounding this simultaneous diagonal
image is a separate finite calculation. Source: ATLAS J4G1-max4W1, attributed
in SymmetricLinear.Model; Aschbacher--Smith, printed p.511/PDF p.528.
-/

@[expose] public section
namespace Janko4.LocalStructure.SymmetricLinear.OrderBound

/-- Conjugation by the already certified basis, on the literal subgroup. -/
abbrev representation : max4Subgroup →* BinaryMatrix :=
  CharacteristicTwo.coordinateHom CharacteristicTwo.basis_mul_basisInverse
    CharacteristicTwo.basisInverse_mul_basis

theorem representation_apply (g : max4Subgroup) :
    representation g = CharacteristicTwo.coordinates g :=
  CharacteristicTwo.coordinateHom_apply _ _ g

theorem representation_injective : Function.Injective representation :=
  CharacteristicTwo.coordinateHom_injective _ _

/-- The literal ATLAS outputs generate the intrinsic carrier. -/
theorem closure_generators :
    Subgroup.closure {CharacteristicTwo.first, CharacteristicTwo.second} = ⊤ := by
  have hp : max4Subgroup.subtype ⁻¹' {(max4Program a b).1, (max4Program a b).2} =
      {CharacteristicTwo.first, CharacteristicTwo.second} := by
    ext g
    change ((g : Model) = (max4Program a b).1 ∨
      (g : Model) = (max4Program a b).2) ↔
      g = CharacteristicTwo.first ∨ g = CharacteristicTwo.second
    simp only [Subtype.ext_iff]
    rfl
  rw [← hp]
  exact Subgroup.closure_preimage_eq_top _

/-- The entire actual subgroup preserves the fifteen-block flag. -/
theorem representation_triangular (g : max4Subgroup) :
    (representation g).BlockTriangular (OrderDual.toDual ∘ blockIndex) := by
  apply BinaryBlockOrder.triangular_of_generators representation blockIndex
    {CharacteristicTwo.first, CharacteristicTwo.second} closure_generators ?_ g
  intro s hs
  rcases hs with rfl | rfl
  · simpa only [representation_apply, coordinates_first] using first_triangular
  · simpa only [representation_apply, coordinates_second] using second_triangular

/-- The simultaneous action on every diagonal block, as an actual homomorphism. -/
def diagonalHom : max4Subgroup →* BinaryMatrixˣ :=
  BinaryBlockOrder.diagonalHom representation blockIndex representation_triangular

/-- The full simultaneous diagonal image; no group identification is assumed. -/
def diagonalImage : Subgroup BinaryMatrixˣ := diagonalHom.range

/-- The first actual diagonal generator. -/
def diagonalFirst : BinaryMatrixˣ := diagonalHom CharacteristicTwo.first
/-- The second actual diagonal generator. -/
def diagonalSecond : BinaryMatrixˣ := diagonalHom CharacteristicTwo.second

theorem diagonalHom_matrix (g : max4Subgroup) :
    (diagonalHom g : BinaryMatrix) = Matrix.blockDiagonalPart blockIndex (representation g) := rfl

theorem diagonalFirst_matrix : (diagonalFirst : BinaryMatrix) =
    Matrix.blockDiagonalPart blockIndex (decodeRows firstRows) := by
  rw [diagonalFirst, diagonalHom_matrix, representation_apply, coordinates_first]

theorem diagonalSecond_matrix : (diagonalSecond : BinaryMatrix) =
    Matrix.blockDiagonalPart blockIndex (decodeRows secondRows) := by
  rw [diagonalSecond, diagonalHom_matrix, representation_apply, coordinates_second]

/-- The finite counting problem concerns exactly these two explicit matrices. -/
theorem diagonalImage_eq_closure :
    diagonalImage = Subgroup.closure {diagonalFirst, diagonalSecond} := by
  rw [diagonalImage, MonoidHom.range_eq_map, ← closure_generators,
    MonoidHom.map_closure]
  simp only [Set.image_insert_eq, Set.image_singleton, diagonalFirst, diagonalSecond]

/-- The kernel on all blocks is unconditionally a two-group. -/
theorem diagonalHom_kernel_isPGroup : IsPGroup 2 diagonalHom.ker :=
  BinaryBlockOrder.kernel_isPGroup representation blockIndex representation_triangular
    representation_injective blockIndex_monotone

/-- A concrete finite matrix representation containing the two diagonal
outputs supplies a divisibility bound for their entire simultaneous image. -/
theorem diagonalImage_card_dvd_of_cover {H : Type*} [Group H]
    (r : H →* BinaryMatrixˣ) (hfirst : diagonalFirst ∈ r.range)
    (hsecond : diagonalSecond ∈ r.range) : Nat.card diagonalImage ∣ Nat.card H := by
  apply dvd_trans _ (Subgroup.card_range_dvd r)
  apply Subgroup.card_dvd_of_le
  rw [diagonalImage_eq_closure]
  apply (Subgroup.closure_le _).mpr
  intro s hs
  rcases hs with rfl | rfl
  · exact hfirst
  · exact hsecond

end Janko4.LocalStructure.SymmetricLinear.OrderBound
