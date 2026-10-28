module

public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.Orbits.Stabilizer
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# The length of the nonsingular exterior orbit

The literal stabilizer of e₀∧e₁ + e₂∧e₃ has the already constructed
shear kernel of order 16 and quotient S₆. Its index in SL₅(2) is therefore
868 = 4 · 217. This orbit contains more than half of the 1024 exterior
vectors, which lets the full normalizer preserve it and permits the
Sylow rechoice in the ambient application.

Source: Aschbacher--Smith, 12.5.5(3) and 12.5.9(1), printed pp.819,821.
-/

public section
open Subgroup
namespace Representation.SL5ExteriorSquare
open SL5TenDimensional

/-- The binary determinant is automatically one, so the usual GL count applies. -/
theorem card_specialLinearFive : Nat.card Group = 9999360 := by
  let e := MulEquiv.ofBijective Matrix.SpecialLinearGroup.toGL
    ⟨Matrix.SpecialLinearGroup.toGL_injective,
      BinaryLinear.OuterCyclic.binary_toGL_surjective 5⟩
  rw [Nat.card_congr e.toEquiv, Matrix.card_GL_field, ZMod.card]
  norm_num [Fin.prod_univ_succ]

/-- Count the actual stabilizer through its actual shear quotient. -/
theorem card_nondecomposableStabilizer : Nat.card nondecomposableStabilizer = 11520 := by
  have hs : Nat.card (shearSubgroup.subgroupOf nondecomposableStabilizer) = 16 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe shearSubgroup_le_nondecomposableStabilizer).toEquiv]
    exact card_shearSubgroup
  rw [card_eq_card_quotient_mul_card_subgroup
    (shearSubgroup.subgroupOf nondecomposableStabilizer), hs,
    Nat.card_congr nondecomposableQuotientEquivSymmetricSix.toEquiv]
  norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]

/-- The nonsingular orbit length, whose two-part is four. -/
theorem index_nondecomposableStabilizer : nondecomposableStabilizer.index = 868 := by
  have h := nondecomposableStabilizer.card_mul_index
  rw [card_specialLinearFive, card_nondecomposableStabilizer] at h
  omega

/-- The genuine exterior square has 1024 vectors. -/
theorem card_exteriorSquare : Nat.card V = 1024 := by
  rw [Nat.card_congr coordinates.toEquiv]
  norm_num [Nat.card_fun, Nat.card_fin, Nat.card_zmod]

end Representation.SL5ExteriorSquare
