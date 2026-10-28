module
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.SmallMovers.Fixed
public import Theory.Representation.SymplecticFourOrthogonalCover.Roots
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Sylow coordinates in the genuine derived symplectic group

Over a nonbinary field the full symplectic group is perfect, so its literal
unipotent subgroup embeds in the derived actor used by the central-cover
interface. The natural binary moving index is exactly the coordinate index.

This connects the MS93 (5.4) finite-model small-mover classification to the
actual quotient map and cover projection of the local group.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.SmallMovers
variable {F : Type*} [Field F] [CharP F 2] [Finite F] [Algebra (ZMod 2) F]

noncomputable def derivedEmbedding (hF : 2 < Nat.card F) :
    unipotent (F := F) →* Representation.SymplecticFourOrthogonalCover.L (K := F) :=
  (unipotent (F := F)).subtype.codRestrict (commutator _) (by
    intro g
    rw [Representation.OneCohomology.SymplecticFour.LargeField.commutator_eq_top hF]
    trivial)

omit [Algebra (ZMod 2) F] in
theorem derivedEmbedding_injective (hF : 2 < Nat.card F) :
    Function.Injective (derivedEmbedding (F := F) hF) := by
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z : Representation.SymplecticFourOrthogonalCover.L (K := F) => z.val) h

theorem derivedEmbedding_movingIndex (hF : 2 < Nat.card F)
    (E : Subgroup (unipotent (F := F))) :
    2 ^ fixedCodim (Representation.SymplecticFourOrthogonalCover.binaryNatural (K := F))
      (E.map (derivedEmbedding hF)) = movingIndex E := by
  rw [←binary_movingIndex]
  congr 1
  have he : (Representation.SymplecticFourOrthogonalCover.binaryNatural (K := F)).comp
      (derivedEmbedding hF) = restrictScalars (k := ZMod 2) natural := rfl
  rw [←he,fixedCodim,fixedCodim,fixedSpace_comp_map]
end Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.SmallMovers
