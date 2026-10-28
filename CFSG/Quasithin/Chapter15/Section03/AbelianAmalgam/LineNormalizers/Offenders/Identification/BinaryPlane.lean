module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.SmallModels.Coordinates
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.BestReduction.Fields

/-!
# Matching the binary matrix plane with the permutation plane

The six matrices are obtained by permuting the three coordinates of the
binary even-weight plane. Their multiplication and the intertwining map are
checked on these finite carriers. Entrywise field transport then retains the
same actor and module coordinates for a field proved to have two elements.
This supplies the literal model comparison used at the end of 15.3.67;
a group isomorphism alone would not identify its commutator or fixed spaces.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 15.3.67, printed p.1154, with the natural-module conventions of B.5.1.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.Identification.BinaryPlane
abbrev Plane := Fin 2 → ZMod 2
abbrev Core := BinaryPermutation.core (Fin 3)
abbrev SL := Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)
private instance : DecidablePred (fun v : Fin 3 → ZMod 2 => v ∈ Core) := by
  intro v
  change Decidable (∑ i, v i = 0)
  infer_instance
private instance : Fintype Core := Subtype.fintype _

def coordinates : Plane ≃ₗ[ZMod 2] Core where
  toFun v := ⟨![v 0, v 1, v 0 + v 1], by revert v; decide +kernel⟩
  invFun v := ![v.val 0, v.val 1]
  map_add' := by decide +kernel
  map_smul' := by decide +kernel
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def matrix (g : Equiv.Perm (Fin 3)) : SL :=
  ⟨!![(![1,0,1] : Fin 3 → ZMod 2) (g⁻¹ 0), (![0,1,1] : Fin 3 → ZMod 2) (g⁻¹ 0);
      (![1,0,1] : Fin 3 → ZMod 2) (g⁻¹ 1), (![0,1,1] : Fin 3 → ZMod 2) (g⁻¹ 1)],
    by revert g; decide +kernel⟩

def matrixHom : Equiv.Perm (Fin 3) →* SL where
  toFun := matrix
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

theorem matrix_bijective : Function.Bijective matrixHom := by decide +kernel

noncomputable def actor : SL ≃* Equiv.Perm (Fin 3) :=
  (MulEquiv.ofBijective matrixHom matrix_bijective).symm

private theorem coordinates_matrix : ∀ (g : Equiv.Perm (Fin 3)) (v : Plane),
    coordinates (specialLinearNatural 2 (matrix g) v) =
      BinaryPermutation.coreRepresentation (Fin 3) g (coordinates v) := by decide +kernel

theorem coordinates_action (g : SL) (v : Plane) :
    coordinates (specialLinearNatural 2 g v) =
      BinaryPermutation.coreRepresentation (Fin 3) (actor g) (coordinates v) := by
  obtain ⟨s, rfl⟩ := matrix_bijective.surjective g
  have he : actor (matrixHom s) = s :=
    (MulEquiv.ofBijective matrixHom matrix_bijective).symm_apply_apply s
  rw [he]
  exact coordinates_matrix s v

variable {F : Type*} [Field F] [Algebra (ZMod 2) F]

noncomputable def fieldCoordinates (e : F ≃+* ZMod 2) : (Fin 2 → F) ≃ₗ[ZMod 2] Plane :=
  LinearEquiv.piCongrRight fun _ =>
    { e.toAddEquiv with map_smul' := ZMod.map_smul e.toAddEquiv }

theorem fieldCoordinates_action (e : F ≃+* ZMod 2)
    (g : Matrix.SpecialLinearGroup (Fin 2) F) (v : Fin 2 → F) :
    fieldCoordinates e ((specialLinearNatural 2).restrictScalars (k := ZMod 2) g v) =
      specialLinearNatural 2 (Atlas.fieldEquivSL 2 e g) (fieldCoordinates e v) := by
  funext i
  change e (∑ j : Fin 2, g.val i j * v j) = ∑ j : Fin 2, e (g.val i j) * e (v j)
  simp only [map_sum, map_mul]

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.Identification.BinaryPlane
