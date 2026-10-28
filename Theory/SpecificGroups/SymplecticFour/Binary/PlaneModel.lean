module

public import Theory.SpecificGroups.SymplecticFour.Binary.PlaneModel.Coordinates

/-!
# The binary plane stabilizer is C₂ × S₄

The explicit affine-plane coordinates in `PlaneModel.Coordinates` give a
faithful multiplicative map from `Perm (Fin 2) × Perm (Fin 4)` into the
actual matrix stabilizer. The vanishing lower-left block of a stabilizer
matrix and its symplectic equation give exactly the hypotheses of the
coordinate coverage theorem. Thus the map is onto, and its inverse is the
required multiplicative equivalence.

Source: the plane local model for Aschbacher--Smith F.1.12(I)(2),
printed pp.262–264. The identification of the book's `LᵢS` with the concrete
stabilizer is assembled separately.
-/

noncomputable section
namespace Theory.SpecificGroups.SymplecticFour.Binary
open Matrix PlaneModel

private def planeProductMap (x : Equiv.Perm (Fin 2) × Equiv.Perm (Fin 4)) :
    planeParabolic (F := ZMod 2) :=
  ⟨⟨modelMatrix x.1 x.2, modelMatrix_symplectic x.1 x.2⟩,
    (mem_planeParabolic_iff _).mpr (by intro i j; rfl)⟩

private theorem planeProductMap_mul
    (x y : Equiv.Perm (Fin 2) × Equiv.Perm (Fin 4)) :
    planeProductMap (x * y) = planeProductMap x * planeProductMap y := by
  apply Subtype.ext
  apply Subtype.ext
  exact modelMatrix_mul x.1 x.2 y.1 y.2

private def planeProductHom :
    (Equiv.Perm (Fin 2) × Equiv.Perm (Fin 4)) →* planeParabolic (F := ZMod 2) :=
  MonoidHom.mk' planeProductMap planeProductMap_mul

private theorem planeProductHom_injective : Function.Injective planeProductHom := by
  intro x y h
  have hm : modelMatrix x.1 x.2 = modelMatrix y.1 y.2 :=
    congrArg (fun g : planeParabolic (F := ZMod 2) => g.val.val) h
  exact Prod.ext (modelMatrix_injective _ _ _ _ hm).1
    (modelMatrix_injective _ _ _ _ hm).2

private theorem planeProductHom_surjective : Function.Surjective planeProductHom := by
  intro g
  have hz : g.val.val.toBlocks₂₁ = 0 := by
    ext i j
    exact (mem_planeParabolic_iff _).mp g.property i j
  have he := fromBlocks_toBlocks g.val.val
  rw [hz] at he
  have hs := g.val.property
  rw [← he, SymplecticGroup.fromBlocks_mem_iff] at hs
  have hd : g.val.val.toBlocks₁₁ᵀ * g.val.val.toBlocks₂₂ = 1 := by
    simpa only [transpose_zero, zero_mul, sub_zero] using hs.2.2
  obtain ⟨s, p, hm⟩ := modelMatrix_surjective _ _ _ hs.2.1 hd
  refine ⟨(s, p), ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact hm.trans he

/-- The actual binary matrix plane stabilizer, identified with `C₂ × S₄`. -/
public noncomputable def planeParabolicZModEquivProd :
    planeParabolic (F := ZMod 2) ≃* (Equiv.Perm (Fin 2) × Equiv.Perm (Fin 4)) :=
  (MulEquiv.ofBijective planeProductHom
    ⟨planeProductHom_injective, planeProductHom_surjective⟩).symm

end Theory.SpecificGroups.SymplecticFour.Binary
