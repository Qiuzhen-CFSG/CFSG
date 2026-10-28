module
public import Theory.Representation.BinaryPermutation.FivePairWreath
public import Theory.Representation.BinaryPermutation.FiveTensorSquare.Model
public import Theory.Representation.FixedPointPermutation

/-!
# The 25-point permutation module of the wreath group

The literal grid action contains the deleted pair and deleted tensor through
equivariant linear maps. Every point vector is the sum of a constant, a
deleted pair vector and a pure deleted tensor. Consequently a permutation
module map separating two point vectors is nonzero on one of these models.

Source: Aschbacher--Smith 10.3.1, printed pp.755--756.
-/

@[expose] public section

open scoped TensorProduct
open Representation
namespace BinaryPermutation.FiveTensorSquare
abbrev Grid := Fin 5 × Fin 5

def gridPoint (g : Wreath) (x : Grid) : Grid :=
  if g.right = 1 then (g.left 1 x.1, g.left swapIndex x.2)
  else (g.left 1 x.2, g.left swapIndex x.1)

instance gridAction : MulAction Wreath Grid where
  smul := gridPoint
  one_smul x := by change gridPoint 1 x = x; simp [gridPoint]
  mul_smul a b x := by
    change gridPoint (a*b) x = gridPoint a (gridPoint b x)
    rcases index_cases a.right with ha | ha <;> rcases index_cases b.right with hb | hb <;>
      simp [gridPoint, RegularWreathProduct.mul_left, RegularWreathProduct.mul_right, ha, hb]

instance grid_transitive : MulAction.IsPretransitive Wreath Grid where
  exists_smul_eq x y := by
    refine ⟨base (Equiv.swap x.1 y.1, Equiv.swap x.2 y.2), ?_⟩
    change gridPoint _ _ = _
    simp [gridPoint, base]

abbrev gridRepresentation : Representation (ZMod 2) Wreath (Grid → ZMod 2) :=
  FixedPointPermutation.action

theorem gridRepresentation_apply_smul (g : Wreath) (f : Grid → ZMod 2) (x : Grid) :
    gridRepresentation g f (g • x) = f x := by
  change f (g⁻¹ • (g • x)) = f x
  rw [inv_smul_smul]

def pairFunctions : (C × C) →ₗ[ZMod 2] (Grid → ZMod 2) where
  toFun v x := v.1.val x.1 + v.2.val x.2
  map_add' u v := by ext x; simp; ring
  map_smul' c v := by ext x; simp; ring

def pairToGrid : FivePair.wreathRepresentation.IntertwiningMap gridRepresentation where
  toLinearMap := pairFunctions
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    funext x
    obtain ⟨y,rfl⟩ := (MulAction.toPerm g).surjective x
    change pairFunctions (FivePair.wreathRepresentation g v) (g • y) =
      gridRepresentation g (pairFunctions v) (g • y)
    rw [gridRepresentation_apply_smul]
    rw [FivePair.wreathRepresentation_apply]
    change pairFunctions (if g.right = 1 then _ else _) (gridPoint g y) = _
    split_ifs with h <;>
      simp [pairFunctions, gridPoint, h, coreRepresentation_apply, representation_apply,
        FivePair.swapIndex, swapIndex, add_comm]

def tensorFunctions : V →ₗ[ZMod 2] (Grid → ZMod 2) := TensorProduct.lift {
  toFun u := {
    toFun v x := u.val x.1 * v.val x.2
    map_add' v w := by ext x; exact mul_add _ _ _
    map_smul' c v := by ext x; simp; ring }
  map_add' u v := by ext w x; exact add_mul _ _ _
  map_smul' c v := by ext w x; simp; ring }

theorem tensorFunctions_tmul (u v : C) (x : Grid) :
    tensorFunctions (u ⊗ₜ[ZMod 2] v) x = u.val x.1 * v.val x.2 := rfl

def tensorToGrid : tensorWreathAction.IntertwiningMap gridRepresentation where
  toLinearMap := tensorFunctions
  isIntertwining' g := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z t hz ht => simp only [LinearMap.comp_apply, map_add] at *; rw [hz,ht]
    | tmul u v =>
      funext x
      obtain ⟨y,rfl⟩ := (MulAction.toPerm g).surjective x
      change tensorFunctions (tensorWreathAction g (u ⊗ₜ[ZMod 2] v)) (g • y) =
        gridRepresentation g (tensorFunctions (u ⊗ₜ[ZMod 2] v)) (g • y)
      rw [gridRepresentation_apply_smul, tensorWreathAction_tmul]
      change tensorFunctions (if g.right = 1 then _ else _) (gridPoint g y) = _
      split_ifs with h <;>
        simp [tensorFunctions_tmul, gridPoint, h, coreRepresentation_apply,
          representation_apply, mul_comm]

def gridCorePoint (i : Fin 5) : C := ⟨Pi.single i 1 + 1, by
  simp [mem_core, Finset.sum_add_distrib]
  decide⟩

theorem grid_single_decomposition (x : Grid) :
    Pi.single x (1 : ZMod 2) = (1 : Grid → ZMod 2) +
      pairToGrid (gridCorePoint x.1,gridCorePoint x.2) +
      tensorToGrid (gridCorePoint x.1 ⊗ₜ[ZMod 2] gridCorePoint x.2) := by
  funext y
  change (Pi.single x (1 : ZMod 2) : Grid → ZMod 2) y = 1 +
    ((gridCorePoint x.1).val y.1 + (gridCorePoint x.2).val y.2) +
      (gridCorePoint x.1).val y.1 * (gridCorePoint x.2).val y.2
  simp only [gridCorePoint, Pi.add_apply, Pi.one_apply]
  rcases x with ⟨i,j⟩
  rcases y with ⟨k,l⟩
  by_cases hi : i = k <;> by_cases hj : j = l <;>
    simp [Prod.mk.injEq, hi, hj] <;> decide

variable {X U : Type*} [Group X] [AddCommGroup U] [Module (ZMod 2) U]

def pairToGrid_comp (e : X →* Wreath) :
    IntertwiningMap (FivePair.wreathRepresentation.comp e) (gridRepresentation.comp e) where
  toLinearMap := pairToGrid.toLinearMap
  isIntertwining' g := pairToGrid.isIntertwining' (e g)

def tensorToGrid_comp (e : X →* Wreath) :
    IntertwiningMap (tensorWreathAction.comp e) (gridRepresentation.comp e) where
  toLinearMap := tensorToGrid.toLinearMap
  isIntertwining' g := tensorToGrid.isIntertwining' (e g)

theorem nonzero_model_restriction (ρ : Representation (ZMod 2) X U) (e : X →* Wreath)
    (f : IntertwiningMap (gridRepresentation.comp e) ρ) (x y : Grid)
    (hxy : f (Pi.single x 1) ≠ f (Pi.single y 1)) :
    (∃ p : IntertwiningMap (FivePair.wreathRepresentation.comp e) ρ, p ≠ 0) ∨
      ∃ t : IntertwiningMap (tensorWreathAction.comp e) ρ, t ≠ 0 := by
  let p := f.comp (pairToGrid_comp e)
  let t := f.comp (tensorToGrid_comp e)
  by_cases hp : p = 0
  · by_cases ht : t = 0
    · exfalso
      have hs (z : Grid) : f (Pi.single z 1) = f (1 : Grid → ZMod 2) := by
        rw [grid_single_decomposition, map_add, map_add]
        change f 1 + p (gridCorePoint z.1, gridCorePoint z.2) +
          t (gridCorePoint z.1 ⊗ₜ[ZMod 2] gridCorePoint z.2) = f 1
        rw [hp, ht]
        simp
      exact hxy ((hs x).trans (hs y).symm)
    · exact Or.inr ⟨t, ht⟩
  · exact Or.inl ⟨p, hp⟩

end BinaryPermutation.FiveTensorSquare
