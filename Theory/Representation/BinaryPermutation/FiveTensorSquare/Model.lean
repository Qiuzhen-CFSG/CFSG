module

public import Theory.Representation.BinaryPermutationAlternatingActions
public import Theory.Representation.QuadraticFourGroup.TensorClassification.ExternalTensor
public import Mathlib.GroupTheory.RegularWreathProduct
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The deleted five-letter tensor square and its wreath action

The four-dimensional augmentation core on five letters is tensored with
itself over the binary field. The two symmetric groups act on the two
tensor coordinates, and the outer involution exchanges the inputs. This
is the sixteen-dimensional deleted-square alternative in the proof of
Aschbacher–Smith D.3.7, printed pp.197–199.
-/

@[expose] public noncomputable section
open scoped TensorProduct
open Representation
namespace BinaryPermutation.FiveTensorSquare

abbrev C := core (Fin 5)
abbrev V := C ⊗[ZMod 2] C
abbrev Alt := alternatingGroup (Fin 5)
abbrev Sym := Equiv.Perm (Fin 5)
abbrev C2 := Multiplicative (ZMod 2)
abbrev Wreath := RegularWreathProduct Sym C2
abbrev δ := alternatingCoreRepresentation (Fin 5)

/-- The actual external tensor of the two deleted A₅ modules. -/
def deletedAction : Representation (ZMod 2) (Alt × Alt) V :=
  QuadraticFourGroup.TensorClassification.externalTensor δ δ

def swapIndex : C2 := Multiplicative.ofAdd 1

theorem index_cases (i : C2) : i = 1 ∨ i = swapIndex := by
  revert i
  decide

@[simp] theorem swapIndex_ne_one : swapIndex ≠ 1 := by decide
@[simp] theorem swapIndex_inv : swapIndex⁻¹ = swapIndex := by decide
@[simp] theorem swapIndex_mul_self : swapIndex * swapIndex = 1 := by decide

def coreEquiv (g : Sym) : C ≃ₗ[ZMod 2] C :=
  LinearEquiv.ofBijective (coreRepresentation (Fin 5) g)
    ((coreRepresentation (Fin 5)).apply_bijective g)

/-- Output-indexed base coordinates, with the nonidentity shift swapping inputs. -/
def tensorWreathMap (w : Wreath) : V ≃ₗ[ZMod 2] V :=
  if w.right = 1 then TensorProduct.congr (coreEquiv (w.left 1))
    (coreEquiv (w.left swapIndex))
  else (TensorProduct.comm (ZMod 2) C C).trans
    (TensorProduct.congr (coreEquiv (w.left 1)) (coreEquiv (w.left swapIndex)))

theorem tensorWreathMap_tmul (w : Wreath) (u v : C) :
    tensorWreathMap w (u ⊗ₜ[ZMod 2] v) =
      if w.right = 1 then
        coreRepresentation (Fin 5) (w.left 1) u ⊗ₜ[ZMod 2]
          coreRepresentation (Fin 5) (w.left swapIndex) v
      else coreRepresentation (Fin 5) (w.left 1) v ⊗ₜ[ZMod 2]
          coreRepresentation (Fin 5) (w.left swapIndex) u := by
  by_cases h : w.right = 1 <;> simp [tensorWreathMap, h, coreEquiv]

def tensorWreathHom : Wreath →* (V ≃ₗ[ZMod 2] V) where
  toFun := tensorWreathMap
  map_one' := by
    apply LinearEquiv.toLinearMap_injective
    ext u v
    simp [tensorWreathMap_tmul]
  map_mul' a b := by
    apply LinearEquiv.toLinearMap_injective
    ext u v
    change tensorWreathMap (a*b) (u ⊗ₜ[ZMod 2] v) =
      tensorWreathMap a (tensorWreathMap b (u ⊗ₜ[ZMod 2] v))
    rcases index_cases a.right with ha | ha <;>
      rcases index_cases b.right with hb | hb <;>
      simp [tensorWreathMap_tmul, RegularWreathProduct.mul_left,
        RegularWreathProduct.mul_right, ha, hb, Module.End.mul_apply]

/-- The literal sixteen-dimensional binary wreath representation. -/
def tensorWreathAction : Representation (ZMod 2) Wreath V where
  toFun w := (tensorWreathHom w).toLinearMap
  map_one' := by
    change (tensorWreathHom 1).toLinearMap = 1
    rw [map_one]
    rfl
  map_mul' a b := by
    change (tensorWreathHom (a*b)).toLinearMap = _
    rw [map_mul]
    rfl

theorem tensorWreathAction_tmul (w : Wreath) (u v : C) :
    tensorWreathAction w (u ⊗ₜ[ZMod 2] v) =
      if w.right = 1 then
        coreRepresentation (Fin 5) (w.left 1) u ⊗ₜ[ZMod 2]
          coreRepresentation (Fin 5) (w.left swapIndex) v
      else coreRepresentation (Fin 5) (w.left 1) v ⊗ₜ[ZMod 2]
          coreRepresentation (Fin 5) (w.left swapIndex) u :=
  tensorWreathMap_tmul w u v

/-- The two coordinate permutations as a wreath base element. -/
def base (g : Sym × Sym) : Wreath :=
  ⟨fun i => if i = 1 then g.1 else g.2, 1⟩

def baseHom : Sym × Sym →* Wreath where
  toFun := base
  map_one' := by ext i <;> simp [base]
  map_mul' a b := by
    apply RegularWreathProduct.ext
    · funext i
      by_cases h : i = 1 <;> simp [base, RegularWreathProduct.mul_left, h]
    · rfl

def alternatingBase : Alt × Alt →* Wreath :=
  baseHom.comp ((alternatingGroup (Fin 5)).subtype.prodMap
    (alternatingGroup (Fin 5)).subtype)

theorem tensorWreathAction_base (g : Sym × Sym) (u v : C) :
    tensorWreathAction (base g) (u ⊗ₜ[ZMod 2] v) =
      coreRepresentation (Fin 5) g.1 u ⊗ₜ[ZMod 2]
        coreRepresentation (Fin 5) g.2 v := by
  simp [tensorWreathAction_tmul, base]

/-- The alternating base restriction is the deleted tensor square, literally. -/
theorem tensorWreathAction_comp_alternatingBase :
    tensorWreathAction.comp alternatingBase = deletedAction := by
  ext g u v
  exact tensorWreathAction_base (g.1.val,g.2.val) u v

theorem finrank_V : Module.finrank (ZMod 2) V = 16 := by
  rw [Module.finrank_tensorProduct, finrank_core, Fintype.card_fin]

end BinaryPermutation.FiveTensorSquare
