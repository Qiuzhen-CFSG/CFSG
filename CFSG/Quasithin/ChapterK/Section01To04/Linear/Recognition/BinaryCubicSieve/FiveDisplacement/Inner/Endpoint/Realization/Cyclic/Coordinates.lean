module
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.Endpoint.Realization.Cyclic.Data
public import Theory.Representation.SL5Adjoint.Simplicity

/-!
# Coordinates for the literal binary SL₅ trace kernel

The twenty off-diagonal matrix units and four differences Eᵢᵢ − E₄₄ give
coordinates on the actual trace kernel. The existing trace-zero expansion
proves reconstruction. Kernel-checked multiplication verifies the five
generator action tables on these matrices, independently of their target
orbit vectors. These coordinates define the linear map used in `Cyclic`.

Source: GM, *Classification of 2F-modules, II*, Lemma 4.5 step 2, pp.23–24.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Representation Matrix
open Representation.SL5TenDimensional.Classification
open Representation.SL5TenDimensional.Classification.Separated
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.Endpoint.Cyclic
def coordinateIndex : Fin 24 → Fin 5 × Fin 5 :=
  ![(0, 1), (0, 2), (0, 3), (0, 4), (1, 0), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 3), (2, 4), (3, 0), (3, 1), (3, 2), (3, 4), (4, 0), (4, 1), (4, 2), (4, 3), (0, 0), (1, 1), (2, 2), (3, 3)]
def basisVector : Fin 24 → SL5Adjoint.Space :=
  ![SL5Adjoint.root 0 1 (by decide),
    SL5Adjoint.root 0 2 (by decide),
    SL5Adjoint.root 0 3 (by decide),
    SL5Adjoint.root 0 4 (by decide),
    SL5Adjoint.root 1 0 (by decide),
    SL5Adjoint.root 1 2 (by decide),
    SL5Adjoint.root 1 3 (by decide),
    SL5Adjoint.root 1 4 (by decide),
    SL5Adjoint.root 2 0 (by decide),
    SL5Adjoint.root 2 1 (by decide),
    SL5Adjoint.root 2 3 (by decide),
    SL5Adjoint.root 2 4 (by decide),
    SL5Adjoint.root 3 0 (by decide),
    SL5Adjoint.root 3 1 (by decide),
    SL5Adjoint.root 3 2 (by decide),
    SL5Adjoint.root 3 4 (by decide),
    SL5Adjoint.root 4 0 (by decide),
    SL5Adjoint.root 4 1 (by decide),
    SL5Adjoint.root 4 2 (by decide),
    SL5Adjoint.root 4 3 (by decide),
    SL5Adjoint.diagonal 0, SL5Adjoint.diagonal 1, SL5Adjoint.diagonal 2, SL5Adjoint.diagonal 3]

def coordinate (b : Fin 24) : SL5Adjoint.Space →ₗ[ZMod 2] ZMod 2 where
  toFun X := X.val (coordinateIndex b).1 (coordinateIndex b).2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coordinate_basis (b c : Fin 24) :
    coordinate b (basisVector c) = if b = c then 1 else 0 := by
  revert b c
  decide +kernel

theorem basis_expansion (X : SL5Adjoint.Space) :
    X = ∑ b, coordinate b X • basisVector b := by
  calc
    X = (∑ i : Fin 5, ∑ j : Fin 5,
        if hij : i ≠ j then X.val i j • SL5Adjoint.root i j hij else 0) +
        ∑ i : Fin 4, X.val i.castSucc i.castSucc • SL5Adjoint.diagonal i :=
      SL5Adjoint.traceZero_expansion X
    _ = _ := by
      simp [coordinate, coordinateIndex, basisVector, Fin.sum_univ_succ, add_assoc]

theorem generator_sq (k : Fin 5) : generator k * generator k = 1 := by
  revert k
  decide +kernel

theorem action_basis (k : Fin 5) (b : Fin 24) :
    SL5Adjoint.action (generator k) (basisVector b) =
      ((actionIndices k b).map basisVector).sum := by
  apply Subtype.ext
  rw [SL5Adjoint.action_val, inv_eq_of_mul_eq_one_right (generator_sq k)]
  revert k b
  decide +kernel

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem ext_basis (f g : SL5Adjoint.Space →ₗ[ZMod 2] V)
    (h : ∀ b, f (basisVector b) = g (basisVector b)) : f = g := by
  ext X
  rw [basis_expansion X]
  simp only [map_sum, map_smul, h]

def linearMap (σ : Representation (ZMod 2) Group V) (v : V) :
    SL5Adjoint.Space →ₗ[ZMod 2] V :=
  ∑ b, (coordinate b).smulRight (imageVector σ v b)

theorem linearMap_basis (σ : Representation (ZMod 2) Group V) (v : V) (b : Fin 24) :
    linearMap σ v (basisVector b) = imageVector σ v b := by
  simp [linearMap, coordinate_basis]

theorem highestRoot_basis : SL5Adjoint.highestRoot = basisVector 3 := rfl

theorem imageVector_highest (σ : Representation (ZMod 2) Group V) (v : V) :
    imageVector σ v 3 = v := by
  change σ (representative 3) v = v
  have hr : representative 3 = 1 := by decide +kernel
  rw [hr]
  simp


end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.Endpoint.Cyclic
