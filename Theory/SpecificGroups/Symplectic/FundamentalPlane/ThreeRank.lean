module

public import Mathlib.LinearAlgebra.SymplecticGroup
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Theory.SpecificGroups.Symplectic.FundamentalPlane
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Algebra.Field.ZMod

/-!
# Independent cubic rotations in the complementary symplectic group

The matrix [[0,−1],[1,−1]] has exact order three over every field. Place one
copy on each hyperbolic plane and retain the reindexing to Mathlib's `J`.
This gives 3-rank at least `k` in Sp₂ₖ. The actual complementary embedding
puts these rotations inside the literal residual of the fundamental SL₂
centralizer, giving the 3-rank witness used in A.2.17, printed p.39.

This is the arbitrary-rank version of the explicit three-plane construction
in `Theory/SpecificGroups/SymplecticSix/ThreeRank.lean`.
-/

public section

open Matrix

namespace Theory.SpecificGroups.Symplectic.FundamentalPlane.ThreeRank
variable {F : Type*} [Field F] {k : ℕ}
private def rotation (a : ZMod 3) : Matrix (Fin 2) (Fin 2) F :=
  ![1, !![0, -1; 1, -1], !![-1, 1; -1, 0]] a

private theorem rotation_zero : rotation (F := F) 0 = 1 := by simp [rotation]
private theorem rotation_add (a b : ZMod 3) :
    rotation (F := F) (a+b) = rotation a * rotation b := by
  fin_cases a <;> fin_cases b <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [rotation, Matrix.mul_apply, Fin.sum_univ_two] <;> rfl
private theorem rotation_injective : Function.Injective (rotation (F := F)) := by
  intro a b h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 0) h
  have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 1 1) h
  fin_cases a <;> fin_cases b <;> first
    | rfl
    | exact False.elim ((one_ne_zero : (1 : F) ≠ 0) h00)
    | exact False.elim ((one_ne_zero : (1 : F) ≠ 0) h00.symm)
    | exact False.elim ((one_ne_zero : (1 : F) ≠ 0) h11)
    | exact False.elim ((one_ne_zero : (1 : F) ≠ 0) h11.symm)
    | exact False.elim ((neg_ne_zero.mpr one_ne_zero : (-1 : F) ≠ 0) h00)
    | exact False.elim ((neg_ne_zero.mpr one_ne_zero : (-1 : F) ≠ 0) h00.symm)

private def planeForm : Matrix (Fin 2) (Fin 2) F := !![0, -1; 1, 0]
private theorem rotation_preserves (a : ZMod 3) :
    (rotation (F := F) a)ᵀ * planeForm * rotation a = planeForm := by
  fin_cases a <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [rotation, planeForm, Matrix.mul_apply, Fin.sum_univ_two]

private def indices : (Fin 2 × Fin k) ≃ (Fin k ⊕ Fin k) where
  toFun x := if x.1 = 0 then .inl x.2 else .inr x.2
  invFun x := match x with | .inl i => (0,i) | .inr i => (1,i)
  left_inv := by rintro ⟨i,j⟩; fin_cases i <;> rfl
  right_inv := by intro i; cases i <;> rfl

private def reindexBlocks : (Fin k → Matrix (Fin 2) (Fin 2) F) →+*
    Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) F :=
  (Matrix.reindexAlgEquiv F F indices).toRingEquiv.toRingHom.comp
    (Matrix.blockDiagonalRingHom (Fin 2) (Fin k) F)

private theorem reindexBlocks_injective : Function.Injective (reindexBlocks (F := F) (k := k)) :=
  (Matrix.reindexAlgEquiv F F indices).injective.comp Matrix.blockDiagonal_injective

private theorem reindexBlocks_transpose (A : Fin k → Matrix (Fin 2) (Fin 2) F) :
    reindexBlocks (fun i => (A i)ᵀ) = (reindexBlocks A)ᵀ := by
  change (Matrix.blockDiagonal (fun i => (A i)ᵀ)).submatrix indices.symm indices.symm = _
  rw [← Matrix.blockDiagonal_transpose]
  rfl

private theorem reindexBlocks_form :
    reindexBlocks (fun _ => planeForm) = Matrix.J (Fin k) F := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [reindexBlocks, indices, planeForm, Matrix.J, Matrix.blockDiagonal,
      Matrix.reindexAlgEquiv, Matrix.reindex, Matrix.one_apply]
  split_ifs <;> simp

/-- Independent order-three rotations on the standard hyperbolic planes. -/
def embedding : (Fin k → Multiplicative (ZMod 3)) →* Matrix.symplecticGroup (Fin k) F where
  toFun a := ⟨reindexBlocks (fun i => rotation (a i).toAdd), by
    apply SymplecticGroup.mem_iff'.mpr
    rw [← reindexBlocks_form, ← reindexBlocks_transpose, ← map_mul, ← map_mul]
    congr 1
    funext i
    exact rotation_preserves _⟩
  map_one' := by
    apply Subtype.ext
    change reindexBlocks (fun _ => rotation (F := F) 0) = 1
    simp_rw [rotation_zero]
    exact map_one reindexBlocks
  map_mul' a b := by
    apply Subtype.ext
    change reindexBlocks (fun i => rotation (F := F) ((a i).toAdd + (b i).toAdd)) = _
    simp_rw [rotation_add]
    exact map_mul reindexBlocks _ _

/-- Each plane determines its own rotation parameter. -/
theorem embedding_injective : Function.Injective (embedding (F := F) (k := k)) := by
  intro a b h
  have h' := reindexBlocks_injective (congrArg Subtype.val h)
  funext i
  exact congrArg Multiplicative.ofAdd (rotation_injective (congrFun h' i))

/-- The explicit elementary abelian subgroup has order `3^k` over every finite field. -/
theorem rank_le_primeRank [Finite F] :
    k ≤ primeRank 3 (Matrix.symplecticGroup (Fin k) F) := by
  have hp : ∀ a : Fin k → Multiplicative (ZMod 3), a ^ 3 = 1 := by
    intro a
    funext i
    change Multiplicative.ofAdd (3 • (a i).toAdd) = Multiplicative.ofAdd 0
    exact congrArg Multiplicative.ofAdd (ZModModule.char_nsmul_eq_zero 3 (a i).toAdd)
  have hc : Nat.card (Fin k → Multiplicative (ZMod 3)) = 3 ^ k := by
    simp [Nat.card_eq_fintype_card]
  exact primeRank_ge_of_elementary_embedding hp hc embedding embedding_injective
/-- The cubic rotations lie in the literal defining-characteristic residual. -/
theorem rank_le_primeRank_residual [Finite F] (k r : ℕ) [CharP F r] :
    k ≤ primeRank 3 (residual (F := F) k r) := by
  have hp : ∀ a : Fin k → Multiplicative (ZMod 3), a ^ 3 = 1 := by
    intro a
    funext i
    change Multiplicative.ofAdd (3 • (a i).toAdd) = Multiplicative.ofAdd 0
    exact congrArg Multiplicative.ofAdd (ZModModule.char_nsmul_eq_zero 3 (a i).toAdd)
  have hc : Nat.card (Fin k → Multiplicative (ZMod 3)) = 3 ^ k := by
    simp [Nat.card_eq_fintype_card]
  exact primeRank_ge_of_elementary_embedding hp hc
    ((tailToResidual k r).comp embedding)
    ((tailToResidual_injective k r).comp embedding_injective)

end Theory.SpecificGroups.Symplectic.FundamentalPlane.ThreeRank
