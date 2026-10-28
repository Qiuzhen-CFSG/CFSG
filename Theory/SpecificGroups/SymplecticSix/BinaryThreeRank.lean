module

public import Theory.SpecificGroups.SymplecticSix.EvenProjective
public import Theory.GroupTheory.PrimeRankWitness
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Algebra.Field.ZMod

/-!
# A rank-three elementary abelian subgroup in PSp₆(2)

Each symplectic plane admits the order-three rotation with matrix
`!![0, 1; 1, 1]`. Three independent rotations give an injective homomorphism
from `(C₃)³` into the standard six-dimensional symplectic matrix group.
Block-diagonal multiplication and reindexing assemble the small plane checks;
there is no enumeration of the ambient group. The already proved triviality
of its center in characteristic two makes the literal projective quotient map
injective as well. The elementary abelian witness theorem then gives 3-rank
at least three.

This is the intrinsic rank obstruction used for the Co₂ and Co₃ centralizer
sections in Aschbacher–Smith A.2.15(2) and A.2.19 (`refs/quasithin.pdf`, printed
pp. 37–41), with the sections identified in GLS3 Tables 5.3j and 5.3k.
-/

public section

open Matrix
namespace Theory.SpecificGroups.SymplecticSix.BinaryThreeRank

private def rotation (a : ZMod 3) : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  if a = 0 then 1 else if a = 1 then !![0, 1; 1, 1] else !![1, 1; 1, 0]

private theorem rotation_zero : rotation 0 = 1 := by decide
private theorem rotation_add : ∀ a b, rotation (a+b) = rotation a * rotation b := by decide
private theorem rotation_injective : Function.Injective rotation := by decide

private def planeForm : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![0, 1; 1, 0]
private theorem rotation_preserves : ∀ a, (rotation a)ᵀ * planeForm * rotation a = planeForm :=
  by decide

private def indices : (Fin 2 × Fin 3) ≃ (Fin 3 ⊕ Fin 3) where
  toFun x := if x.1 = 0 then .inl x.2 else .inr x.2
  invFun x := match x with | .inl i => (0,i) | .inr i => (1,i)
  left_inv := by rintro ⟨i,j⟩; fin_cases i <;> rfl
  right_inv := by intro i; cases i <;> rfl

private def reindexBlocks : (Fin 3 → Matrix (Fin 2) (Fin 2) (ZMod 2)) →+*
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  (Matrix.reindexAlgEquiv (ZMod 2) (ZMod 2) indices).toRingEquiv.toRingHom.comp (Matrix.blockDiagonalRingHom (Fin 2) (Fin 3) (ZMod 2))

private theorem reindexBlocks_injective : Function.Injective reindexBlocks :=
  (Matrix.reindexAlgEquiv (ZMod 2) (ZMod 2) indices).injective.comp Matrix.blockDiagonal_injective

private theorem reindexBlocks_transpose (A : Fin 3 → Matrix (Fin 2) (Fin 2) (ZMod 2)) :
    reindexBlocks (fun i => (A i)ᵀ) = (reindexBlocks A)ᵀ := by
  change (Matrix.blockDiagonal (fun i => (A i)ᵀ)).submatrix indices.symm indices.symm = _
  rw [← Matrix.blockDiagonal_transpose]
  rfl

private theorem reindexBlocks_form : reindexBlocks (fun _ => planeForm) = Matrix.J (Fin 3) (ZMod 2) :=
  by decide

/-- Independent order-three rotations on the three hyperbolic planes. -/
def embedding : (Fin 3 → (Multiplicative (ZMod 3))) →* Sp (ZMod 2) where
  toFun a := ⟨reindexBlocks (fun i => rotation (a i).toAdd), by
    apply SymplecticGroup.mem_iff'.mpr
    rw [← reindexBlocks_form, ← reindexBlocks_transpose, ← map_mul, ← map_mul]
    congr 1
    funext i
    exact rotation_preserves _⟩
  map_one' := by
    apply Subtype.ext
    change reindexBlocks (fun _ => rotation 0) = 1
    simp_rw [rotation_zero]
    exact map_one reindexBlocks
  map_mul' a b := by
    apply Subtype.ext
    change reindexBlocks (fun i => rotation ((a i).toAdd + (b i).toAdd)) = _
    simp_rw [rotation_add]
    exact map_mul reindexBlocks _ _

/-- Faithfulness is visible on each individual plane. -/
theorem embedding_injective : Function.Injective embedding := by
  intro a b h
  have h' := reindexBlocks_injective (congrArg Subtype.val h)
  funext i
  exact congrArg Multiplicative.ofAdd (rotation_injective (congrFun h' i))

/-- Projectivization retains every element of this elementary abelian subgroup. -/
def projectiveEmbedding : (Fin 3 → (Multiplicative (ZMod 3))) →* PSp (ZMod 2) :=
  EvenProjective.equiv.toMonoidHom.comp embedding

/-- This is the literal quotient map restricted to the constructed subgroup. -/
theorem projectiveEmbedding_apply (a : Fin 3 → Multiplicative (ZMod 3)) :
    projectiveEmbedding a = QuotientGroup.mk' (Subgroup.center (Sp (ZMod 2))) (embedding a) :=
  EvenProjective.equiv_apply _

/-- The quotient is faithful on the constructed elementary abelian subgroup. -/
theorem projectiveEmbedding_injective : Function.Injective projectiveEmbedding :=
  EvenProjective.equiv.injective.comp embedding_injective

/-- The embedded group is elementary abelian of order 27. -/
theorem primeRank_three_ge : 3 ≤ primeRank 3 (PSp (ZMod 2)) := by
  have hp : ∀ a : Fin 3 → (Multiplicative (ZMod 3)), a ^ 3 = 1 := by
    intro a
    funext i
    change Multiplicative.ofAdd (3 • (a i).toAdd) = Multiplicative.ofAdd 0
    exact congrArg Multiplicative.ofAdd (ZModModule.char_nsmul_eq_zero 3 (a i).toAdd)
  have hc : Nat.card (Fin 3 → (Multiplicative (ZMod 3))) = 3 ^ 3 := by
    simp [Nat.card_eq_fintype_card]
  exact primeRank_ge_of_elementary_embedding hp hc projectiveEmbedding
    projectiveEmbedding_injective

end Theory.SpecificGroups.SymplecticSix.BinaryThreeRank
