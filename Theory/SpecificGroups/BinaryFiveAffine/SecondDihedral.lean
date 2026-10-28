module
public import Theory.SpecificGroups.BinaryFiveAffine.Marking
public import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic
/-! # The second marked dihedral axis
The square action on the S₄ factor supplies a second D₈ subgroup, retained
for Sylow alignment in the source normalizer transport. -/
@[expose] public section
namespace BinaryFiveAffine

def squarePermutation : DihedralGroup 4 → Equiv.Perm (Fin 4)
  | .r i => finRotate 4 ^ i.val
  | .sr i => Equiv.swap 1 3 * finRotate 4 ^ i.val

set_option maxRecDepth 10000 in
def squareEmbedding : DihedralGroup 4 →* Equiv.Perm (Fin 4) where
  toFun := squarePermutation
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

set_option maxRecDepth 10000 in
theorem squareEmbedding_injective : Function.Injective squareEmbedding := by decide +kernel

def secondDihedralEmbedding : DihedralGroup 4 →* W := symmetricEmbedding.comp squareEmbedding

theorem secondDihedralEmbedding_injective : Function.Injective secondDihedralEmbedding :=
  symmetricEmbedding_injective.comp squareEmbedding_injective

def R₂ : Subgroup W := secondDihedralEmbedding.range

theorem R₂_le_X : R₂ ≤ X := by rintro _ ⟨r,rfl⟩; exact ⟨squareEmbedding r,rfl⟩

theorem R₂_card : Nat.card R₂ = 8 := by
  change Nat.card (secondDihedralEmbedding.range) = 8
  rw [← Nat.card_congr (MonoidHom.ofInjective secondDihedralEmbedding_injective).toEquiv]
  norm_num [DihedralGroup.card]

theorem second_central_vector : secondDihedralEmbedding (.r 2) =
    SemidirectProduct.inl (tailVector 2) := by
  apply SemidirectProduct.ext <;> decide +kernel

theorem marked_axes_weight_four : weight (pair01 * tailVector 2) = 4 := by decide +kernel

/-- The two actual dihedral embeddings supply the central axes in the original
normalizer splitting; subsequent Sylow alignment may conjugate both together. -/
theorem marked_dihedral_pair :
    Function.Injective dihedralEmbedding ∧ Function.Injective secondDihedralEmbedding ∧
    dihedralEmbedding (.r 2) = t ∧
    secondDihedralEmbedding (.r 2) = SemidirectProduct.inl (tailVector 2) ∧
    (∀ r s, Commute (dihedralEmbedding r) (secondDihedralEmbedding s)) ∧
    R₂ ≤ X ∧ Nat.card R₂ = 8 := by
  exact ⟨dihedralEmbedding_injective,secondDihedralEmbedding_injective,dihedral_marked,
    second_central_vector,fun r s => embeddings_commute r (squareEmbedding s),R₂_le_X,R₂_card⟩

end BinaryFiveAffine
