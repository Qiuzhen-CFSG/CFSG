module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.KernelCentralizer

/-!
# Literal native representatives of the printed permutations

Each representative is evaluated in the original max1 generators, using the
already certified Figure 1/2 word. Every other lift is its product with a unique
native kernel mask. These statements do not assert involutivity of the chosen
representatives: the square and commutator corrections still require calculation.
Source: Kleidman--Wilson (1988), Figures 1/2, with the ATLAS max1 marking.
-/

set_option backward.isDefEq.respectTransparency true
@[expose] public noncomputable section
namespace Janko4.LocalStructure.ElementaryEightGeometry
open Subgroup Theory.GroupTheory Cardinality Cardinality.QuotientCount.Image
open SylowCore SylowCore.Transport
attribute [local irreducible] modelGroup matrixA matrixB localKernel max1Subgroup localX localY
local notation "L" => SylowCore.Local
local notation "E" => localKernel matrixA_mul_self matrixB_pow_four
local notation "π" => starProjection matrixA_mul_self matrixB_pow_four
local notation "e" => maskEquiv matrixA_mul_self matrixB_pow_four

def nativeAlphabet : Fin 4 → L :=
  ![localX matrixA_mul_self matrixB_pow_four, localY matrixA_mul_self matrixB_pow_four,
    (localX matrixA_mul_self matrixB_pow_four)⁻¹, (localY matrixA_mul_self matrixB_pow_four)⁻¹]

def permutationLift (i : Fin 6) : L := evalWord nativeAlphabet (word i)

private theorem nativeAlphabet_projection (i : Fin 4) :
    (π (nativeAlphabet i)).val = alphabet i := by
  fin_cases i
  · change (π (localX matrixA_mul_self matrixB_pow_four)).val = starX
    exact congrArg Subtype.val (starProjection_x _ _)
  · change (π (localY matrixA_mul_self matrixB_pow_four)).val = starY
    exact congrArg Subtype.val (starProjection_y _ _)
  · change (π (localX matrixA_mul_self matrixB_pow_four)⁻¹).val = starX⁻¹
    rw [map_inv, starProjection_x]
    rfl
  · change (π (localY matrixA_mul_self matrixB_pow_four)⁻¹).val = starY⁻¹
    rw [map_inv, starProjection_y]
    rfl

private theorem word_projection (w : List (Fin 4)) :
    (π (evalWord nativeAlphabet w)).val = evalWord alphabet w := by
  induction w with
  | nil => simp only [evalWord, map_one, Subgroup.coe_one]
  | cons i w ih => simp only [evalWord, map_mul, Subgroup.coe_mul,
      nativeAlphabet_projection, ih]

/-- Each representative maps to the exact selected permutation, with no change of marking. -/
theorem permutationLift_projection (i : Fin 6) : π (permutationLift i) = starElement i := by
  apply Subtype.ext
  exact (word_projection (word i)).trans (starElement_word i)

/-- The whole fibre is parametrized by original kernel elements, on the left. -/
theorem permutationLift_fibre (i : Fin 6) (x : L) :
    π x = starElement i ↔ ∃! m : Fin 2048, x = (e m : L) * permutationLift i := by
  constructor
  · intro hx
    have hk : x * (permutationLift i)⁻¹ ∈ E := by
      rw [← starProjection_ker, MonoidHom.mem_ker, map_mul, map_inv,
        permutationLift_projection, hx, mul_inv_cancel]
    obtain ⟨m,hm⟩ := (e).surjective ⟨x * (permutationLift i)⁻¹,hk⟩
    have hv : (e m : L) = x * (permutationLift i)⁻¹ := congrArg Subtype.val hm
    refine ⟨m, ?_, ?_⟩
    · change x = (e m : L) * permutationLift i
      rw [hv, inv_mul_cancel_right]
    · intro n hn
      apply (e).injective
      apply Subtype.ext
      apply mul_right_cancel (b := permutationLift i)
      rw [← hn, hv, inv_mul_cancel_right]
  · rintro ⟨m,hm,_⟩
    rw [hm, map_mul, permutationLift_projection]
    have hk : π (e m : L) = 1 := by
      apply MonoidHom.mem_ker.mp
      rw [starProjection_ker]
      exact (e m).property
    rw [hk, one_mul]

end Janko4.LocalStructure.ElementaryEightGeometry