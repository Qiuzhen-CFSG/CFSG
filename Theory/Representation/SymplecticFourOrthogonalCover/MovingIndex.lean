module

public import Theory.Representation.SymplecticFourOrthogonalCover.FixedIndex
public import Theory.Representation.ScalarCoinvariants
public import Theory.Representation.BinaryOffender.FaithfulRankOne

/-!
# Minimum movement over the field of four elements

Faithfulness makes the fixed codimension of a nontrivial subgroup positive.
Restriction of scalars makes it a multiple of the binary degree of the field.
For a field of order four it is therefore at least two. Fixed-index transport
extends this to every binary central factor of the odd orthogonal cover.

This excludes the exceptional index-two seed adjustment in MS93 (5.0) when
q=4, without a complement to the fixed central layer.
-/

public section
open Representation Representation.BinaryOffender Representation.OneCohomology
namespace Representation.SymplecticFourOrthogonalCover
variable {K : Type*} [Field K] [Finite K] [CharP K 2] [Algebra (ZMod 2) K]
omit [Finite K] [CharP K 2] in
theorem binaryNatural_injective : Function.Injective (binaryNatural (K := K)) := by
  intro g h he
  apply Subtype.ext
  apply Subtype.ext
  apply Matrix.mulVec_injective
  exact funext (fun v => LinearMap.congr_fun he v)
omit [CharP K 2] in
theorem two_le_fixedCodim_of_card_four (hK : Nat.card K = 4)
    (A : Subgroup (L (K := K))) (hne : A ≠ ⊥) : 2 ≤ fixedCodim binaryNatural A := by
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := K)
  simp only [Nat.card_zmod,hK] at hc
  have hd : Module.finrank (ZMod 2) K = 2 :=
    (Nat.pow_right_injective (by decide : 1 < 2)) hc.symm
  have hpos := fixedCodim_pos_of_faithful binaryNatural binaryNatural_injective hne
  have he := fixedCodim_restrictScalars (symplecticDerivedNatural (k := K) 2) A
  rw [hd] at he
  change fixedCodim binaryNatural A = _ at he
  omega
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  {σ : Representation (ZMod 2) (L (K := K)) W}
theorem cover_moving_index_ge_four (hK : Nat.card K = 4)
    (p : σ.IntertwiningMap (binaryNatural (K := K))) (hp : IsCover p)
    (A : Subgroup (L (K := K))) (hne : A ≠ ⊥) :
    4 ≤ 2 ^ fixedCodim σ A := by
  rw [fixedCodim_of_binaryCover p hp]
  exact Nat.pow_le_pow_right (by decide : 0 < 2) (two_le_fixedCodim_of_card_four hK A hne)
end Representation.SymplecticFourOrthogonalCover
