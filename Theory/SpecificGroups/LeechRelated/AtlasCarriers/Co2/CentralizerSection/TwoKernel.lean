module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Co2.CentralizerSection.ThreeRank.Words
public import Theory.GroupTheory.PrimeRankWitness
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Group.TypeTags.Finite

/-!
# A direct elementary subgroup for the Co₂ local-rank obstruction

The three checked commuting cubic words define a homomorphism from C₃³ into
the actual centralizing-word numerator. Their 27 products have distinct images
of point zero in the fixed 2300-point action, proving injectivity. The elementary
subgroup therefore gives three-rank at least three in the numerator.

This is the direct elementary-subgroup alternative to bounding the kernel of
`symplecticMap`. It proves the needed local obstruction without assuming any
kernel bound, centrality or splitting; it makes no assertion that preservation
of the coloring alone forces a two-group kernel. The chapter consumer uses the
existing involution and the literal numerator containment in its centralizer.

Source: Aschbacher–Smith A.2.19 and I.1.3, printed pp.40–41 and 407;
GLS3 Table 5.3k. The finite word certificates and their attribution are in
`ThreeRank/source/README.md`.
-/

public section

namespace Sporadic.LeechRelated.Co2.CentralizerSection.ThreeRank

/-- Three cyclic groups of order three. -/
abbrev Elementary := Multiplicative (ZMod 3) ×
  (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))

private def cyclic (i : Fin 3) : Multiplicative (ZMod 3) →* numerator where
  toFun a := element i ^ a.toAdd.val
  map_one' := rfl
  map_mul' a b := by
    change element i ^ (a.toAdd + b.toAdd).val =
      element i ^ a.toAdd.val * element i ^ b.toAdd.val
    rw [ZMod.val_add, ← pow_eq_pow_mod _ (element_cube i), pow_add]

/-- A literal elementary abelian subgroup in the centralizing-word numerator. -/
def elementaryEmbedding : Elementary →* numerator :=
  (cyclic 0).noncommCoprod
    ((cyclic 1).noncommCoprod (cyclic 2) (fun a b =>
      (element_commute 1 2).pow_pow a.toAdd.val b.toAdd.val))
    (fun a b =>
      ((element_commute 0 1).pow_pow a.toAdd.val b.1.toAdd.val).mul_right
        ((element_commute 0 2).pow_pow a.toAdd.val b.2.toAdd.val))

private def pointImage (a : Elementary) : Fin 2300 :=
  (elementFast 0)^[a.1.toAdd.val]
    ((elementFast 1)^[a.2.1.toAdd.val] ((elementFast 2)^[a.2.2.toAdd.val] 0))

set_option maxRecDepth 20000 in
private theorem pointImage_injective : Function.Injective pointImage := by decide +kernel

private theorem element_pow_apply (i : Fin 3) (n : ℕ) (x : Fin 2300) :
    permutation (element i ^ n) x = (elementFast i)^[n] x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', map_mul, Equiv.Perm.mul_apply, element_apply, ih,
      Function.iterate_succ_apply']

private theorem elementaryEmbedding_point (a : Elementary) :
    permutation (elementaryEmbedding a) 0 = pointImage a := by
  change permutation (element 0 ^ a.1.toAdd.val *
    (element 1 ^ a.2.1.toAdd.val * element 2 ^ a.2.2.toAdd.val)) 0 = _
  simp only [map_mul, Equiv.Perm.mul_apply, element_pow_apply, pointImage]

/-- The 27 products have distinct images of point zero, hence are distinct words. -/
theorem elementaryEmbedding_injective : Function.Injective elementaryEmbedding := by
  intro a b h
  apply pointImage_injective
  simpa only [elementaryEmbedding_point] using congrArg (fun g => permutation g 0) h

/-- The embedded subgroup witnesses three-rank at least three in the actual numerator. -/
theorem three_le_primeRank_numerator : 3 ≤ primeRank 3 numerator := by
  have hp : ∀ a : Elementary, a ^ 3 = 1 := by decide +kernel
  have hc : Nat.card Elementary = 3 ^ 3 := by simp [Elementary, Nat.card_eq_fintype_card]
  exact primeRank_ge_of_elementary_embedding hp hc elementaryEmbedding
    elementaryEmbedding_injective

end Sporadic.LeechRelated.Co2.CentralizerSection.ThreeRank
