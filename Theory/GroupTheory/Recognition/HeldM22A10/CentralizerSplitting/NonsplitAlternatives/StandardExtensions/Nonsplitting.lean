module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.StandardExtensions.Parity

/-!
# Nontriviality of the two parity extensions

The ordinary parity factor set is not a coboundary: an involutory lift of a
transposition would require its norm on binary four-space to be the diagonal,
which is impossible at a fixed coordinate. For the twisted action, individual
involutory lifts exist, but lifts of two disjoint transpositions cannot both
be involutions and commute. A homomorphic section would give exactly such a
pair. The small norm obstructions are checked by the kernel on 16 and 256
binary inputs respectively.

Consequently neither parity extension splits over its specified projection
kernel. These results certify the nontrivial representatives used in the
finite extension step of Huppert--Blackburn III, XII.1.18(b), p.314. They do
not assert completeness of the extension classes or identify the extensions
with the published sixteen-point permutation models.
-/

namespace Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.StandardExtensions
open LocalModelDichotomy AbelianExtension

private def swapLeft : SymmetricFour := Equiv.swap 0 1
private def swapRight : SymmetricFour := Equiv.swap 2 3

private theorem permutation_norm_obstruction :
    ∀ x : BinaryFour, x * permutationAction swapLeft x ≠ diagonal := by
  decide +kernel

private theorem twisted_norm_obstruction : ∀ x y : BinaryFour,
    x * twistedAction swapLeft x = diagonal →
    y * twistedAction swapRight y = diagonal →
    x * twistedAction swapLeft y ≠ y * twistedAction swapRight x := by
  decide +kernel

/-- The parity factor set for the ordinary action is not a coboundary. -/
public theorem permutationFactorSet_not_equivalent_trivial :
    ¬ permutationFactorSet.Equivalent (FactorSet.trivial permutationAction) := by
  rintro ⟨b, hb, h⟩
  have hss : swapLeft * swapLeft = 1 := by decide +kernel
  have hcarry : permutationFactorSet.toFun swapLeft swapLeft = diagonal := by
    decide +kernel
  have hs := h swapLeft swapLeft
  rw [hss, hb, hcarry, mul_one] at hs
  change diagonal = b swapLeft * permutationAction swapLeft (b swapLeft) * 1 at hs
  rw [mul_one] at hs
  exact permutation_norm_obstruction (b swapLeft) hs.symm

/-- The parity factor set for the twisted action is not a coboundary. -/
public theorem twistedFactorSet_not_equivalent_trivial :
    ¬ twistedFactorSet.Equivalent (FactorSet.trivial twistedAction) := by
  rintro ⟨b, hb, h⟩
  have hss : swapLeft * swapLeft = 1 := by decide +kernel
  have htt : swapRight * swapRight = 1 := by decide +kernel
  have hst : swapLeft * swapRight = swapRight * swapLeft := by decide +kernel
  have hc : ∀ a b, twistedFactorSet.toFun a b = parityCarry a b := fun _ _ => rfl
  have hs := h swapLeft swapLeft
  have ht := h swapRight swapRight
  have hst' := h swapLeft swapRight
  have hts := h swapRight swapLeft
  have hcs : parityCarry swapLeft swapLeft = diagonal := by decide +kernel
  have hct : parityCarry swapRight swapRight = diagonal := by decide +kernel
  have hcst : parityCarry swapLeft swapRight = diagonal := by decide +kernel
  have hcts : parityCarry swapRight swapLeft = diagonal := by decide +kernel
  simp only [hc, hss, htt, hb, hcs, hct, hcst, hcts, FactorSet.trivial, mul_one]
    at hs ht hst' hts
  have hcomm : b swapLeft * twistedAction swapLeft (b swapRight) =
      b swapRight * twistedAction swapRight (b swapLeft) := by
    rw [← hst', ← hts, hst]
  exact twisted_norm_obstruction (b swapLeft) (b swapRight) hs.symm ht.symm hcomm

/-- The ordinary parity extension has no complement to its specified kernel. -/
public theorem permutationFactorSet_no_complement :
    ¬ ∃ K : Subgroup permutationFactorSet.Extension,
      permutationFactorSet.projection.ker.IsComplement' K := by
  rw [← FactorSet.equivalent_trivial_iff_exists_complement]
  exact permutationFactorSet_not_equivalent_trivial

/-- The twisted parity extension has no complement to its specified kernel. -/
public theorem twistedFactorSet_no_complement :
    ¬ ∃ K : Subgroup twistedFactorSet.Extension,
      twistedFactorSet.projection.ker.IsComplement' K := by
  rw [← FactorSet.equivalent_trivial_iff_exists_complement]
  exact twistedFactorSet_not_equivalent_trivial

end Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.StandardExtensions
