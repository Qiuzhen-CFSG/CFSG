module
public import Theory.Representation.BinaryPermutation.SixCoreExtension.Residual.Transport

/-!
# Squares of nonconstant six-core vectors

Both nonconstant A₆-orbits, of weights two and four, consist of squares in
the full split extension. The weight-two root uses a fixed coordinate;
therefore it need not lie in the centralizer's two-residual core. This is
compatible with the unique core-square theorem, which distinguishes the two
lifts of one natural-module vector.

Source: the binary hexad model in Aschbacher--Smith I.2.2(6b), p.412.
-/

public section
namespace BinaryPermutation.SixCoreExtension
noncomputable section

private def pairRoot : Model :=
  ⟨Multiplicative.ofAdd ⟨![1,0,0,0,1,0], by rw [mem_core]; decide⟩,
    ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by simp [Equiv.Perm.mem_alternatingGroup]⟩⟩

private theorem pairRoot_sq : pairRoot ^ 2 = vector (Multiplicative.ofAdd pair) := by
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    apply Subtype.ext
    funext i
    fin_cases i <;> rfl
  · apply Subtype.ext
    ext i
    fin_cases i <;> rfl

/-- Every nonconstant augmentation-core vector is a square in the actual
extension; this statement does not put the root in its two-residual core. -/
theorem exists_square_vector (v : V) (hv : coreToNatural (Fin 6) v ≠ 0) :
    ∃ x : Model, x ^ 2 = vector (Multiplicative.ofAdd v) := by
  obtain ⟨g,hg | hg⟩ := exists_pair_or_four_transport v hv
  · refine ⟨MulAut.conj (SemidirectProduct.inr g) pairRoot,?_⟩
    rw [← map_pow,pairRoot_sq,conj_vector,hg]
  · refine ⟨MulAut.conj (SemidirectProduct.inr g) root,?_⟩
    rw [← map_pow,root_sq,conj_vector,hg]

end
end BinaryPermutation.SixCoreExtension
