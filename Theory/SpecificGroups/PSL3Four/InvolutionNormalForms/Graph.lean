module

public import Theory.SpecificGroups.PSL3Four.InvolutionNormalForms.Graph.Gram
public import Theory.SpecificGroups.PSL3.OddInvolutionFixed.Graph
public import Theory.SpecificGroups.PSL3.OuterSolvable.StandardQuotient

/-!
# The graph involution class of PSL₃(4)

The projective involution equation forces the conjugating matrix to be
symmetric. Gram factorization writes it as hᵀh, and conjugation by the
linear actor of h⁻ᵀ removes the linear factor. All identities use the
actual action on SL₃(4)/Z(SL₃(4)); the conjugator need not have determinant one.

Source: the inverted-cubic assertion in Aschbacher–Smith H.4.7, printed
pp.382–383 of refs/quasithin.pdf. The cubic itself is constructed by the
Chapter H consumer.
-/

public section
noncomputable section
namespace Matrix.PSL3Four.InvolutionNormalForms

open Matrix.PSL3.OuterSolvable

/-- An involution in the linear–graph coset is conjugate to inverse transpose
on the actual quotient SL₃(4)/Z(SL₃(4)). -/
theorem graph_involution_conjugate (m : GL (Fin 3) F)
    (hm : (linearConj F m * graph F)^2 = 1) :
    ∃ d : MulAut PSL, MulAut.congr d (linearConj F m * graph F) = graph F := by
  obtain ⟨h, hh⟩ := symmetric_gram m (PSL3.OddInvolutionFixed.graph_involution_symmetric m hm)
  let n := inverseTransposeGL F h
  have hfactor : m = n⁻¹ * h := Units.ext hh
  have hn : inverseTransposeGL F n = h := Units.ext rfl
  have hnorm : n * m * inverseTransposeGL F n⁻¹ = 1 := by
    rw [hfactor, map_inv, hn]
    group
  refine ⟨linearConj F n, ?_⟩
  change linearConj F n * (linearConj F m * graph F) * (linearConj F n)⁻¹ = graph F
  rw [← map_inv, mul_assoc, mul_assoc, graph_linearConj, ← mul_assoc,
    ← map_mul, ← mul_assoc, ← map_mul, hnorm, map_one, one_mul]

end Matrix.PSL3Four.InvolutionNormalForms
