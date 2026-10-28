module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.NormNum

/-!
# The scalar field in the cocode row of 8.2.8(5)

The printed statement of Aschbacher–Smith, *The Classification of Quasithin
Groups*, Proposition 8.2.8(5), p.718 (PDF p.735), specifies F₂ in case (3a).
For the M₂₄ cocode row k = 2, however, the ranks in 8.2.5 and the natural
sections in E.2.14 give dim(P/U) = 12, dim(J) = 4 and dim(B/U) = 6 over F₂.
Thus the asserted tensor product of those literal spaces cannot be over F₂.

The proof on p.719 instead constructs Λ ⊗ Θ with binary dimensions three
and four. To use the literal B/U as the second factor, the cocode row needs
the additional F₄ scalar structure, making the factor dimensions two and
three over F₄. Constructing that structure and the marked equivalence remains
part of the tensor proof; these diagnostics do not construct it.

This is an obstruction to the printed local tensor interface, not a
counterexample to the normalizer or classification theorem. In particular it
must not be used to eliminate the surviving cocode branch. The source rank
identifications still have to be supplied on the actual quotients.
-/

public section
namespace CFSG.Quasithin.Chapter8.Section02.Normalizer
open scoped TensorProduct

/-- The literal binary dimensions in the cocode row exclude the printed
binary tensor isomorphism. -/
theorem no_binary_tensor_of_cocode_dimensions
    {P J B : Type*} [AddCommGroup P] [AddCommGroup J] [AddCommGroup B]
    [Module (ZMod 2) P] [Module (ZMod 2) J] [Module (ZMod 2) B]
    (hP : Module.finrank (ZMod 2) P = 12)
    (hJ : Module.finrank (ZMod 2) J = 4)
    (hB : Module.finrank (ZMod 2) B = 6) :
    ¬ Nonempty (P ≃ₗ[ZMod 2] J ⊗[ZMod 2] B) := by
  rintro ⟨e⟩
  have hd := e.finrank_eq
  rw [Module.finrank_tensorProduct, hP, hJ, hB] at hd
  norm_num at hd

/-- An explicit instance of the dimension obstruction, independent of any
unproved Chapter 8 setup. -/
theorem no_binary_tensor_four_six_twelve :
    ¬ Nonempty ((Fin 12 → ZMod 2) ≃ₗ[ZMod 2]
      (Fin 4 → ZMod 2) ⊗[ZMod 2] (Fin 6 → ZMod 2)) := by
  apply no_binary_tensor_of_cocode_dimensions <;> simp

end CFSG.Quasithin.Chapter8.Section02.Normalizer
