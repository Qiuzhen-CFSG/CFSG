module
public import CFSG.Quasithin.ChapterD.Section03.EvenExchange
public import Theory.Representation.SL2.SmallSquare

/-!
# Removing the Schur-nonlinear exchange alternative

The previous exchange analysis bounds the whole binary degree by 4(n+1)
when the exchanger acts nontrivially on the Schur field. The small-square
classification now identifies that entire module as a natural tensor too.
Thus the original small cubic square has a natural/Hermitian constituent
in one factor, or a whole-space natural tensor. The intertwiner and its
component twist are retained; no Schur-linearity assumption remains.

This is the remaining exchanged-actor recognition in D.3.7. The original
Chapter 10 consumer must still exclude the natural tensor using its ambient
hypotheses and complete constituent minimality.
Source: Aschbacher--Smith D.3.7, printed pp.197--199.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterD
variable {F V : Type*} [Field F] [Finite F] [CharP F 2]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
local instance evenNaturalTensorAlgebra : Algebra (ZMod 2) F := ZMod.algebra _ 2
open Representation.QuadraticFourGroup.TensorClassification

/-- The actual constituent models or a whole-space natural tensor, in the
original factor coordinates. -/
def EvenSquareConstituentOrNatural
    (σ : Representation (ZMod 2) (SL(2,F) × SL(2,F)) V) (n : ℕ) : Prop :=
    (EvenFactorConstituent (σ.comp (MonoidHom.inl SL(2,F) SL(2,F))) n ∨
      EvenFactorConstituent (σ.comp (MonoidHom.inr SL(2,F) SL(2,F))) n) ∨
    ∃ α : MulAut SL(2,F), Nonempty (σ.Equiv (restrictScalars (k := ZMod 2)
      (externalTensor ((SL2.BinarySmall.embeddedNatural (RingHom.id F)).comp α.symm.toMonoidHom)
        (SL2.BinarySmall.embeddedNatural (RingHom.id F)))))

/-- Small exchanges give actual natural tensors also when they act
nontrivially on the original Schur field. -/
theorem even_square_constituent_or_natural_tensor
    (σ : Representation (ZMod 2) (SL(2,F) × SL(2,F)) V)
    (hi : σ.IsIrreducible) (hf : Function.Injective σ)
    (n : ℕ) (hn : 3 ≤ n) (hF : Nat.card F=2^n)
    (h : EvenSquareTensorAnalysis σ n) : EvenSquareConstituentOrNatural σ n := by
  let := hi
  rcases h with hc | ht | ⟨_,_,_,_,_,hdegree,_⟩
  · exact Or.inl hc
  · exact Or.inr ht
  · exact Or.inr (SL2.SmallSquare.small_square_natural_tensor σ hf n hn hF hdegree)
end CFSG.Quasithin.ChapterD
