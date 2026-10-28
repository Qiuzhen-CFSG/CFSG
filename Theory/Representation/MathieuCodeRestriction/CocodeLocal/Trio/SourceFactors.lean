module

public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Trio.Affine

/-!
# Natural tensor factors in the source order

The affine quotient is S₃ × SL₃(2). The checked SL₃(2)–PSL₃(2) isomorphism
puts it in the source order L₃(2) × S₃. We transport the natural actions along
this concrete isomorphism, retaining the literal three-space and the binary
even core on three letters. Thus the tensor action has a specified meaning
on the actual projective matrix factor, with no natural/dual substitution.

Source: Aschbacher–Smith H.14.1(3), printed p.396, and H.15.6(3), printed
p.401. The SL/PSL comparison is the licensed ATLAS port already used in
`Affine`; see `LICENSES/ATLAS.txt`.
-/

@[expose] public section
open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.QuotientConstruction
open scoped MatrixGroups TensorProduct
namespace MathieuCode.TrioCalculation
noncomputable section

abbrev SourceQuotientModel := PSL(3, ZMod 2) × Equiv.Perm (Fin 3)

/-- The actual matrix comparison, with the linear factor first. -/
def sourceFactorsEquiv : QuotientModel ≃* SourceQuotientModel :=
  (MulEquiv.prodComm).trans
    (MulEquiv.prodCongr Atlas.Comparisons.Exceptional.sl3TwoEquivPsl3Two (MulEquiv.refl _))

/-- The natural L₃(2) module through its checked SL₃(2) realization. -/
def sourceNaturalThree : Representation (ZMod 2) SourceQuotientModel Vector :=
  quotientNaturalThree.comp sourceFactorsEquiv.symm.toMonoidHom

/-- The natural S₃ module, the even core on three letters. -/
def sourceNaturalTwo :
    Representation (ZMod 2) SourceQuotientModel (BinaryPermutation.core (Fin 3)) :=
  quotientNaturalTwo.comp sourceFactorsEquiv.symm.toMonoidHom

lemma sourceNaturalThree_apply (q : SourceQuotientModel) (v : Vector) :
    sourceNaturalThree q v =
      Matrix.SpecialLinearGroup.toLin' (Atlas.Comparisons.Exceptional.sl3TwoEquivPsl3Two.symm q.1) v :=
  rfl

lemma sourceNaturalTwo_apply (q : SourceQuotientModel) (v : BinaryPermutation.core (Fin 3)) :
    sourceNaturalTwo q v = BinaryPermutation.coreRepresentation (Fin 3) q.2 v := rfl

/-- Both factors act on their literal natural tensor product. -/
def sourceTensorRepresentation : Representation (ZMod 2) SourceQuotientModel NaturalTensor :=
  quotientTensorRepresentation.comp sourceFactorsEquiv.symm.toMonoidHom

lemma sourceTensorRepresentation_eq_tprod :
    sourceTensorRepresentation = sourceNaturalThree.tprod sourceNaturalTwo := rfl

lemma sourceTensorRepresentation_factors (q : QuotientModel) :
    sourceTensorRepresentation (sourceFactorsEquiv q) = quotientTensorRepresentation q := by
  change quotientTensorRepresentation (sourceFactorsEquiv.symm (sourceFactorsEquiv q)) = _
  rw [MulEquiv.symm_apply_apply]

end
end MathieuCode.TrioCalculation
