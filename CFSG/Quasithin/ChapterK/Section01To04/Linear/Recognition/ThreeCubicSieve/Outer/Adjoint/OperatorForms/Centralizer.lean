module
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint.Forms
public import Theory.Representation.SL3.BinaryDefiningFactors.Classification.TensorSimplicity.RestrictedFactors

/-!
# The binary adjoint centralizer

The actual adjoint base-change equivalence and restricted-factor simplicity
prove absolute irreducibility over the defining field. Over the binary field,
Wedderburn's theorem makes the commuting endomorphism ring commutative. Its
commutation with defining-field scalars makes each binary endomorphism linear
over that field; absolute irreducibility then makes it a scalar.

This includes the fields of orders two and four, and never assumes that the
SL₃ action is faithful. The operator-form assembly applies this to the quotient
of two operators inducing the same component automorphism.
Source: GLS III, Remark 2.8.8 and Example 2.8.10(c); GM, Proposition 4.8, step 3A.
-/

@[expose] public noncomputable section
open Representation Representation.BinaryOffender
open Representation.SL3.BinaryDefiningFactors
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups MonoidAlgebra
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint.OperatorForms
set_option backward.isDefEq.respectTransparency false
variable (B : BinaryField)

theorem adjoint_absolute : IsAbsolutelyIrreducible
    (factorRep (RingHom.id B.Carrier) .adjoint) := by
  constructor
  apply (RepEquiv.irreducible_euqiv
    (RepEquiv.ofRepresentationEquiv
      (adjointBaseChange (F := B.Carrier) (K := AlgebraicClosure B.Carrier)))).mpr
  exact factorRep_isIrreducible _ _

theorem coefficient_centralizer (f : IntertwiningMap
    (factorRep (RingHom.id B.Carrier) .adjoint)
    (factorRep (RingHom.id B.Carrier) .adjoint)) :
    ∃ c : B.Carrier, ∀ x, f x = c • x := by
  let : IsIrreducible (factorRep (RingHom.id B.Carrier) .adjoint) :=
    factorRep_isIrreducible _ _
  obtain ⟨c, hc⟩ := (isAbsolutelyIrreducible_iff_surjective _).mp
    (adjoint_absolute B) f
  refine ⟨c, fun x => ?_⟩
  exact (congrArg (fun a : End (factorRep (RingHom.id B.Carrier) .adjoint) => a x) hc).symm

theorem binary_centralizer [IsIrreducible (binaryRep B)]
    (f : IntertwiningMap (binaryRep B) (binaryRep B)) :
    ∃ c : B.Carrier, ∀ x, f x = c • x := by
  let : Finite (AdjointSpace B.Carrier) := Module.finite_of_finite B.Carrier
  let : FiniteDimensional (ZMod 2) (AdjointSpace B.Carrier) := Module.Finite.of_finite
  have hs (c : B.Carrier) (x : AdjointSpace B.Carrier) : f (c • x) = c • f x := by
    let s : IntertwiningMap (binaryRep B) (binaryRep B) := {
      toLinearMap := (c • (LinearMap.id : Module.End B.Carrier
        (AdjointSpace B.Carrier))).restrictScalars (ZMod 2)
      isIntertwining' := by
        intro g
        apply LinearMap.ext
        intro y
        exact (map_smul (factorRep (RingHom.id B.Carrier) .adjoint g) c y).symm }
    have h := mul_comm (IntertwiningMap.equivAlgEnd (binaryRep B) f)
      (IntertwiningMap.equivAlgEnd (binaryRep B) s)
    exact congrArg (fun a : Module.End (ZMod 2)[SL(3,B.Carrier)]
      (binaryRep B).asModule => (binaryRep B).asModuleEquiv
        (a ((binaryRep B).asModuleEquiv.symm x))) h
  let f' : IntertwiningMap (factorRep (RingHom.id B.Carrier) .adjoint)
      (factorRep (RingHom.id B.Carrier) .adjoint) := {
    toLinearMap := { toFun := f, map_add' := map_add f, map_smul' := hs }
    isIntertwining' := by
      intro g
      ext x
      exact LinearMap.congr_fun (f.isIntertwining' g) x }
  exact coefficient_centralizer B f'
end CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint.OperatorForms
