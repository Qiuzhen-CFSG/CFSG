module

public import Theory.Representation.SL2.BinarySmallModels

/-!
# Models for the repeated-pair binary highest weight

The Hermitian model is the existing conjugation action, transported along
actual group-field and coefficient-field equivalences. Its binary module
structure remains the one published by `BinarySmall.spaceBinaryModule`.
The comparison action on matrices is the tensor of the natural action's
`j`-th and `(j+s)`-th Frobenius twists. The entrywise formulas below fix
both conventions for subsequent intertwining constructions.

These are concrete actions, not recognition assumptions or a dimension-based
identification. Source: GLS volume 3, §§2.8.6, 2.8.8, 2.8.10(b);
Aschbacher--Smith, combined manuscript (1 March 2004), G.9.3(7), pp.354,356–357.
-/

@[expose] public section

open scoped MatrixGroups MonoidAlgebra TensorProduct
open Representation.OrthogonalFourMinus Representation.OrthogonalFourMinus.FiniteModel
namespace Representation.SL2.BinaryHermitian
noncomputable section

variable {K : Type*} [Field K] {E : Type*} [Field E]
    {s : ℕ} [NeZero s]

/-- Pull back the scalar action along the actual coefficient field identification. -/
@[instance_reducible] def coefficientModule (θ : E ≃+* fixedField s) : Module E (Space s) :=
  Module.compHom (Space s) θ.toRingHom

/-- The actual Hermitian action with coefficients transported from its fixed field. -/
def model (θ : E ≃+* fixedField s) (f : K ≃+* Field s) :
    letI := coefficientModule θ
    Representation E SL(2,K) (Space s) := by
  letI := coefficientModule θ
  exact
    { toFun g :=
        { toFun := action s (Matrix.SpecialLinearGroup.map f.toRingHom g)
          map_add' := map_add _
          map_smul' c v := map_smul _ (θ c) v }
      map_one' := by
        apply LinearMap.ext
        intro v
        exact congrArg (fun h : Module.End (fixedField s) (Space s) => h v)
          ((action s).comp (Matrix.SpecialLinearGroup.map f.toRingHom)).map_one
      map_mul' g h := by
        apply LinearMap.ext
        intro v
        exact congrArg (fun a : Module.End (fixedField s) (Space s) => a v)
          (((action s).comp (Matrix.SpecialLinearGroup.map f.toRingHom)).map_mul g h) }

/-- The two Frobenius factors realized as an action on two-by-two matrices. -/
def pair {L : Type*} [Field L] [CharP L 2] [PerfectRing L 2]
    (e : K →+* L) (s j : ℕ) : Representation L SL(2,K) (Mat L) :=
  (tensorAction (iterateFrobeniusEquiv L 2 s)).comp
    (Matrix.SpecialLinearGroup.map ((iterateFrobeniusEquiv L 2 j).toRingHom.comp e))

theorem model_apply (θ : E ≃+* fixedField s) (f : K ≃+* Field s)
    (g : SL(2,K)) (X : Space s) :
    letI := coefficientModule θ
    (model θ f g X).val =
      (g.val.map f) * X.val * adjoint (conjugation s) (g.val.map f) := rfl

theorem pair_apply {L : Type*} [Field L] [CharP L 2] [PerfectRing L 2]
    (e : K →+* L) (s j : ℕ) (g : SL(2,K)) (X : Mat L) :
    pair e s j g X =
      (g.val.map (fun x => e x ^ (2 ^ j))) * X *
        (g.val.map (fun x => e x ^ (2 ^ (j+s)))).transpose := by
  change _ * X * _ = _ * X * _
  congr 1
  ext a b
  change iterateFrobeniusEquiv L 2 s (iterateFrobeniusEquiv L 2 j (e (g.val b a))) = _
  rw [iterateFrobeniusEquiv_def, iterateFrobeniusEquiv_def, ← pow_mul, ← pow_add]
  rfl

end
end Representation.SL2.BinaryHermitian
