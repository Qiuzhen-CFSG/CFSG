module

public import Theory.Representation.SL2.BinaryHermitianRecognition.Setup
public import Theory.Representation.SL2.BinaryHermitianRecognition.FieldComparison
public import Theory.Representation.SL2.BinaryHermitianRecognition.HighestWeight
public import Theory.Representation.SL2.BinaryHermitianRecognition.ScalarExtension
public import Theory.Representation.SL2.HighestWeightSpan
public import Theory.Representation.EndFieldRep
public import Theory.Representation.ScalarDescent

/-!
# Scalar descent for binary Hermitian recognition

An intertwiner over an extension of the Schur field descends to that field.
Its underlying additive equivalence then gives an intertwiner for the exact
binary action published in `BinarySmallModels`. No dimension-only module
identification is used.

Compatible group-field and half-field identifications are constructed from
the given cardinalities. The entrywise scalar extension of Hermitian matrices
and the polynomial realization of the two Frobenius factors supply the actual
intertwining comparisons. The final theorem therefore recognizes the Hermitian
module from the repeated-pair highest weight and the Schur degree, including
half-degree one. Its conclusion retains an actual ring equivalence of the
group fields and a binary intertwiner to the published Hermitian action.

Source: GLS volume 3, §§2.8.6, 2.8.8, 2.8.10(b); Aschbacher--Smith,
combined manuscript (1 March 2004), G.9.3(7), printed pp.354,356–357.
-/

@[expose] public section

open scoped MatrixGroups MonoidAlgebra TensorProduct
open Representation.OrthogonalFourMinus Representation.OrthogonalFourMinus.FiniteModel
namespace Representation.SL2.BinaryHermitian
noncomputable section
variable {K : Type*} [Field K] {s : ℕ} [NeZero s]

local instance (s : ℕ) [NeZero s] : Module (ZMod 2) (Space s) :=
  BinarySmall.spaceBinaryModule s

variable [Finite K] [CharP K 2]
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL(2,K) V) [ρ.IsIrreducible]

omit [Finite K] [CharP K 2] in
/-- Scalar descent of an actual Hermitian intertwiner gives the published
binary recognition predicate, retaining the specified field identification. -/
theorem isHermitian_of_modelComparison
    (θ : Module.End (ZMod 2)[SL(2,K)] ρ.asModule ≃+* fixedField s)
    (f : K ≃+* Field s)
    (h : letI := coefficientModule θ
      Nonempty ((extendScalars (AlgebraicClosure (Module.End (ZMod 2)[SL(2,K)] ρ.asModule))
        ρ.endFieldRep).Equiv
        (extendScalars (AlgebraicClosure (Module.End (ZMod 2)[SL(2,K)] ρ.asModule))
          (model θ f)))) : BinarySmall.IsHermitian ρ s := by
  let E := Module.End (ZMod 2)[SL(2,K)] ρ.asModule
  let := coefficientModule θ
  have : Finite V := Module.finite_iff_finite.mp (inferInstance : Module.Finite (ZMod 2) V)
  have : Finite ρ.asModule := Finite.of_injective _ ρ.asModuleEquiv.injective
  have : Module.Finite E ρ.asModule := Module.Finite.of_finite
  have : Module.Finite E (Space s) := Module.Finite.of_finite
  obtain ⟨u⟩ := repEquiv_of_extendScalars ρ.endFieldRep (model θ f)
    ⟨RepEquiv.ofRepresentationEquiv h.some⟩
  let a : V ≃+ Space s := ρ.asModuleEquiv.symm.toAddEquiv.trans u.toLinearEquiv.toAddEquiv
  let b : V ≃ₗ[ZMod 2] Space s :=
    LinearEquiv.ofBijective (a.toAddMonoidHom.toZModLinearMap 2) a.bijective
  refine ⟨f, ⟨Representation.Equiv.mk b ?_⟩⟩
  intro g
  apply LinearMap.ext
  intro v
  exact u.isIntertwining g (ρ.asModuleEquiv.symm v)


/-- Assemble the two concrete intertwining comparisons after constructing all
field identifications. The matrix and highest-weight comparisons remain explicit
premises here; this is a scalar-descent helper, not an exhaustivity theorem. -/
theorem isHermitian_of_pair_comparisons (j : ℕ)
    (hK : Nat.card K = 2 ^ (2*s))
    (hE : Module.finrank (ZMod 2) (Module.End (ZMod 2)[SL(2,K)] ρ.asModule) = s)
    (e : K →+* AlgebraicClosure (Module.End (ZMod 2)[SL(2,K)] ρ.asModule))
    (hρ : Nonempty ((extendScalars (AlgebraicClosure
        (Module.End (ZMod 2)[SL(2,K)] ρ.asModule)) ρ.endFieldRep).Equiv
      (highestWeightSpan e (2 ^ j * (1 + 2 ^ s))).toRepresentation)) :
    let E := Module.End (ZMod 2)[SL(2,K)] ρ.asModule
    let L := AlgebraicClosure E
    letI : CharP L 2 := charP_of_injective_ringHom e.injective 2
    Nonempty ((pair e s j).Equiv
      (highestWeightSpan e (2 ^ j * (1 + 2 ^ s))).toRepresentation) →
    (∀ (f : K ≃+* Field s) (β : Field s →+* L) (θ : E ≃+* fixedField s),
      (∀ a, β (θ a).val = algebraMap E L a) →
      (∀ x, β (f x) = e x ^ (2 ^ j)) →
      letI := coefficientModule θ
      Nonempty ((extendScalars L (model θ f)).Equiv (pair e s j))) →
    BinarySmall.IsHermitian ρ s := by
  let E := Module.End (ZMod 2)[SL(2,K)] ρ.asModule
  let L := AlgebraicClosure E
  let : CharP L 2 := charP_of_injective_ringHom e.injective 2
  dsimp only
  intro hpair hmodel
  have hc : Nat.card E = 2 ^ s := by
    rw [← FiniteField.pow_finrank_eq_natCard 2 E, hE]
  obtain ⟨f, β, θ, hθ, hf⟩ := exists_modelFields s j (algebraMap E L) e hK hc
  let := coefficientModule θ
  obtain ⟨hm⟩ := hmodel f β θ hθ hf
  exact isHermitian_of_modelComparison ρ θ f
    ⟨hρ.some.trans (hpair.some.symm.trans hm.symm)⟩

omit [NeZero s] in
/-- An irreducible binary representation with Schur degree `s` and repeated-pair
highest weight `2^j * (1 + 2^s)` is the actual Hermitian module over the fixed
half-field. The Frobenius shift is absorbed into the group-field equivalence,
and both concrete comparison maps are descended to the binary action. -/
theorem isHermitian_of_highestWeight_pair (hs : 0 < s)
    (hK : Nat.card K = 2 ^ (2 * s))
    (hE : Module.finrank (ZMod 2) (Module.End (ZMod 2)[SL(2,K)] ρ.asModule) = s)
    (j : ℕ) (hj : j < s)
    (e : K →+* AlgebraicClosure (Module.End (ZMod 2)[SL(2,K)] ρ.asModule))
    (hρ : Nonempty ((extendScalars (AlgebraicClosure
        (Module.End (ZMod 2)[SL(2,K)] ρ.asModule)) ρ.endFieldRep).Equiv
      (highestWeightSpan e (2 ^ j * (1 + 2 ^ s))).toRepresentation)) :
    letI : NeZero s := ⟨Nat.ne_of_gt hs⟩
    BinarySmall.IsHermitian ρ s := by
  let : NeZero s := ⟨Nat.ne_of_gt hs⟩
  let E := Module.End (ZMod 2)[SL(2,K)] ρ.asModule
  let L := AlgebraicClosure E
  let : CharP L 2 := charP_of_injective_ringHom e.injective 2
  exact isHermitian_of_pair_comparisons ρ j hK hE e hρ
    (pair_equiv_highestWeightSpan e s j hK hj)
    (fun f β θ hθ hf => nonempty_extendScalars_model_equiv_pair θ β hθ e f j hf)

end
end Representation.SL2.BinaryHermitian
