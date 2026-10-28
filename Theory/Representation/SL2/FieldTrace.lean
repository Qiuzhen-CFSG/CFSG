module

public import Theory.Representation.SL2.SteinbergParameters
public import Theory.Representation.SL2.CoefficientTwist
public import Theory.Representation.EndFieldFrobenius
public import Theory.SpecificGroups.PSL2.AutomorphismModel

/-!
# Frobenius on the actual SL₂ Schur traces

Precomposing the polynomial orbit span by a field automorphism changes its
coefficient embedding. The coefficient-twist character formula and the genuine
highest-weight classification therefore identify entrywise Frobenius on the
group with Frobenius on the character of the original Schur-field module.
A Schur-linear intertwiner for inner times Frobenius preserves the character;
the spanning-trace theorem forces its exponent to be divisible by the actual
Schur degree. No small-degree or tensor-displacement assumption is used.

Source: Guralnick--Malle, Classification of 2F-modules II, §3.5, manuscript
p.20, and the extendability step in Proposition 4.1(2), p.22.
-/

public section

open scoped MatrixGroups MonoidAlgebra
open Representation MvPolynomial
namespace Representation.SL2
variable {K F : Type*} [Field K] [Field F]

private theorem span_comp_fieldAut (e : K →+* F) (δ : K ≃+* K) (n : ℕ) :
    (highestWeightSpan (e.comp δ.toRingHom) n).toSubmodule =
      (highestWeightSpan e n).toSubmodule := by
  change Submodule.span F _ = Submodule.span F _
  apply congrArg (Submodule.span F)
  apply Set.ext
  intro f
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨Theory.PSL2.sl2FieldAut δ g, ?_⟩
    have he : Matrix.SpecialLinearGroup.map e (Theory.PSL2.sl2FieldAut δ g) =
        Matrix.SpecialLinearGroup.map (e.comp δ.toRingHom) g := by
      ext i j
      rfl
    exact congrArg (fun h => polynomialAction F h (X 0 ^ n)) he
  · rintro ⟨g, rfl⟩
    obtain ⟨g, rfl⟩ := (Theory.PSL2.sl2FieldAut δ).surjective g
    refine ⟨g, ?_⟩
    have he : Matrix.SpecialLinearGroup.map (e.comp δ.toRingHom) g =
        Matrix.SpecialLinearGroup.map e (Theory.PSL2.sl2FieldAut δ g) := by
      ext i j
      rfl
    exact congrArg (fun h => polynomialAction F h (X 0 ^ n)) he

private def sameSubmoduleEquiv {R M : Type*} [Field R] [AddCommGroup M] [Module R M]
    (U W : Submodule R M) (h : U = W) : U ≃ₗ[R] W where
  toFun v := ⟨v.val, by rw [← h]; exact v.property⟩
  invFun v := ⟨v.val, by rw [h]; exact v.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem sameSubmoduleEquiv_coe {R M : Type*} [Field R] [AddCommGroup M] [Module R M]
    (U W : Submodule R M) (h : U = W) (v : U) :
    (sameSubmoduleEquiv U W h v : M) = v := rfl

private theorem trace_sameSubmodule {R M : Type*} [Field R] [AddCommGroup M] [Module R M]
    (U W : Submodule R M) (h : U = W) (A : Module.End R U) (B : Module.End R W)
    (hAB : ∀ v : U, (A v : M) = (B (sameSubmoduleEquiv U W h v) : M)) :
    LinearMap.trace R U A = LinearMap.trace R W B := by
  subst W
  have he : A = B := by
    ext v : 1
    apply Subtype.ext
    exact hAB v
  rw [he]

private theorem subrepresentation_apply_coe {R Γ M : Type*} [Field R] [Monoid Γ]
    [AddCommGroup M] [Module R M] (τ : Representation R Γ M)
    (U : Subrepresentation τ) (g : Γ) (v : U.toSubmodule) :
    (U.toRepresentation g v : M) = τ g v := rfl

theorem highestWeightSpan_character_fieldAut (e : K →+* F) (δ : K ≃+* K)
    (n : ℕ) (g : SL(2,K)) :
    (highestWeightSpan e n).toRepresentation.character (Theory.PSL2.sl2FieldAut δ g) =
      (highestWeightSpan (e.comp δ.toRingHom) n).toRepresentation.character g := by
  apply trace_sameSubmodule _ _ (span_comp_fieldAut e δ n).symm
  intro v
  rw [subrepresentation_apply_coe, subrepresentation_apply_coe, sameSubmoduleEquiv_coe]
  change polynomialAction F (Matrix.SpecialLinearGroup.map e
    (Theory.PSL2.sl2FieldAut δ g)) v =
      polynomialAction F (Matrix.SpecialLinearGroup.map (e.comp δ.toRingHom) g) v
  have he : Matrix.SpecialLinearGroup.map e (Theory.PSL2.sl2FieldAut δ g) =
      Matrix.SpecialLinearGroup.map (e.comp δ.toRingHom) g := by
    ext i j
    rfl
  exact congrArg (fun h => polynomialAction F h v) he

end Representation.SL2

namespace Representation.SL2
variable {K V : Type*} [Field K] [Finite K] [CharP K 2]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (σ : Representation (ZMod 2) SL(2,K) V) [σ.IsIrreducible]

/-- Entrywise Frobenius acts as Frobenius on the actual Schur traces. -/
theorem endFieldRep_character_frobenius (m : ℕ) (g : SL(2,K)) :
    σ.endFieldRep.character (Theory.PSL2.sl2FieldAut (iterateFrobeniusEquiv K 2 m) g) =
      σ.endFieldRep.character g ^ (2 ^ m) := by
  let E := Module.End (ZMod 2)[SL(2,K)] σ.asModule
  let F := AlgebraicClosure E
  let : CharP E 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) E).injective 2
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap E F).injective 2
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let : IsAbsolutelyIrreducible σ.endFieldRep := endFieldRep_isAbsolutelyIrreducible σ
  let : IsIrreducible (extendScalars F σ.endFieldRep) :=
    IsAbsolutelyIrreducible.irreducible_of_extension σ.endFieldRep F
  let e : K →+* F := (IsAlgClosed.lift (R := ZMod 2) (S := K) (M := F)).toRingHom
  obtain ⟨n, ⟨φ⟩⟩ := exists_highestWeightSpan_equiv e 2 (extendScalars F σ.endFieldRep)
  have hchar (x : SL(2,K)) : (highestWeightSpan e n.val).toRepresentation.character x =
      algebraMap E F (σ.endFieldRep.character x) := by
    rw [← congrFun (Representation.char_iso φ) x]
    exact LinearMap.trace_baseChange (σ.endFieldRep x) F
  have he : e.comp (iterateFrobeniusEquiv K 2 m).toRingHom =
      (iterateFrobeniusEquiv F 2 m).toRingHom.comp e := by
    ext x
    exact map_pow e x (2 ^ m)
  apply (algebraMap E F).injective
  rw [map_pow, ← hchar, ← hchar, highestWeightSpan_character_fieldAut, he]
  exact highestWeightSpan_character_comp_embedding (iterateFrobeniusEquiv F 2 m) e n.val g

/-- An actual Schur-linear equivalence extending an inner times Frobenius
normalizer forces its Frobenius exponent to be a multiple of the Schur degree. -/
theorem schurDegree_dvd_of_field_intertwiner (m : ℕ) (c : SL(2,K))
    (T : σ.asModule ≃ₗ[Module.End (ZMod 2)[SL(2,K)] σ.asModule] σ.asModule)
    (hT : ∀ g v, T (σ.endFieldRep g v) =
      σ.endFieldRep (c * Theory.PSL2.sl2FieldAut (iterateFrobeniusEquiv K 2 m) g * c⁻¹)
        (T v)) : schurDegree 2 σ ∣ m := by
  apply (endFieldRep_trace_frobenius_iff 2 σ m).mp
  intro g
  have he : T.conj (σ.endFieldRep g) =
      σ.endFieldRep (c * Theory.PSL2.sl2FieldAut (iterateFrobeniusEquiv K 2 m) g * c⁻¹) := by
    ext v
    rw [LinearEquiv.conj_apply_apply, hT, T.apply_symm_apply]
  have hh := LinearMap.trace_conj' (σ.endFieldRep g) T
  rw [he] at hh
  change σ.endFieldRep.character (_ * _ * _) = σ.endFieldRep.character g at hh
  rw [Representation.char_conj, endFieldRep_character_frobenius] at hh
  exact hh
end Representation.SL2
