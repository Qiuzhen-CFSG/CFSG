module

public import Theory.Representation.SL2.SteinbergParameters
public import Theory.Representation.SL2.UpperFixedDimension
public import Theory.Representation.EndFieldInvariants
public import Theory.Representation.InvariantsBaseChange
public import Theory.Representation.SylowInvariantDimension
public import Mathlib.Algebra.Algebra.ZMod

/-!
# Sylow Fixed Dimensions over the Prime Field

For a finite field K of characteristic p and an irreducible finite-dimensional
GF(p)-representation of SL2(K), the dimension fixed by any Sylow p-subgroup is
the degree of its actual Schur endomorphism field over GF(p). Faithfulness and
odd characteristic are not needed for this intermediate result.

Extend the existing endFieldRep to its algebraic closure and classify it by
an actual highest-weight orbit span. The actual intertwining equivalence
restricts to invariant subspaces. Sylow conjugacy transfers the upper
fixed-line computation to the chosen Sylow, giving dimension one over the
closure. Modular invariant base change descends this to the Schur field,
and its original scalar tower multiplies the dimension by that field's degree.

This is the fixed-space descent used for Alperin--Brauer--Gorenstein II.4,
Lemma 18(ii), article pp. 45--46. The minimal-dimension theorem separately
identifies the Schur degree with the finite-field extension exponent.
-/

open scoped MatrixGroups MonoidAlgebra TensorProduct

namespace Representation.SL2

private noncomputable def invariantsEquivOfEquiv {F G V W : Type*} [Field F] [Group G]
    [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    {ρ : Representation F G V} {σ : Representation F G W} (φ : ρ.Equiv σ) :
    ρ.invariants ≃ₗ[F] σ.invariants where
  toFun v := ⟨φ v, by
    intro g
    have h := Representation.IntertwiningMap.isIntertwining ρ σ φ.toIntertwiningMap g v
    rw [v.property g] at h
    convert h.symm using 1 <;> rfl⟩
  invFun v := ⟨φ.symm v, by
    intro g
    have h := Representation.IntertwiningMap.isIntertwining σ ρ φ.symm.toIntertwiningMap g v
    rw [v.property g] at h
    convert h.symm using 1 <;> rfl⟩
  left_inv v := Subtype.ext (φ.toLinearEquiv.symm_apply_apply v)
  right_inv v := Subtype.ext (φ.toLinearEquiv.apply_symm_apply v)
  map_add' x y := Subtype.ext (map_add φ (x : V) (y : V))
  map_smul' a v := Subtype.ext (map_smul φ a (v : V))

public theorem finrank_sylow_invariants_eq_endField {K V : Type*} [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [AddCommGroup V] [Module (ZMod p) V]
    [FiniteDimensional (ZMod p) V] (ρ : Representation (ZMod p) SL(2,K) V)
    [ρ.IsIrreducible] (P : Sylow p SL(2,K)) :
    Module.finrank (ZMod p) (Representation.invariants (ρ.comp P.toSubgroup.subtype)) =
      Module.finrank (ZMod p) (Module.End (ZMod p)[SL(2,K)] ρ.asModule) := by
  let E := Module.End (ZMod p)[SL(2,K)] ρ.asModule
  let F := AlgebraicClosure E
  let : CharP E p := charP_of_injective_algebraMap (algebraMap (ZMod p) E).injective p
  let : CharP F p := charP_of_injective_algebraMap (algebraMap E F).injective p
  let : Algebra (ZMod p) K := ZMod.algebra K p
  let : Algebra (ZMod p) F := ZMod.algebra F p
  let : Finite ρ.asModule := Module.finite_iff_finite.mp
    (inferInstance : Module.Finite (ZMod p) ρ.asModule)
  let : Module.Finite E ρ.asModule := Module.Finite.of_finite
  let : IsAbsolutelyIrreducible ρ.endFieldRep := endFieldRep_isAbsolutelyIrreducible ρ
  let : IsIrreducible (extendScalars F ρ.endFieldRep) :=
    IsAbsolutelyIrreducible.irreducible_of_extension ρ.endFieldRep F
  let e : K →+* F := (IsAlgClosed.lift (R := ZMod p) (S := K) (M := F)).toRingHom
  obtain ⟨n, ⟨φ⟩⟩ := exists_highestWeightSpan_equiv e p (extendScalars F ρ.endFieldRep)
  let φP : Representation.Equiv ((extendScalars F ρ.endFieldRep).comp P.toSubgroup.subtype)
      ((highestWeightSpan e n.val).toRepresentation.comp P.toSubgroup.subtype) :=
    Representation.Equiv.mk φ.toLinearEquiv (fun g => φ.isIntertwining' g.val)
  have hfixed : Module.finrank F (Representation.invariants
      ((extendScalars F ρ.endFieldRep).comp P.toSubgroup.subtype)) = 1 := by
    rw [(invariantsEquivOfEquiv φP).finrank_eq]
    rw [finrank_invariants_sylow_eq (highestWeightSpan e n.val).toRepresentation p P
      (Matrix.SpecialLinearGroup.upperUnipotentSylow K p)]
    exact highestWeightSpan_upper_invariants_finrank e n.val n.isLt
  have hbase := finrank_invariants_extendScalars_eq_of_finite (E := F)
    (ρ.endFieldRep.comp P.toSubgroup.subtype)
  have hE : Module.finrank E (Representation.invariants (ρ.endFieldRep.comp P.toSubgroup.subtype)) = 1 :=
    hbase.symm.trans hfixed
  rw [finrank_invariants_eq_endField_mul ρ P.toSubgroup, hE, mul_one]

end Representation.SL2
