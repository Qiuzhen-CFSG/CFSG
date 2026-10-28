module

public import Theory.Representation.BinaryOffender.SchurNormalizerDisplacement
public import Theory.Representation.ReeF4.BinaryDegree.SchurDescent
public import Theory.Representation.InvariantsBaseChange


/-!
# Scalar extension of a Schur-linear normalizer subgroup

Every operator of the specified subgroup commutes with the component Schur
field, hence acts on that actual scalar module and its algebraic closure.
Their common fixed equations are unchanged. The dimension tower and exactness
of scalar extension give the binary fixed codimension as the Schur degree
times the absolute fixed codimension. The actor subgroup need not act
irreducibly; irreducibility is used only for the original component.

This is the scalar transport for Guralnick--Malle, Classification of 2F-modules
II, Proposition 4.11, internal pp.31--32. The source consumer is the Chapter K
SchurOuter module; no natural recognition or binary absolute irreducibility is
assumed.
-/

public section

open scoped MonoidAlgebra TensorProduct
open Representation Representation.BinaryOffender Representation.FrobeniusTensor
namespace Representation.SU3.CubicDegree.SchurOuter
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (σ : Representation (ZMod 2) G V) [σ.IsIrreducible]
  (A : Subgroup (linearNormalizer σ))
  (hl : ∀ t ∈ A, SchurNormalizer.IsSchurLinear σ t)

/-- The same subgroup acts linearly over the component Schur field. -/
@[expose] noncomputable def schurActorRepresentation : Representation (SchurField σ) A σ.asModule where
  toFun a := {
    toFun v := σ.asModuleEquiv.symm (a.val.val.val (σ.asModuleEquiv v))
    map_add' v w := by simp
    map_smul' c v := by
      apply σ.asModuleEquiv.injective
      exact (SchurNormalizer.isSchurLinear_iff_endField σ a.val).mp (hl a.val a.property) c v }
  map_one' := by ext v; rfl
  map_mul' a b := by ext v; rfl

omit [FiniteDimensional (ZMod 2) V] [σ.IsIrreducible] in
/-- The Schur-field actor retains the original operator on every vector. -/
theorem schurActorRepresentation_apply (a : A) (v : σ.asModule) :
    σ.asModuleEquiv (schurActorRepresentation σ A hl a v) =
      normalizerRepresentation σ a (σ.asModuleEquiv v) := rfl

/-- Extend the actual actor representation to the algebraic closure. -/
@[expose] noncomputable def absoluteActorRepresentation :
    Representation (Closure σ) A (AbsoluteSpace σ) :=
  extendScalars (Closure σ) (schurActorRepresentation σ A hl)

private noncomputable def fixedEquiv :
    (schurActorRepresentation σ A hl).invariants ≃ₗ[ZMod 2]
      fixedSpace (normalizerRepresentation σ) A where
  toFun v := ⟨σ.asModuleEquiv v, fun a => congrArg σ.asModuleEquiv (v.property a)⟩
  invFun v := ⟨σ.asModuleEquiv.symm v,
    fun a => congrArg σ.asModuleEquiv.symm (v.property a)⟩
  left_inv v := Subtype.ext (σ.asModuleEquiv.symm_apply_apply v)
  right_inv v := Subtype.ext (σ.asModuleEquiv.apply_symm_apply v)
  map_add' v w := Subtype.ext (σ.asModuleEquiv.map_add v w)
  map_smul' c v := Subtype.ext (σ.asModuleEquiv.map_smul c v)

/-- Common fixed codimension scales by exactly the component Schur degree. -/
theorem fixedCodim_eq_schur_mul :
    fixedCodim (normalizerRepresentation σ) A =
      Module.finrank (ZMod 2) (SchurField σ) *
        Module.finrank (Closure σ)
          (AbsoluteSpace σ ⧸ (absoluteActorRepresentation σ A hl).invariants) := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (Module.End (ZMod 2) V) := Finite.of_injective
    (fun f : Module.End (ZMod 2) V => (f : V → V)) DFunLike.coe_injective
  have hf : Module.finrank (ZMod 2) (fixedSpace (normalizerRepresentation σ) A) =
      Module.finrank (ZMod 2) (SchurField σ) *
        Module.finrank (Closure σ) (absoluteActorRepresentation σ A hl).invariants := by
    rw [absoluteActorRepresentation, finrank_invariants_extendScalars_eq_of_finite,
      Module.finrank_mul_finrank]
    exact (fixedEquiv σ A hl).finrank_eq.symm
  have hc := fixedCodim_add_finrank (normalizerRepresentation σ) A
  have hq := (absoluteActorRepresentation σ A hl).invariants.finrank_quotient_add_finrank
  rw [hf, binary_finrank_eq σ, ← hq, Nat.mul_add] at hc
  exact Nat.add_right_cancel hc

end Representation.SU3.CubicDegree.SchurOuter
