module

public import Theory.Representation.SL2.BinaryInvolutionDisplacement.HighestWeight
public import Theory.Representation.SL2.SteinbergParameters
public import Theory.Representation.EndFieldRep
public import Theory.Representation.ScalarDescent
public import Mathlib.Algebra.Algebra.ZMod

/-!
# Half-dimension displacement for binary SL₂ irreducibles

Every nonidentity involution moves at least half of a nontrivial irreducible
binary representation of SL₂ over a finite characteristic-two field.

Regard the module over its actual Schur endomorphism field, extend to that
field's algebraic closure, and use the concrete highest-weight classification.
Nontriviality excludes weight zero. The monomial-pair calculation then gives
the bound over the closure. Kernel base change preserves displacement rank;
restriction to the prime field multiplies both ranks by the same Schur degree.
All comparisons use the actual intertwining maps and the original action.

Source: Guralnick–Malle, Classification of 2F-modules II, §3.5 and
Proposition 4.1(2), manuscript pp.20,22; Aschbacher–Smith, K.3.1,
printed pp.453–454. This result requires no small-module catalogue,
recognition hypothesis, degree window, or offender bound.
-/

open scoped MatrixGroups MonoidAlgebra TensorProduct
open MvPolynomial
open Representation.BinaryOffender.NaturalTensor
namespace Representation.SL2

private theorem highestWeightSpan_zero_apply {K F : Type*} [Field K] [Field F]
    (e : K →+* F) (g : SL(2,K)) (v : (highestWeightSpan e 0).toSubmodule) :
    (highestWeightSpan e 0).toRepresentation g v = v := by
  apply Subtype.ext
  change polynomialAction F (Matrix.SpecialLinearGroup.map e g) v = v
  have hfix (f : MvPolynomial (Fin 2) F) (hf : f ∈ highestWeightSpan e 0) :
      polynomialAction F (Matrix.SpecialLinearGroup.map e g) f = f := by
    change f ∈ Submodule.span F _ at hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨h, rfl⟩ := hf
      simp only [pow_zero, map_one]
    | zero => exact map_zero _
    | add f h _ _ hf hh => simp only [map_add, hf, hh]
    | smul a f _ hf => simp only [map_smul, hf]
  exact hfix v v.property

private theorem extendScalars_eq_one_iff {E F G W : Type*} [Field E] [Field F]
    [Algebra E F] [Monoid G] [AddCommGroup W] [Module E W]
    (σ : Representation E G W) (g : G) : extendScalars F σ g = 1 ↔ σ g = 1 := by
  constructor
  · intro h
    ext v
    apply (Module.FaithfullyFlat.tensorProduct_mk_injective (A := E) (B := F) W)
    have hh := congrArg (fun f : Module.End F (F ⊗[E] W) => f (1 ⊗ₜ[E] v)) h
    exact hh
  · intro h
    simp only [extendScalars_apply, h, LinearMap.baseChange_one]

private theorem eq_one_of_equiv {F G V W : Type*} [Field F] [Monoid G]
    [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    {ρ : Representation F G V} {σ : Representation F G W} (φ : ρ.Equiv σ)
    (g : G) (h : σ g = 1) : ρ g = 1 := by
  ext v
  apply φ.toLinearEquiv.injective
  change φ (ρ g v) = φ v
  have hc := Representation.IntertwiningMap.isIntertwining ρ σ φ.toIntertwiningMap g v
  rw [h] at hc
  convert hc using 1
  all_goals rfl

private theorem endFieldRep_eq_one_iff {F G V : Type*} [Field F] [Monoid G]
    [AddCommGroup V] [Module F V] (ρ : Representation F G V) (g : G) :
    ρ.endFieldRep g = 1 ↔ ρ g = 1 := by
  constructor
  · intro h
    ext v
    have hh := congrArg (fun f : Module.End (Module.End F[G] ρ.asModule) ρ.asModule =>
      ρ.asModuleEquiv (f (ρ.asModuleEquiv.symm v))) h
    simpa only [endFieldRep_apply, LinearEquiv.apply_symm_apply, Module.End.one_apply] using hh
  · intro h
    ext v
    simp only [endFieldRep_apply, h, Module.End.one_apply, LinearEquiv.symm_apply_apply]




private theorem displacement_rank_extendScalars {E F G W : Type*}
    [Field E] [Field F] [Algebra E F] [Group G]
    [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    (ρ : Representation E G W) (g : G) :
    operatorFixedCodim (extendScalars F ρ g) = operatorFixedCodim (ρ g) := by
  have hk := (LinearMap.kerBaseChangeEquiv (E := F) (ρ g - 1)).finrank_eq
  rw [Module.finrank_baseChange, LinearMap.baseChange_sub, LinearMap.baseChange_one] at hk
  have hF := operatorFixedCodim_add_finrank (extendScalars F ρ g)
  have hE := operatorFixedCodim_add_finrank (ρ g)
  rw [Module.finrank_baseChange] at hF
  change Module.finrank E (ρ g - 1).ker =
    Module.finrank F (extendScalars F ρ g - 1).ker at hk
  omega

private theorem displacement_rank_endField {k G W : Type*} [Field k] [Finite k]
    [Group G] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (ρ : Representation k G W) [ρ.IsIrreducible] (g : G) :
    operatorFixedCodim (ρ g) = Module.finrank k (Module.End k[G] ρ.asModule) *
      operatorFixedCodim (ρ.endFieldRep g) := by
  let E := Module.End k[G] ρ.asModule
  let A := ρ.endFieldRep g
  have he := operatorFixedCodim_eq_of_equiv (A.restrictScalars k) (ρ g)
    ρ.asModuleEquiv (fun v => by
      change ρ.asModuleEquiv (ρ.endFieldRep g v) = ρ g (ρ.asModuleEquiv v)
      rw [endFieldRep_apply, LinearEquiv.apply_symm_apply])
  rw [← he]
  change Module.finrank k (((A - 1).restrictScalars k).range) =
    Module.finrank k E * Module.finrank E (A - 1).range
  rw [LinearMap.range_restrictScalars,
    ((A - 1).range.restrictScalarsEquiv k).restrictScalars k |>.finrank_eq,
    Module.finrank_mul_finrank]

/-- Every nonidentity involution moves at least half of a nontrivial irreducible
binary representation of the actual matrix group SL₂(K). -/
public theorem binary_involution_displacement {K V : Type*}
    [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL(2,K) V) [ρ.IsIrreducible]
    (hρ : ∃ g, ρ g ≠ 1) (g : SL(2,K)) (hg : g ≠ 1) (hg2 : g ^ 2 = 1) :
    Module.finrank (ZMod 2) V ≤
      2 * Module.finrank (ZMod 2) (LinearMap.range (ρ g - 1)) := by
  let E := Module.End (ZMod 2)[SL(2,K)] ρ.asModule
  let F := AlgebraicClosure E
  let : CharP E 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) E).injective 2
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap E F).injective 2
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let : Finite ρ.asModule := Module.finite_iff_finite.mp
    (inferInstance : Module.Finite (ZMod 2) ρ.asModule)
  let : Module.Finite E ρ.asModule := Module.Finite.of_finite
  let : IsAbsolutelyIrreducible ρ.endFieldRep := endFieldRep_isAbsolutelyIrreducible ρ
  let : IsIrreducible (extendScalars F ρ.endFieldRep) :=
    IsAbsolutelyIrreducible.irreducible_of_extension ρ.endFieldRep F
  let e : K →+* F := (IsAlgClosed.lift (R := ZMod 2) (S := K) (M := F)).toRingHom
  obtain ⟨n, ⟨φ⟩⟩ := exists_highestWeightSpan_equiv e 2 (extendScalars F ρ.endFieldRep)
  have htransport (x : SL(2,K)) (hx : (highestWeightSpan e n.val).toRepresentation x = 1) :
      ρ x = 1 :=
    (endFieldRep_eq_one_iff ρ x).mp
      ((extendScalars_eq_one_iff (F := F) ρ.endFieldRep x).mp (eq_one_of_equiv φ x hx))
  have hn0 : 0 < n.val := by
    by_contra! hz
    have hnzero : n.val = 0 := Nat.eq_zero_of_le_zero hz
    obtain ⟨x, hx⟩ := hρ
    apply hx
    apply htransport
    rw [hnzero]
    apply LinearMap.ext
    intro v
    exact highestWeightSpan_zero_apply e x v
  have hbound := BinaryInvolutionDisplacement.highestWeight_involution_bound
    e n.val n.isLt hn0 g hg hg2
  have hd := φ.toLinearEquiv.finrank_eq
  have hr := operatorFixedCodim_eq_of_equiv
    (extendScalars F ρ.endFieldRep g) ((highestWeightSpan e n.val).toRepresentation g)
    φ.toLinearEquiv (fun v =>
      Representation.IntertwiningMap.isIntertwining _ _ φ.toIntertwiningMap g v)
  rw [← hr, ← hd, Module.finrank_baseChange, displacement_rank_extendScalars] at hbound
  have hmul := Nat.mul_le_mul_left (Module.finrank (ZMod 2) E) hbound
  rw [Module.finrank_mul_finrank, ρ.asModuleEquiv.finrank_eq] at hmul
  have hdisp := displacement_rank_endField ρ g
  change operatorFixedCodim (ρ g) = Module.finrank (ZMod 2) E *
    operatorFixedCodim (ρ.endFieldRep g) at hdisp
  change Module.finrank (ZMod 2) V ≤ 2 * operatorFixedCodim (ρ g)
  nlinarith [hmul]

end Representation.SL2
