module

public import Theory.Representation.SL2.SteinbergParameters
public import Theory.Representation.EndFieldTrace
public import Theory.Representation.SL2.FrobeniusWeightPeriod
public import Theory.Representation.SL2.HighestWeightCentralSign
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Algebra.ZMod

/-!
# Highest-Weight Data for Prime-Field Representations

For a nontrivial finite-dimensional irreducible representation of SL2(K) over
GF(p), where p is an odd prime and |K| = p^m, let E be its actual Schur
endomorphism field and s = [E : GF(p)]. We obtain a nonzero highest weight
n < |K|, the divisibilities s | m and (|K| - 1) | n * (p^s - 1), and the
dimension s times the product of one plus the base-p digits of n. If the
central matrix -I is outside the original kernel, n is odd.

The existing endomorphism-field representation is absolutely irreducible.
Extend it to the algebraic closure of E and apply the concrete highest-weight
classification. Its traces span E; preservation of trace under scalar extension
and equivalence permits the Frobenius-period theorem to identify s. The
highest-weight dimension formula and the scalar-dimension tower give the
dimension. Identity actions descend through both scalar extension and the
actual intertwining equivalence, so the zero weight would make the original
action trivial. The same descent transfers the central sign test to its kernel.

These are the representation-theoretic parameters in the argument following
Fong--Wong (1.15), Nagoya Math. J. 36 (1969), p. 149. Repetition of digits and
the resulting low-degree bounds are separate arithmetic and assembly results.
-/

open scoped MatrixGroups MonoidAlgebra TensorProduct

open MvPolynomial

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



variable {K V : Type*} [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
    (ρ : Representation (ZMod p) SL(2,K) V) [ρ.IsIrreducible]

public theorem exists_primeField_highestWeight_parameters (hp2 : p ≠ 2)
    (hρ : ∃ g, ρ g ≠ 1) (m : ℕ) (hcard : Nat.card K = p ^ m) :
    let s := Module.finrank (ZMod p) (Module.End (ZMod p)[SL(2,K)] ρ.asModule)
    0 < s ∧ ∃ n : Fin (Nat.card K), 0 < n.val ∧ s ∣ m ∧
      (Nat.card K - 1) ∣ n.val * (p ^ s - 1) ∧
      Module.finrank (ZMod p) V = s * ∏ i : Fin m, (n.val / p ^ (i : ℕ) % p + 1) ∧
      ((-1 : SL(2,K)) ∉ ρ.ker → Odd n.val) := by
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
  let τ : SL(2,K) → E := fun g => LinearMap.trace E ρ.asModule (ρ.endFieldRep g)
  have hspan : Submodule.span (ZMod p) (Set.range τ) = ⊤ := span_range_endFieldRep_trace ρ
  have hchar (g : SL(2,K)) : (highestWeightSpan e n.val).toRepresentation.character g =
      algebraMap E F (τ g) := by
    rw [← congrFun (Representation.char_iso φ) g]
    exact LinearMap.trace_baseChange (ρ.endFieldRep g) F
  have hperiod := highestWeightSpan_traceField_period p e n.val m n.isLt hcard τ hspan hchar
  have htransport (g : SL(2,K)) (hg : (highestWeightSpan e n.val).toRepresentation g = 1) :
      ρ g = 1 :=
    (endFieldRep_eq_one_iff ρ g).mp
      ((extendScalars_eq_one_iff (F := F) ρ.endFieldRep g).mp (eq_one_of_equiv φ g hg))
  have hn0 : 0 < n.val := by
    by_contra! hz
    have hnzero : n.val = 0 := Nat.eq_zero_of_le_zero hz
    obtain ⟨g, hg⟩ := hρ
    apply hg
    apply htransport
    rw [hnzero]
    apply LinearMap.ext
    intro v
    exact highestWeightSpan_zero_apply e g v
  have hs : 0 < Module.finrank (ZMod p) E := by
    let : Module.Finite (ZMod p) E := Module.Finite.of_finite
    exact Module.finrank_pos
  refine ⟨hs, n, hn0, hperiod.1, hperiod.2, ?_, ?_⟩
  · have hd : Module.finrank E ρ.asModule =
        Module.finrank F (highestWeightSpan e n.val).toSubmodule := by
      rw [← Module.finrank_baseChange (R := F)]
      exact φ.toLinearEquiv.finrank_eq
    rw [highestWeightSpan_finrank_eq_prod_digits e p (Fact.out) n.val m hcard
      (by simpa only [← hcard] using n.isLt)] at hd
    rw [← hd, Module.finrank_mul_finrank (ZMod p) E ρ.asModule]
    exact ρ.asModuleEquiv.finrank_eq.symm

  · intro hneg
    by_contra! hodd
    have heven : Even n.val := Nat.not_odd_iff_even.mp hodd
    apply hneg
    apply htransport
    apply (highestWeightSpan_neg_one_mem_ker_iff e n.val ?_).mpr heven
    intro htwo
    have hpdiv : p ∣ 2 := (CharP.cast_eq_zero_iff F p 2).mp htwo
    have hp : p = 2 := (Nat.dvd_prime Nat.prime_two).mp hpdiv |>.resolve_left
      ((Fact.out : p.Prime).one_lt.ne')
    exact hp2 hp

end Representation.SL2
