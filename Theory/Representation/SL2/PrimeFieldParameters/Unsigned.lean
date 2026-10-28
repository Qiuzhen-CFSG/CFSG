module

public import Theory.Representation.SL2.PrimeFieldParameters
public import Theory.Representation.SL2.OrbitDimensionBounds
public import Theory.Combinatorics.PeriodicDigitProduct
/-!
# Highest-weight degree bounds without the central-sign restriction

The prime-field descent and Frobenius-period argument work in every prime
characteristic. Only the separate parity conclusion for the central matrix
minus one requires odd characteristic. Retaining the nonzero highest weight,
Schur degree and digit-product formula gives dimension s*b^t with m=s*t and
b≥2. Thus every nontrivial irreducible defining-characteristic SL₂ module
has prime-field dimension at least 2m, including characteristic two.

This separate extension preserves the existing odd-characteristic API and
supplies the genuine binary degree input used in Aschbacher–Smith E.2.13(4),
printed p.225. It uses the actual highest-weight classification and Schur
endomorphism field, with no additional recognition premise.
-/

public section
open scoped MatrixGroups MonoidAlgebra TensorProduct
open MvPolynomial
namespace Representation.SL2.Unsigned
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

theorem exists_primeField_highestWeight_parameters
    (hρ : ∃ g, ρ g ≠ 1) (m : ℕ) (hcard : Nat.card K = p ^ m) :
    let s := Module.finrank (ZMod p) (Module.End (ZMod p)[SL(2,K)] ρ.asModule)
    0 < s ∧ ∃ n : Fin (Nat.card K), 0 < n.val ∧ s ∣ m ∧
      (Nat.card K - 1) ∣ n.val * (p ^ s - 1) ∧
      Module.finrank (ZMod p) V = s * ∏ i : Fin m, (n.val / p ^ (i : ℕ) % p + 1) := by
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
  refine ⟨hs, n, hn0, hperiod.1, hperiod.2, ?_⟩
  · have hd : Module.finrank E ρ.asModule =
        Module.finrank F (highestWeightSpan e n.val).toSubmodule := by
      rw [← Module.finrank_baseChange (R := F)]
      exact φ.toLinearEquiv.finrank_eq
    rw [highestWeightSpan_finrank_eq_prod_digits e p (Fact.out) n.val m hcard
      (by simpa only [← hcard] using n.isLt)] at hd
    rw [← hd, Module.finrank_mul_finrank (ZMod p) E ρ.asModule]
    exact ρ.asModuleEquiv.finrank_eq.symm


theorem irreducible_finrank_bound
    (hρ : ∃ g, ρ g ≠ 1) (m : ℕ) (hm : m ≠ 0) (hcard : Nat.card K = p ^ m) :
    2 * m ≤ Module.finrank (ZMod p) V := by
  let s := Module.finrank (ZMod p) (Module.End (ZMod p)[SL(2,K)] ρ.asModule)
  obtain ⟨hs, n, hn, hsdiv, hperiod, hdim⟩ :=
    exists_primeField_highestWeight_parameters p ρ hρ m hcard
  obtain ⟨t, hmt⟩ := hsdiv
  have ht : 0 < t := by
    by_contra! h
    have : t = 0 := Nat.eq_zero_of_le_zero h
    simp only [this, mul_zero] at hmt
    exact hm hmt
  have hnlt : n.val < p ^ (s*t) := by
    rw [← hmt, ← hcard]
    exact n.isLt
  have hper : (p ^ (s*t) - 1) ∣ n.val * (p ^ s - 1) := by
    simpa only [hcard, hmt] using hperiod
  obtain ⟨b, hb, hprod, _⟩ := Nat.exists_digit_product_pow_of_period p s t n.val
    (Fact.out : p.Prime).two_le hs ht hn hnlt hper
  rw [hdim, hmt, hprod]
  exact orbit_dimension_lower_bound ht hb
end Representation.SL2.Unsigned
