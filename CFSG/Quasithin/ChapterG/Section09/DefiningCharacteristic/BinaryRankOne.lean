module

public import Theory.Representation.SL2.SteinbergParameters
public import Theory.Representation.EndFieldTrace
public import Theory.Representation.SL2.FrobeniusWeightPeriod
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Algebra.ZMod
public import Theory.Combinatorics.PeriodicDigitProduct
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Binary SL₂ highest weights and small degrees

The concrete highest-weight classification works in characteristic two. We
apply it to the scalar extension of the actual Schur-field representation;
the trace-field theorem gives its Frobenius period. Binary digits make every
restricted factor have degree one or two. A repeated block therefore gives
`n = s*t` and `d = s*(2^a)^t`, where `s` is the actual Schur-field degree.

The bound `d ≤ 2*(n+1)`, for `n ≥ 2`, forces `a = 1` and either `t = 1`,
`t = 2`, or `s = 1, t = 3`. Consequently the absolute degrees are two,
four, or (only over the field of eight elements) eight. The highest-weight
result retains an actual representation equivalence after scalar extension.
Identification with the natural, orthogonal and triple-tensor modules is
still a separate obligation; dimension alone does not identify a module.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), G.9.3,
printed pp.354,356--357; GLS volume 3, 2.8.6, 2.8.8 and 2.8.10(b).
The scalar-descent argument extends the odd-characteristic argument in
`Theory.Representation.SL2.PrimeFieldParameters` without changing that API.
-/

public section

open scoped MatrixGroups MonoidAlgebra TensorProduct
open MvPolynomial
open Representation Representation.SL2

namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic
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

private theorem binary_digit_product (k n : ℕ) :
    (∏ i : Fin k, (n / 2 ^ (i : ℕ) % 2 + 1)) =
      2 ^ (∑ i : Fin k, (n / 2 ^ (i : ℕ) % 2)) := by
  have h (i : Fin k) : n / 2 ^ (i : ℕ) % 2 + 1 = 2 ^ (n / 2 ^ (i : ℕ) % 2) := by
    have := Nat.mod_lt (n / 2 ^ (i : ℕ)) (by decide : 0 < 2)
    interval_cases n / 2 ^ (i : ℕ) % 2 <;> rfl
  simp_rw [h]
  exact Finset.prod_pow_eq_pow_sum _ _ _

private theorem four_mul_le_four_pow {t : ℕ} (ht : 1 ≤ t) : 4 * t ≤ 4 ^ t := by
  induction t, ht using Nat.le_induction with
  | base => norm_num
  | succ t ht ih => rw [pow_succ]; nlinarith

private theorem four_mul_le_two_pow {t : ℕ} (ht : 4 ≤ t) : 4 * t ≤ 2 ^ t := by
  induction t, ht using Nat.le_induction with
  | base => norm_num
  | succ t ht ih => rw [pow_succ]; nlinarith

/-- The small binary orbit dimensions, retaining the actual Schur degree. -/
theorem binary_small_orbit_parameters {s t a : ℕ}
    (hs : 0 < s) (ht : 0 < t) (ha : 0 < a) (hn : 2 ≤ s * t)
    (hd : s * (2 ^ a) ^ t ≤ 2 * (s * t + 1)) :
    a = 1 ∧ (t = 1 ∨ t = 2 ∨ (s = 1 ∧ t = 3)) := by
  have ha1 : a = 1 := by
    by_contra h
    have ha2 : 2 ≤ a := by omega
    have hb : 4 ≤ 2 ^ a := (by norm_num : 4 = 2 ^ 2) ▸
      Nat.pow_le_pow_right (by decide : 0 < 2) ha2
    have hp := (four_mul_le_four_pow ht).trans (Nat.pow_le_pow_left hb t)
    have hm := Nat.mul_le_mul_left s hp
    nlinarith
  refine ⟨ha1, ?_⟩
  rw [ha1, pow_one] at hd
  have ht4 : t < 4 := by
    by_contra h
    have hp := four_mul_le_two_pow (by omega : 4 ≤ t)
    have hm := Nat.mul_le_mul_left s hp
    nlinarith
  rcases (by omega : t = 1 ∨ t = 2 ∨ t = 3) with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · right; right
    rw [h] at hd
    norm_num at hd
    exact ⟨by omega, h⟩


variable {K V : Type*} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL(2,K) V) [ρ.IsIrreducible]

/-- Nonzero highest weight, actual Schur-field period and scalar-extension
equivalence for every nontrivial binary irreducible representation. -/
theorem exists_binary_highestWeight_parameters
    (hρ : ∃ g, ρ g ≠ 1) (m : ℕ) (hcard : Nat.card K = 2 ^ m) :
    let s := Module.finrank (ZMod 2) (Module.End (ZMod 2)[SL(2,K)] ρ.asModule)
    0 < s ∧ ∃ n : Fin (Nat.card K), 0 < n.val ∧ s ∣ m ∧
      (Nat.card K - 1) ∣ n.val * (2 ^ s - 1) ∧
      Module.finrank (ZMod 2) V = s * ∏ i : Fin m, (n.val / 2 ^ (i : ℕ) % 2 + 1) ∧
      ∃ e : K →+* AlgebraicClosure (Module.End (ZMod 2)[SL(2,K)] ρ.asModule),
        Nonempty ((extendScalars (AlgebraicClosure (Module.End (ZMod 2)[SL(2,K)]
          ρ.asModule)) ρ.endFieldRep).Equiv (highestWeightSpan e n.val).toRepresentation) := by
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
  let τ : SL(2,K) → E := fun g => LinearMap.trace E ρ.asModule (ρ.endFieldRep g)
  have hspan : Submodule.span (ZMod 2) (Set.range τ) = ⊤ := span_range_endFieldRep_trace ρ
  have hchar (g : SL(2,K)) : (highestWeightSpan e n.val).toRepresentation.character g =
      algebraMap E F (τ g) := by
    rw [← congrFun (Representation.char_iso φ) g]
    exact LinearMap.trace_baseChange (ρ.endFieldRep g) F
  have hperiod := highestWeightSpan_traceField_period 2 e n.val m n.isLt hcard τ hspan hchar
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
  have hs : 0 < Module.finrank (ZMod 2) E := by
    let : Module.Finite (ZMod 2) E := Module.Finite.of_finite
    exact Module.finrank_pos
  refine ⟨hs, n, hn0, hperiod.1, hperiod.2, ?_, e, ⟨φ⟩⟩
  have hd : Module.finrank E ρ.asModule =
      Module.finrank F (highestWeightSpan e n.val).toSubmodule := by
    rw [← Module.finrank_baseChange (R := F)]
    exact φ.toLinearEquiv.finrank_eq
  rw [highestWeightSpan_finrank_eq_prod_digits e 2 (Fact.out) n.val m hcard
    (by simpa only [← hcard] using n.isLt)] at hd
  rw [← hd, Module.finrank_mul_finrank (ZMod 2) E ρ.asModule]
  exact ρ.asModuleEquiv.finrank_eq.symm



/-- Genuine Frobenius-orbit parameters for a nontrivial binary irreducible. -/
theorem exists_binary_orbit_parameters (hρ : ∃ g, ρ g ≠ 1)
    (m : ℕ) (hm : 0 < m) (hcard : Nat.card K = 2 ^ m) :
    let s := Module.finrank (ZMod 2) (Module.End (ZMod 2)[SL(2,K)] ρ.asModule)
    0 < s ∧ ∃ t a : ℕ, 0 < t ∧ 0 < a ∧ m = s * t ∧
      Module.finrank (ZMod 2) V = s * (2 ^ a) ^ t := by
  let s := Module.finrank (ZMod 2) (Module.End (ZMod 2)[SL(2,K)] ρ.asModule)
  obtain ⟨hs, n, hn, hsdiv, hperiod, hdim, _⟩ :=
    exists_binary_highestWeight_parameters ρ hρ m hcard
  obtain ⟨t, hmt⟩ := hsdiv
  have ht : 0 < t := by
    by_contra! h
    have : t = 0 := Nat.eq_zero_of_le_zero h
    simp only [this, mul_zero] at hmt
    omega
  have hnlt : n.val < 2 ^ (s * t) := by
    rw [← hmt, ← hcard]
    exact n.isLt
  have hper : (2 ^ (s * t) - 1) ∣ n.val * (2 ^ s - 1) := by
    simpa only [hcard, hmt] using hperiod
  obtain ⟨b, hb, hprod, _⟩ := Nat.exists_digit_product_pow_of_period 2 s t n.val
    (by decide) hs ht hn hnlt hper
  have hpow : b ^ t = 2 ^ (∑ i : Fin (s * t), (n.val / 2 ^ (i : ℕ) % 2)) := by
    rw [← hprod, binary_digit_product]
  have hbdiv : b ∣ 2 ^ (∑ i : Fin (s * t), (n.val / 2 ^ (i : ℕ) % 2)) := by
    rw [← hpow]
    exact dvd_pow_self b ht.ne'
  obtain ⟨a, _, hba⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hbdiv
  have ha : 0 < a := by
    by_contra! h
    have : a = 0 := Nat.eq_zero_of_le_zero h
    simp only [this, pow_zero] at hba
    omega
  refine ⟨hs, t, a, ht, ha, hmt, ?_⟩
  rw [hdim, hmt, hprod, hba]

/-- Under the G.9 degree bound the actual Schur degree gives the two minimal
possibilities or the exceptional eight-dimensional module over GF(2). -/
theorem binary_small_degree_schur_alternatives (hρ : ∃ g, ρ g ≠ 1)
    (n : ℕ) (hn : 2 ≤ n) (hcard : Nat.card K = 2 ^ n)
    (hd : Module.finrank (ZMod 2) V ≤ 2 * (n + 1)) :
    let s := Module.finrank (ZMod 2) (Module.End (ZMod 2)[SL(2,K)] ρ.asModule)
    (s = n ∧ Module.finrank (ZMod 2) V = 2 * n) ∨
      (2 * s = n ∧ Module.finrank (ZMod 2) V = 2 * n) ∨
      (s = 1 ∧ n = 3 ∧ Module.finrank (ZMod 2) V = 8) := by
  obtain ⟨hs, t, a, ht, ha, hnt, hdim⟩ :=
    exists_binary_orbit_parameters ρ hρ n (by omega) hcard
  have hsmall := hd
  rw [hdim, hnt] at hsmall
  obtain ⟨rfl, ht1 | ht2 | ⟨hs1, ht3⟩⟩ :=
    binary_small_orbit_parameters hs ht ha (hnt ▸ hn) hsmall
  · left
    subst t
    simp only [pow_one, mul_one] at hnt hdim
    constructor <;> omega
  · right; left
    subst t
    norm_num at hdim
    constructor <;> omega
  · right; right
    subst t
    rw [hs1] at hnt hdim
    norm_num at hnt hdim
    exact ⟨hs1, hnt, hdim⟩

/-- Degree-only consequence; module recognition is a further obligation. -/
theorem binary_small_degree_alternatives (hρ : ∃ g, ρ g ≠ 1)
    (n : ℕ) (hn : 2 ≤ n) (hcard : Nat.card K = 2 ^ n)
    (hd : Module.finrank (ZMod 2) V ≤ 2 * (n + 1)) :
    Module.finrank (ZMod 2) V = 2 * n ∨
      (n = 3 ∧ Module.finrank (ZMod 2) V = 8) := by
  rcases binary_small_degree_schur_alternatives ρ hρ n hn hcard hd with
    h | h | h
  · exact Or.inl h.2
  · exact Or.inl h.2
  · exact Or.inr h.2


/-- Absolute degrees of the actual Schur-field representation in the small
binary range. This is suitable for the two-component degree induction. -/
theorem binary_small_absolute_degree_alternatives (hρ : ∃ g, ρ g ≠ 1)
    (n : ℕ) (hn : 2 ≤ n) (hcard : Nat.card K = 2 ^ n)
    (hd : Module.finrank (ZMod 2) V ≤ 2 * (n + 1)) :
    let E := Module.End (ZMod 2)[SL(2,K)] ρ.asModule
    let s := Module.finrank (ZMod 2) E
    let k := Module.finrank E ρ.asModule
    (s = n ∧ k = 2) ∨ (2 * s = n ∧ k = 4) ∨ (s = 1 ∧ n = 3 ∧ k = 8) := by
  let E := Module.End (ZMod 2)[SL(2,K)] ρ.asModule
  have ht : Module.finrank (ZMod 2) V =
      Module.finrank (ZMod 2) E * Module.finrank E ρ.asModule := by
    rw [Module.finrank_mul_finrank]
    exact ρ.asModuleEquiv.finrank_eq.symm
  have hs : 0 < Module.finrank (ZMod 2) E :=
    (exists_binary_highestWeight_parameters ρ hρ n hcard).1
  rcases binary_small_degree_schur_alternatives ρ hρ n hn hcard hd with h | h | h
  · left
    exact ⟨h.1, by nlinarith [h.2]⟩
  · right; left
    exact ⟨h.1, by nlinarith [h.2]⟩
  · right; right
    exact ⟨h.1, h.2.1, by nlinarith [h.2.2]⟩

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic
