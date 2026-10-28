module
public import Theory.Representation.SL2.PrimeFieldParameters.Unsigned

/-!
# The highest weight of the source cubic radical module

An irreducible binary SL₂(2^(3n)) module of dimension 8n has Schur degree n.
The existing highest-weight classification and trace-field period give a
repeated binary digit block. The dimension bounds force three repetitions;
the block has one nonzero digit. Thus its actual Schur-field extension is
isomorphic to the polynomial orbit span of weight
2^j + 2^(j+n) + 2^(j+2n), for j<n.

This proves the representation-selection step in Fong--Seitz II (4.7)(b),
used on printed p.218. TensorAction constructs the intertwiner with the
three actual natural factors. The companion TensorApplication applies it
to the same quotient's radical action. This calculation includes n=1 and
does not identify the root-coordinate basis or assert the remaining source
matrix equations.
-/

@[expose] public noncomputable section
open scoped MatrixGroups MonoidAlgebra
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource.TensorWeights

private def digits (k w : ℕ) : ℕ := ∏ i : Fin k, (w / 2^i.val % 2+1)

private theorem digits_succ (k w : ℕ) :
    digits (k+1) w = (w%2+1)*digits k (w/2) := by
  rw [digits,Fin.prod_univ_succ]
  simp only [Fin.val_zero,pow_zero,Nat.div_one]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  simp only [Fin.val_succ,pow_succ,Nat.div_div_eq_div_mul,mul_comm]

private theorem digits_pos (k w : ℕ) : 0 < digits k w :=
  Finset.prod_pos (fun _ _ => Nat.zero_lt_succ _)

private theorem digits_one (k w : ℕ) (hw : w < 2^k) (hd : digits k w = 1) : w = 0 := by
  induction k generalizing w with
  | zero => simpa using hw
  | succ k ih =>
    rw [digits_succ] at hd
    have hdiv : w/2 < 2^k := Nat.div_lt_of_lt_mul (by simpa only [pow_succ'] using hw)
    have hd1 : digits k (w/2) = 1 := Nat.eq_one_of_mul_eq_one_left hd
    have hz := ih (w/2) hdiv hd1
    have hm : w%2 = 0 := by nlinarith
    have he := Nat.mod_add_div w 2
    omega

private theorem digits_two (k w : ℕ) (hw : w < 2^k) (hd : digits k w = 2) :
    ∃ j < k, w = 2^j := by
  induction k generalizing w with
  | zero => simp [digits] at hd
  | succ k ih =>
    rw [digits_succ] at hd
    have hdiv : w/2 < 2^k := Nat.div_lt_of_lt_mul (by simpa only [pow_succ'] using hw)
    have he := Nat.mod_add_div w 2
    have hm := Nat.mod_lt w (by decide : 0 < 2)
    by_cases hzero : w%2 = 0
    · simp only [hzero,zero_add,one_mul] at hd
      obtain ⟨j,hj,hjv⟩ := ih (w/2) hdiv hd
      refine ⟨j+1,by omega,?_⟩
      rw [pow_succ]
      omega
    · have hmod : w%2 = 1 := by omega
      have hd1 : digits k (w/2) = 1 := by rw [hmod] at hd; omega
      have hz := digits_one k (w/2) hdiv hd1
      exact ⟨0,by omega,by simpa using (show w = 1 by omega)⟩

private theorem digits_append (k l a b : ℕ) (ha : a < 2^k) :
    digits (k+l) (a+2^k*b) = digits k a*digits l b := by
  induction k generalizing a with
  | zero =>
    have : a = 0 := by simpa using ha
    simp only [this,Nat.zero_add,pow_zero,one_mul]
    change digits l b = 1*digits l b
    rw [one_mul]
  | succ k ih =>
    have hdiv : a/2 < 2^k := Nat.div_lt_of_lt_mul (by simpa only [pow_succ'] using ha)
    rw [show k+1+l = (k+l)+1 by omega,digits_succ,pow_succ',mul_assoc,
      Nat.add_mul_mod_self_left,Nat.add_mul_div_left _ _ (by decide : 0 < 2),
      ih (a/2) hdiv,digits_succ]
    exact (mul_assoc _ _ _).symm

private theorem digits_repeat (k t a : ℕ) (ha : a < 2^k) :
    digits (k*t) (a*∑ i ∈ Finset.range t,(2^k)^i) = (digits k a)^t := by
  induction t with
  | zero => simp [digits]
  | succ t ih =>
    rw [geom_sum_succ]
    rw [show a*(2^k*(∑ i ∈ Finset.range t,(2^k)^i)+1) =
      a+2^k*(a*∑ i ∈ Finset.range t,(2^k)^i) by ring]
    rw [show k*(t+1) = k+k*t by ring,digits_append k (k*t) a _ ha,ih,pow_succ']

/-- A binary period of length n and degree eight force one repeated bit.
This includes n=1: the weight is seven. -/
theorem repeated_weight {n w : ℕ} (hn : 0 < n) (hw : w < 2^(3*n))
    (hperiod : 2^(3*n)-1 ∣ w*(2^n-1))
    (hd : (∏ i : Fin (3*n),(w/2^i.val%2+1)) = 8) :
    ∃ j < n, w = 2^j+2^(j+n)+2^(j+2*n) := by
  let R := ∑ i ∈ Finset.range 3,(2^n)^i
  have hP : 1 < 2^n := one_lt_pow₀ (by decide) hn.ne'
  have hR : 0 < R := by simp [R,Finset.sum_range_succ]
  have hgeom : R*(2^n-1) = 2^(3*n)-1 := by
    simpa only [R,←pow_mul,mul_comm n 3] using geom_sum_mul_of_one_le hP.le 3
  have hdvd : R ∣ w := by
    apply Nat.dvd_of_mul_dvd_mul_right (by omega : 0 < 2^n-1)
    rwa [hgeom]
  obtain ⟨a,ha⟩ := hdvd
  have halt : a < 2^n := by
    have hle : R*a ≤ R*(2^n-1) := by rw [←ha,hgeom]; omega
    have := Nat.le_of_mul_le_mul_left hle hR
    omega
  have hpow : (digits n a)^3 = 8 := by
    rw [←digits_repeat n 3 a halt]
    change digits (n*3) (a*R) = 8
    rw [mul_comm n 3,mul_comm a R,←ha]
    exact hd
  have htwo : digits n a = 2 := by
    have he : (digits n a)^3 = 2^3 := hpow
    exact Nat.pow_left_injective (by decide : 3 ≠ 0) he
  obtain ⟨j,hj,hja⟩ := digits_two n a halt htwo
  refine ⟨j,hj,?_⟩
  rw [ha,hja]
  simp only [R,Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,pow_one]
  rw [pow_add,pow_add,show 2*n = n*2 by omega,pow_mul]
  ring

private theorem four_mul_le_two_power {t : ℕ} (ht : 4 ≤ t) : 4*t ≤ 2^t := by
  induction t, ht using Nat.le_induction with
  | base => norm_num
  | succ t ht ih => rw [pow_succ]; nlinarith

/-- The prime-field dimension 8n of SL₂(2^(3n)) forces Schur degree n. -/
theorem schur_degree {F V : Type*} [Field F] [Finite F] [CharP F 2]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL(2,F) V) [ρ.IsIrreducible]
    (hnt : ∃ g,ρ g ≠ 1) {n : ℕ} (hn : 0 < n)
    (hF : Nat.card F = 2^(3*n)) (hV : Module.finrank (ZMod 2) V = 8*n) :
    Module.finrank (ZMod 2) (Module.End (ZMod 2)[SL(2,F)] ρ.asModule) = n := by
  obtain ⟨hs,w,hw,hsdiv,hper,hdim⟩ :=
    Representation.SL2.Unsigned.exists_primeField_highestWeight_parameters 2 ρ hnt (3*n) hF
  let s := Module.finrank (ZMod 2) (Module.End (ZMod 2)[SL(2,F)] ρ.asModule)
  change 0 < s at hs
  change s ∣ 3*n at hsdiv
  obtain ⟨t,ht⟩ := hsdiv
  have htpos : 0 < t := by nlinarith
  have hwlt : w.val < 2^(s*t) := by rw [←ht,←hF]; exact w.isLt
  have hwper : 2^(s*t)-1 ∣ w.val*(2^s-1) := by simpa only [←ht,hF] using hper
  obtain ⟨b,hb,hprod,_⟩ := Nat.exists_digit_product_pow_of_period 2 s t w.val
    (by decide) hs htpos hw hwlt hwper
  rw [ht,hprod,hV] at hdim
  have he : 3*b^t = 8*t := by nlinarith
  have htlt : t < 4 := by
    by_contra! hh
    have hbound := (four_mul_le_two_power hh).trans (Nat.pow_le_pow_left hb t)
    nlinarith
  have ht3 : t = 3 := by omega
  change s = n
  rw [ht3] at ht
  omega

open Representation Representation.SL2

/-- The literal Schur-field extension of an eight-dimensional cubic source
module has exactly three equally spaced Frobenius factors. The comparison
is an actual representation equivalence, not merely a dimension count. -/
theorem highest_weight {F V : Type*} [Field F] [Finite F] [CharP F 2]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL(2,F) V) [ρ.IsIrreducible]
    (hnt : ∃ g,ρ g ≠ 1) {n : ℕ} (hn : 0 < n)
    (hF : Nat.card F = 2^(3*n)) (hV : Module.finrank (ZMod 2) V = 8*n) :
    ∃ e : F →+* AlgebraicClosure (Module.End (ZMod 2)[SL(2,F)] ρ.asModule),
      ∃ j < n, Nonempty ((extendScalars
        (AlgebraicClosure (Module.End (ZMod 2)[SL(2,F)] ρ.asModule)) ρ.endFieldRep).Equiv
          (highestWeightSpan e (2^j+2^(j+n)+2^(j+2*n))).toRepresentation) := by
  let E := Module.End (ZMod 2)[SL(2,F)] ρ.asModule
  let C := AlgebraicClosure E
  let : CharP E 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) E).injective 2
  let : CharP C 2 := charP_of_injective_algebraMap (algebraMap E C).injective 2
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let : Algebra (ZMod 2) C := ZMod.algebra C 2
  let : Finite ρ.asModule := Module.finite_iff_finite.mp
    (inferInstance : Module.Finite (ZMod 2) ρ.asModule)
  let : Module.Finite E ρ.asModule := Module.Finite.of_finite
  let : IsAbsolutelyIrreducible ρ.endFieldRep := endFieldRep_isAbsolutelyIrreducible ρ
  let : IsIrreducible (extendScalars C ρ.endFieldRep) :=
    IsAbsolutelyIrreducible.irreducible_of_extension ρ.endFieldRep C
  let e : F →+* C := (IsAlgClosed.lift (R := ZMod 2) (S := F) (M := C)).toRingHom
  obtain ⟨w,⟨φ⟩⟩ := exists_highestWeightSpan_equiv e 2 (extendScalars C ρ.endFieldRep)
  have hs : Module.finrank (ZMod 2) E = n := schur_degree ρ hnt hn hF hV
  let τ : SL(2,F) → E := fun g => LinearMap.trace E ρ.asModule (ρ.endFieldRep g)
  have hspan : Submodule.span (ZMod 2) (Set.range τ) = ⊤ := span_range_endFieldRep_trace ρ
  have hchar (g : SL(2,F)) : (highestWeightSpan e w.val).toRepresentation.character g =
      algebraMap E C (τ g) := by
    rw [←congrFun (Representation.char_iso φ) g]
    exact LinearMap.trace_baseChange (ρ.endFieldRep g) C
  have hperiod := (highestWeightSpan_traceField_period 2 e w.val (3*n) w.isLt hF τ hspan hchar).2
  simp only [hs,hF] at hperiod
  have hd : Module.finrank E ρ.asModule = Module.finrank C (highestWeightSpan e w.val).toSubmodule := by
    rw [←Module.finrank_baseChange (R := C)]
    exact φ.toLinearEquiv.finrank_eq
  have hdim : Module.finrank C (highestWeightSpan e w.val).toSubmodule = 8 := by
    have ht := Module.finrank_mul_finrank (ZMod 2) E ρ.asModule
    rw [hs,ρ.asModuleEquiv.finrank_eq,hV,hd] at ht
    nlinarith
  rw [highestWeightSpan_finrank_eq_prod_digits e 2 Nat.prime_two w.val (3*n) hF
    (by simpa only [←hF] using w.isLt)] at hdim
  obtain ⟨j,hj,hweight⟩ := repeated_weight hn (by simpa only [←hF] using w.isLt) hperiod hdim
  exact ⟨e,j,hj,hweight ▸ ⟨φ⟩⟩

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource.TensorWeights
