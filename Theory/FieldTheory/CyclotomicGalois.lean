module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.FieldTheory.IsAlgClosed.Classification
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.Data.ZMod.Units
public import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
public import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Cyclotomic automorphisms and rational descent

A unit exponent modulo `n` acts on all complex `n`-th roots of unity through
an automorphism of `ℂ/ℚ`. Extend the cyclotomic automorphism across a
transcendence basis and then an algebraic closure. The finite cyclotomic
fixed-field theorem detects rational values, and CRT chooses exponents with
specified actions on coprime factors.

Extracted from Peterfalvi (1.9), for Suzuki VI §2.2, Example 3.
The historical `Section1` names are retained for compatibility.
-/

noncomputable section
open IsCyclotomicExtension
open scoped Cyclotomic
namespace Section1

private theorem complex_galois_aut_pow_on_roots_aux
    {n e : ℕ} (hn : n ≠ 0) (he : e.Coprime n) :
    ∃ τ : Gal(ℂ/ℚ), ∀ z : ℂ, z ^ n = 1 → τ z = z ^ e := by
  classical
  let : NeZero n := ⟨hn⟩
  have : NeZero (n : ℚ) := ⟨by exact_mod_cast hn⟩
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)
  have hζ : IsPrimitiveRoot ζ n := by
    dsimp [ζ]
    exact Complex.isPrimitiveRoot_exp n hn
  have hζalg : IsAlgebraic ℚ ζ := by
    refine ⟨Polynomial.cyclotomic n ℚ, Polynomial.cyclotomic_ne_zero n ℚ, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
      Polynomial.map_cyclotomic, ← Polynomial.IsRoot.def,
      Polynomial.isRoot_cyclotomic_iff]
    exact hζ
  let F : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ ({ζ} : Set ℂ)
  have hFcyc : IsCyclotomicExtension {n} ℚ F := by
    change IsCyclotomicExtension {n} ℚ F.toSubalgebra
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hζalg]
    exact hζ.adjoin_isCyclotomicExtension ℚ
  have : IsCyclotomicExtension {n} ℚ F := hFcyc
  have : IsCyclotomicExtension {n} ℚ F.toSubalgebra := by
    change IsCyclotomicExtension {n} ℚ F
    exact hFcyc
  have : NumberField F := IsCyclotomicExtension.numberField {n} ℚ F
  let u : (ZMod n)ˣ := ZMod.unitOfCoprime e he
  let σF : Gal(F/ℚ) := (IsCyclotomicExtension.Rat.galEquivZMod n F).symm u
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis F ℂ
  let x : s → ℂ := fun a => (a : ℂ)
  have hsx : IsTranscendenceBasis F x := by
    simpa [x] using hs
  let B := Algebra.adjoin F (Set.range x)
  let ae : MvPolynomial s F ≃ₐ[F] B := hsx.1.aevalEquiv
  have hrepr_const (y : F) : ae.symm (algebraMap F B y) = MvPolynomial.C y := by
    apply ae.injective
    rw [AlgEquiv.apply_symm_apply]
    exact (ae.commutes y).symm
  have hmap_const (y : F) :
      (MvPolynomial.mapAlgEquiv (σ := s) (R := ℚ) σF) (MvPolynomial.C y) =
        MvPolynomial.C (σF y) := by
    rw [MvPolynomial.mapAlgEquiv_apply, MvPolynomial.map_C]
    rfl
  let baseAut : B ≃+* B :=
    (ae.symm.toRingEquiv.trans
      (MvPolynomial.mapAlgEquiv (σ := s) (R := ℚ) σF).toRingEquiv).trans
        ae.toRingEquiv
  have hbase_const (y : F) :
      baseAut (algebraMap F B y) = algebraMap F B (σF y) := by
    dsimp [baseAut]
    change ae ((MvPolynomial.mapAlgEquiv (σ := s) (R := ℚ) σF)
      (ae.symm (algebraMap F B y))) = algebraMap F B (σF y)
    rw [hrepr_const y]
    rw [hmap_const y]
    exact ae.commutes (σF y)
  have hbase_Q (q : ℚ) :
      baseAut (algebraMap ℚ B q) = algebraMap ℚ B q := by
    have hq : algebraMap ℚ B q = algebraMap F B (algebraMap ℚ F q) := by
      exact (IsScalarTower.algebraMap_apply ℚ F B q).symm
    rw [hq, hbase_const]
    simp
  let baseAlgAut : B ≃ₐ[ℚ] B := AlgEquiv.ofRingEquiv hbase_Q
  have hbaseAlg_const (y : F) :
      baseAlgAut (algebraMap F B y) = algebraMap F B (σF y) := by
    exact hbase_const y
  have hclosure : IsAlgClosure B ℂ := by
    dsimp [B]
    exact IsAlgClosed.isAlgClosure_of_transcendence_basis x hsx
  let τR : ℂ ≃+* ℂ := by
    let : IsAlgClosure B ℂ := hclosure
    exact IsAlgClosure.equivOfEquiv ℂ ℂ baseAlgAut.toRingEquiv
  have hτR_Q (q : ℚ) : τR (algebraMap ℚ ℂ q) = algebraMap ℚ ℂ q := by
    let : IsAlgClosure B ℂ := hclosure
    have hB := IsAlgClosure.equivOfEquiv_algebraMap (L := ℂ) (M := ℂ)
      baseAlgAut.toRingEquiv (algebraMap ℚ B q)
    simp [τR, baseAlgAut] at hB ⊢
  let τ : Gal(ℂ/ℚ) := AlgEquiv.ofRingEquiv hτR_Q
  have hτ_on_F (y : F) : τ (y : ℂ) = (σF y : ℂ) := by
    let : IsAlgClosure B ℂ := hclosure
    have hB := IsAlgClosure.equivOfEquiv_algebraMap (L := ℂ) (M := ℂ)
      baseAlgAut.toRingEquiv (algebraMap F B y)
    change (IsAlgClosure.equivOfEquiv ℂ ℂ baseAlgAut.toRingEquiv)
        (algebraMap B ℂ (algebraMap F B y)) =
      algebraMap B ℂ (baseAlgAut (algebraMap F B y)) at hB
    rw [hbaseAlg_const y] at hB
    simpa [τ, τR, baseAlgAut] using hB
  refine ⟨τ, ?_⟩
  intro z hz
  have hzFmem : z ∈ F := by
    exact IsCyclotomicExtension.mem_of_pow_eq_one F.toSubalgebra
      (S := ({n} : Set ℕ)) (by simp) hn hz
  let zF : F := ⟨z, hzFmem⟩
  have hzFpow : zF ^ n = 1 := by
    ext
    exact hz
  have hσu : IsCyclotomicExtension.Rat.galEquivZMod n F σF = u := by
    exact MulEquiv.apply_symm_apply (IsCyclotomicExtension.Rat.galEquivZMod n F) u
  have hmodeq : ((u : ZMod n).val : ℕ) ≡ e [MOD n] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    calc
      (((u : ZMod n).val : ℕ) : ZMod n) = (u : ZMod n) := ZMod.natCast_zmod_val _
      _ = e := ZMod.coe_unitOfCoprime e he
  have hpow_eq :
      zF ^ (IsCyclotomicExtension.Rat.galEquivZMod n F σF).val.val = zF ^ e := by
    rw [hσu]
    exact pow_eq_pow_of_modEq hmodeq hzFpow
  have hσFz : σF zF = zF ^ e := by
    rw [IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq n F σF hzFpow]
    exact hpow_eq
  calc
    τ z = τ (zF : ℂ) := rfl
    _ = (σF zF : ℂ) := hτ_on_F zF
    _ = ((zF ^ e : F) : ℂ) := by rw [hσFz]
    _ = z ^ e := by rfl

public theorem complex_galois_aut_pow_on_roots
    {n e : ℕ} (he : e.Coprime n) :
    ∃ τ : Gal(ℂ/ℚ), ∀ z : ℂ, z ^ n = 1 → τ z = z ^ e := by
  by_cases hn : n = 0
  · have he1 : e = 1 := by
      simpa [hn, Nat.coprime_zero_right] using he
    refine ⟨1, ?_⟩
    intro z _hz
    simp [he1]
  · exact complex_galois_aut_pow_on_roots_aux hn he

public abbrev CyclotomicABField (a b : ℕ) :=
  CyclotomicField (a * b) ℚ

public instance cyclotomicABField_isCyclotomicExtension (a b : ℕ) [NeZero (a * b)] :
    IsCyclotomicExtension {a * b} ℚ (CyclotomicABField a b) := by
  have : NeZero ((a * b : ℕ) : ℚ) := ⟨by exact_mod_cast (NeZero.ne (a * b))⟩
  exact CyclotomicField.isCyclotomicExtension (a * b) ℚ

/--
An element of the concrete cyclotomic field `ℚ_{ab}` fixed by all
`ℚ`-automorphisms is rational.  This is the finite Galois fixed-field descent
used in the rationality route for PF `(3.9)(c)`.
-/
public theorem cyclotomicABField_mem_rat_of_fixed_gal {a b : ℕ} [NeZero (a * b)]
    (x : CyclotomicABField a b)
    (hfixed : ∀ v : Gal((CyclotomicABField a b)/ℚ), v x = x) :
    ∃ q : ℚ, algebraMap ℚ (CyclotomicABField a b) q = x := by
  have : IsCyclotomicExtension {a * b} ℚ (CyclotomicABField a b) :=
    cyclotomicABField_isCyclotomicExtension a b
  have : IsGalois ℚ (CyclotomicABField a b) :=
    IsCyclotomicExtension.isGalois {a * b} ℚ (CyclotomicABField a b)
  have : FiniteDimensional ℚ (CyclotomicABField a b) :=
    IsCyclotomicExtension.finiteDimensional {a * b} ℚ (CyclotomicABField a b)
  exact (IsGalois.mem_range_algebraMap_iff_fixed x).2 hfixed

/--
Complex-valued form of the fixed-field descent above.  If a complex value is
the image of an element of `ℚ_{ab}` fixed by all `ℚ`-automorphisms of
`ℚ_{ab}`, then the complex value is rational.
-/
public theorem cyclotomicABField_complex_rat_of_fixed_gal {a b : ℕ} [NeZero (a * b)]
    (ι : CyclotomicABField a b →ₐ[ℚ] ℂ)
    (x : CyclotomicABField a b) (z : ℂ)
    (hz : z = ι x)
    (hfixed : ∀ v : Gal((CyclotomicABField a b)/ℚ), v x = x) :
    ∃ q : ℚ, z = (q : ℂ) := by
  rcases cyclotomicABField_mem_rat_of_fixed_gal x hfixed with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  rw [hz, ← hq]
  simp

@[expose] public noncomputable def cyclotomicABRoot (a b : ℕ) (hn : a * b ≠ 0) :
    CyclotomicABField a b := by
  let : NeZero (a * b) := ⟨hn⟩
  exact IsCyclotomicExtension.zeta (a * b) ℚ (CyclotomicABField a b)

public theorem zmod_units_crt_exists_of_coprime {a b : ℕ} (hab : a.Coprime b)
    (ua : (ZMod a)ˣ) :
    ∃ w : (ZMod (a * b))ˣ,
      ZMod.unitsMap (Nat.dvd_mul_right a b) w = ua ∧
      ZMod.unitsMap (Nat.dvd_mul_left b a) w = 1 := by
  classical
  let e : (ZMod (a * b))ˣ ≃* (ZMod a)ˣ × (ZMod b)ˣ :=
    (Units.mapEquiv (ZMod.chineseRemainder hab).toMulEquiv).trans MulEquiv.prodUnits
  let w : (ZMod (a * b))ˣ := e.symm (ua, 1)
  refine ⟨w, ?_, ?_⟩
  · have he : e w = (ua, 1) := by simp [w]
    have hfst := congrArg Prod.fst he
    have hmap : ZMod.unitsMap (Nat.dvd_mul_right a b) w =
        (MulEquiv.prodUnits ((Units.mapEquiv (ZMod.chineseRemainder hab).toMulEquiv) w)).1 := by
      ext
      change (w : ZMod (a * b)).cast = ((ZMod.chineseRemainder hab (w : ZMod (a * b))).1)
      rw [ZMod.chineseRemainder]
      simp
    rw [hmap]
    exact hfst
  · have he : e w = (ua, 1) := by simp [w]
    have hsnd := congrArg Prod.snd he
    have hmap : ZMod.unitsMap (Nat.dvd_mul_left b a) w =
        (MulEquiv.prodUnits ((Units.mapEquiv (ZMod.chineseRemainder hab).toMulEquiv) w)).2 := by
      ext
      change (w : ZMod (a * b)).cast = ((ZMod.chineseRemainder hab (w : ZMod (a * b))).2)
      rw [ZMod.chineseRemainder]
      simp
    rw [hmap]
    exact hsnd


public theorem zmod_units_crt_val_modEq_left_int {a b : ℕ}
    (hn : a * b ≠ 0) {k : ℤ} (hk : IsCoprime k (a : ℤ))
    {w : (ZMod (a * b))ˣ}
    (hwa : ZMod.unitsMap (Nat.dvd_mul_right a b) w =
      ZMod.unitOfIsCoprime k hk) :
    (((w : ZMod (a * b)).val : ℤ) ≡ k [ZMOD a]) := by
  have : NeZero (a * b) := ⟨hn⟩
  have hvalCast : (((w : ZMod (a * b)).val : ℕ) : ZMod a) =
      ((w : ZMod (a * b)).cast : ZMod a) := by
    have hval : (((w : ZMod (a * b)).val : ℕ) : ZMod (a * b)) =
        (w : ZMod (a * b)) :=
      ZMod.natCast_zmod_val (w : ZMod (a * b))
    convert congrArg (fun z : ZMod (a * b) => (z.cast : ZMod a)) hval
    simp
  have hcast : (((w : ZMod (a * b)).val : ℤ) : ZMod a) = (k : ZMod a) := by
    calc
      (((w : ZMod (a * b)).val : ℤ) : ZMod a) =
          (((w : ZMod (a * b)).val : ℕ) : ZMod a) := by norm_num
      _ = ((w : ZMod (a * b)).cast : ZMod a) := hvalCast
      _ = ((ZMod.unitsMap (Nat.dvd_mul_right a b) w : ZMod a)) := rfl
      _ = (ZMod.unitOfIsCoprime k hk : ZMod a) := by rw [hwa]
      _ = (k : ZMod a) := rfl
  exact (ZMod.intCast_eq_intCast_iff _ _ _).mp hcast

public theorem zmod_units_crt_val_modEq_right_one {a b : ℕ}
    (hn : a * b ≠ 0) {w : (ZMod (a * b))ˣ}
    (hwb : ZMod.unitsMap (Nat.dvd_mul_left b a) w = 1) :
    (((w : ZMod (a * b)).val : ℤ) ≡ (1 : ℤ) [ZMOD b]) := by
  have : NeZero (a * b) := ⟨hn⟩
  have hvalCast : (((w : ZMod (a * b)).val : ℕ) : ZMod b) =
      ((w : ZMod (a * b)).cast : ZMod b) := by
    have hval : (((w : ZMod (a * b)).val : ℕ) : ZMod (a * b)) =
        (w : ZMod (a * b)) :=
      ZMod.natCast_zmod_val (w : ZMod (a * b))
    convert congrArg (fun z : ZMod (a * b) => (z.cast : ZMod b)) hval
    simp
  have hcast :
      (((w : ZMod (a * b)).val : ℤ) : ZMod b) = ((1 : ℤ) : ZMod b) := by
    calc
      (((w : ZMod (a * b)).val : ℤ) : ZMod b) =
          (((w : ZMod (a * b)).val : ℕ) : ZMod b) := by norm_num
      _ = ((w : ZMod (a * b)).cast : ZMod b) := hvalCast
      _ = ((ZMod.unitsMap (Nat.dvd_mul_left b a) w : ZMod b)) := rfl
      _ = ((1 : (ZMod b)ˣ) : ZMod b) := by rw [hwb]
      _ = ((1 : ℤ) : ZMod b) := by norm_num
  exact (ZMod.intCast_eq_intCast_iff _ _ _).mp hcast

end Section1
