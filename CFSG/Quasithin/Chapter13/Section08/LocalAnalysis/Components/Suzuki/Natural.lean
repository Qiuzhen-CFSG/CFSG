module

public import BenderSuzuki.MatrixGroups.Suzuki
public import Theory.Representation.GeneralLinearNatural
public import Theory.Representation.FirstCohomologyLinearTransport
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Commuting endomorphisms of the natural Suzuki modules

These are the actual column-vector representations of SuzukiMatrixGroup m
and its two-factor direct product, restricted to binary scalars. A commuting
endomorphism preserves the first coordinate line, since it is the fixed
space of the root element (1,0). The Weyl element and the root element (0,1)
force the same additive map on all four coordinate lines. The root elements
(a,0) force that additive map to be multiplication by a field scalar.

In the two-factor case, off-diagonal maps vanish because the natural module
has no fixed vectors. Thus each factor has its own scalar. Since the field
has order 2^(2m+1), its multiplicative group has order prime to three, so a
commuting operator whose cube is one is the identity in both cases.

Source: the natural-module calculation used in Aschbacher–Smith 13.8.16,
printed pp.952–953 (combined manuscript of 1 March 2004). The matrices are
the existing Suzuki root and Weyl matrices. Source applications require
m ≥ 1, although these calculations also hold for m = 0.
-/

@[expose] public section

open BenderSuzuki BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
open Representation
namespace CFSG.Quasithin.Chapter13.Section08.Components.Suzuki

/-- The natural four-dimensional field module, with scalars restricted to F₂. -/
noncomputable abbrev natural (m : ℕ) :
    Representation (ZMod 2) (SuzukiMatrixGroup m)
      (Fin 4 → BinaryGaloisField (2 * m + 1)) :=
  restrictScalars ((generalLinearNatural 4).comp (SuzukiMatrixSubgroup m).subtype)

/-- The natural action is the literal matrix action on column vectors. -/
theorem natural_apply (m : ℕ) (g : SuzukiMatrixGroup m)
    (v : Fin 4 → BinaryGaloisField (2 * m + 1)) :
    natural m g v = (g.val : Matrix (Fin 4) (Fin 4) _).mulVec v := rfl

/-- The odd field exponent makes its unit group prime to three. -/
theorem field_units_card_coprime_three (m : ℕ) :
    Nat.Coprime 3 (Nat.card (BinaryGaloisField (2 * m + 1))ˣ) := by
  rw [Nat.card_units, GaloisField.card 2 (2 * m + 1) (by omega)]
  apply Nat.prime_three.coprime_iff_not_dvd.mpr
  intro h
  have he : 2 ^ (2 * m + 1) % 3 = 2 := by
    rw [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hp : 1 ≤ 2 ^ (2 * m + 1) := by
    have : 0 < 2 ^ (2 * m + 1) := by positivity
    omega
  have hz := (Nat.modEq_iff_dvd' hp).mpr h
  change 1 % 3 = 2 ^ (2 * m + 1) % 3 at hz
  omega

/-- There is no nonidentity cube root of one in the multiplicative field group. -/
theorem field_unit_eq_one_of_cube (m : ℕ)
    (a : (BinaryGaloisField (2 * m + 1))ˣ) (ha : a ^ 3 = 1) : a = 1 := by
  apply orderOf_eq_one_iff.mp
  exact Nat.eq_one_of_dvd_coprimes (field_units_card_coprime_three m)
    (orderOf_dvd_of_pow_eq_one ha) (orderOf_dvd_natCard a)

/-- A scalar whose cube is one is one. -/
theorem field_scalar_eq_one_of_cube (m : ℕ)
    (a : BinaryGaloisField (2 * m + 1)) (ha : a ^ 3 = 1) : a = 1 := by
  have hne : a ≠ 0 := by intro hz; simp [hz] at ha
  let u := Units.mk0 a hne
  have hu : u ^ 3 = 1 := Units.ext ha
  exact congrArg Units.val (field_unit_eq_one_of_cube m u hu)


/-- The binary natural action retains linearity over the full coefficient field. -/
theorem natural_smul (m : ℕ) (g : SuzukiMatrixGroup m)
    (a : BinaryGaloisField (2 * m + 1)) (v : Fin 4 → BinaryGaloisField (2 * m + 1)) :
    natural m g (a • v) = a • natural m g v := by
  exact (generalLinearNatural 4 g.val).map_smul a v

/-- A scalar binary endomorphism whose cube is one is the identity. -/
theorem scalar_endomorphism_eq_one_of_cube (m : ℕ)
    (f : Module.End (ZMod 2) (Fin 4 → BinaryGaloisField (2 * m + 1)))
    (a : BinaryGaloisField (2 * m + 1))
    (hf : ∀ v, f v = a • v) (hcube : f ^ 3 = 1) : f = 1 := by
  have hc := congrArg (fun t : Module.End (ZMod 2)
    (Fin 4 → BinaryGaloisField (2 * m + 1)) => t (fun _ => 1) 0) hcube
  have hpow : a ^ 3 = 1 := by
    simpa [pow_succ, Module.End.mul_apply, hf, Pi.smul_apply, smul_eq_mul,
      mul_assoc] using hc
  have ha := field_scalar_eq_one_of_cube m a hpow
  ext v i
  simp [hf, ha]


/-- Commutation with the concrete root and Weyl elements forces a binary
endomorphism of the natural module to be multiplication by a field scalar. -/
theorem commuting_endomorphism_scalar (m : ℕ)
    (f : Module.End (ZMod 2) (Fin 4 → BinaryGaloisField (2 * m + 1)))
    (hf : ∀ g : SuzukiMatrixGroup m, ∀ v, f (natural m g v) = natural m g (f v)) :
    ∃ a : BinaryGaloisField (2 * m + 1), ∀ v, f v = a • v := by
  classical
  let α := fun x : BinaryGaloisField (2 * m + 1) => f (Pi.single 0 x) 0
  have hroot (a b : BinaryGaloisField (2 * m + 1)) (v) :
      f ((SuzukiRootMatrix m a b).mulVec v) = (SuzukiRootMatrix m a b).mulVec (f v) := by
    let g : SuzukiMatrixGroup m := ⟨SuzukiRootGL m a b,
      Subgroup.subset_closure (Or.inl ⟨a, b, rfl⟩)⟩
    exact hf g v
  have hweyl (v) :
      f ((SuzukiWeylMatrix m).mulVec v) = (SuzukiWeylMatrix m).mulVec (f v) := by
    let g : SuzukiMatrixGroup m := ⟨SuzukiWeylGL m,
      Subgroup.subset_closure (Or.inr (Or.inr rfl))⟩
    exact hf g v
  have hfirst (x : BinaryGaloisField (2 * m + 1)) :
      (SuzukiRootMatrix m 1 0).mulVec (Pi.single 0 x) = Pi.single 0 x := by
    ext i
    fin_cases i <;> simp [SuzukiRootMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  have h0 (x) : f (Pi.single 0 x) = Pi.single 0 (α x) := by
    have he := (hroot 1 0 (Pi.single 0 x)).symm
    rw [hfirst] at he
    have hc3 : f (Pi.single 0 x) 3 = 0 := by
      simpa [SuzukiRootMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four] using congrFun he 2
    have hc2 : f (Pi.single 0 x) 2 = 0 := by
      simpa [SuzukiRootMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four, hc3] using congrFun he 1
    have hc1 : f (Pi.single 0 x) 1 = 0 := by
      simpa [SuzukiRootMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four, hc3, hc2] using congrFun he 0
    ext i
    fin_cases i <;> simp [α, hc1, hc2, hc3]
  have hw0 (x : BinaryGaloisField (2 * m + 1)) :
      (SuzukiWeylMatrix m).mulVec (Pi.single 0 x) = Pi.single 3 x := by
    ext i
    fin_cases i <;> simp [SuzukiWeylMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  have h3 (x) : f (Pi.single 3 x) = Pi.single 3 (α x) := by
    rw [← hw0, hweyl, h0, hw0]
  have hr3 (x : BinaryGaloisField (2 * m + 1)) :
      (SuzukiRootMatrix m 0 1).mulVec (Pi.single 3 x) =
        Pi.single 0 x + Pi.single 1 x + Pi.single 3 x := by
    ext i
    fin_cases i <;> simp [SuzukiRootMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  have h1 (x) : f (Pi.single 1 x) = Pi.single 1 (α x) := by
    have he := hroot 0 1 (Pi.single 3 x)
    rw [hr3, map_add, map_add, h0, h3, hr3] at he
    exact add_left_cancel (add_right_cancel he)
  have hw1 (x : BinaryGaloisField (2 * m + 1)) :
      (SuzukiWeylMatrix m).mulVec (Pi.single 1 x) = Pi.single 2 x := by
    ext i
    fin_cases i <;> simp [SuzukiWeylMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  have h2 (x) : f (Pi.single 2 x) = Pi.single 2 (α x) := by
    rw [← hw1, hweyl, h1, hw1]
  have hcoord (v : Fin 4 → BinaryGaloisField (2 * m + 1)) (i) : f v i = α (v i) := by
    have hv : v = Pi.single 0 (v 0) + Pi.single 1 (v 1) +
        Pi.single 2 (v 2) + Pi.single 3 (v 3) := by
      ext j
      fin_cases j <;> simp
    have he : f v = Pi.single 0 (α (v 0)) + Pi.single 1 (α (v 1)) +
        Pi.single 2 (α (v 2)) + Pi.single 3 (α (v 3)) := by
      calc
        f v = f (Pi.single 0 (v 0) + Pi.single 1 (v 1) +
          Pi.single 2 (v 2) + Pi.single 3 (v 3)) := congrArg f hv
        _ = _ := by rw [map_add, map_add, map_add, h0, h1, h2, h3]
    rw [he]
    fin_cases i <;> simp
  have hr1 (a x : BinaryGaloisField (2 * m + 1)) :
      (SuzukiRootMatrix m a 0).mulVec (Pi.single 1 x) =
        Pi.single 0 (a * x) + Pi.single 1 x := by
    ext i
    fin_cases i <;> simp [SuzukiRootMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  have hα (a : BinaryGaloisField (2 * m + 1)) : α a = a * α 1 := by
    have he := hroot a 0 (Pi.single 1 1)
    rw [hr1, map_add, h0, h1, hr1] at he
    simpa using congrFun he 0
  refine ⟨α 1, fun v => ?_⟩
  ext i
  rw [hcoord, hα]
  exact mul_comm _ _

/-- A commuting order-three action on the actual natural module is trivial. -/
theorem commuting_endomorphism_eq_one_of_cube (m : ℕ)
    (f : Module.End (ZMod 2) (Fin 4 → BinaryGaloisField (2 * m + 1)))
    (hf : ∀ g : SuzukiMatrixGroup m, ∀ v, f (natural m g v) = natural m g (f v))
    (hcube : f ^ 3 = 1) : f = 1 := by
  obtain ⟨a, ha⟩ := commuting_endomorphism_scalar m f hf
  exact scalar_endomorphism_eq_one_of_cube m f a ha hcube


/-- The natural module has no nonzero Suzuki-fixed vector. -/
theorem natural_fixed_eq_zero (m : ℕ)
    (v : Fin 4 → BinaryGaloisField (2 * m + 1))
    (hv : ∀ g : SuzukiMatrixGroup m, natural m g v = v) : v = 0 := by
  let u : SuzukiMatrixGroup m := ⟨SuzukiRootGL m 1 0,
    Subgroup.subset_closure (Or.inl ⟨1, 0, rfl⟩)⟩
  have he : (SuzukiRootMatrix m 1 0).mulVec v = v := hv u
  have h3 : v 3 = 0 := by
    simpa [SuzukiRootMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four] using congrFun he 2
  have h2 : v 2 = 0 := by
    simpa [SuzukiRootMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four, h3] using congrFun he 1
  have h1 : v 1 = 0 := by
    simpa [SuzukiRootMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four, h3, h2] using congrFun he 0
  let w : SuzukiMatrixGroup m := ⟨SuzukiWeylGL m,
    Subgroup.subset_closure (Or.inr (Or.inr rfl))⟩
  have hw : (SuzukiWeylMatrix m).mulVec v = v := hv w
  have h0 : v 0 = 0 := by
    simpa [SuzukiWeylMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four, h3] using congrFun hw 3
  ext i
  fin_cases i <;> assumption

/-- The two natural modules for the two independent Suzuki factors. -/
noncomputable abbrev naturalPair (m : ℕ) :=
  Representation.prod
    ((natural m).comp (MonoidHom.fst (SuzukiMatrixGroup m) (SuzukiMatrixGroup m)))
    ((natural m).comp (MonoidHom.snd (SuzukiMatrixGroup m) (SuzukiMatrixGroup m)))

/-- Every endomorphism commuting with the two factors is scalar on each summand; off-diagonal maps vanish. -/
theorem commuting_pair_endomorphism_scalar (m : ℕ)
    (f : Module.End (ZMod 2) ((Fin 4 → BinaryGaloisField (2 * m + 1)) ×
      (Fin 4 → BinaryGaloisField (2 * m + 1))))
    (hf : ∀ g, ∀ v, f (naturalPair m g v) = naturalPair m g (f v)) :
    ∃ a b : BinaryGaloisField (2 * m + 1), ∀ v, f v = (a • v.1, b • v.2) := by
  let V := Fin 4 → BinaryGaloisField (2 * m + 1)
  have haction (g h : SuzukiMatrixGroup m) (x y : V) :
      f (natural m g x, natural m h y) =
        (natural m g (f (x, y)).1, natural m h (f (x, y)).2) := hf (g, h) (x, y)
  have hcross₁ (y : V) : (f (0, y)).1 = 0 := by
    apply natural_fixed_eq_zero m
    intro g
    have he := congrArg Prod.fst (haction g 1 0 y)
    simpa only [map_one, map_zero, Module.End.one_apply] using he.symm
  have hcross₂ (x : V) : (f (x, 0)).2 = 0 := by
    apply natural_fixed_eq_zero m
    intro g
    have he := congrArg Prod.snd (haction 1 g x 0)
    simpa only [map_one, map_zero, Module.End.one_apply] using he.symm
  let f₁ : Module.End (ZMod 2) V :=
    (LinearMap.fst (ZMod 2) V V).comp (f.comp (LinearMap.inl (ZMod 2) V V))
  let f₂ : Module.End (ZMod 2) V :=
    (LinearMap.snd (ZMod 2) V V).comp (f.comp (LinearMap.inr (ZMod 2) V V))
  have hf₁ : ∀ g v, f₁ (natural m g v) = natural m g (f₁ v) := by
    intro g v
    have he := congrArg Prod.fst (haction g 1 v 0)
    simpa [f₁, V] using he
  have hf₂ : ∀ g v, f₂ (natural m g v) = natural m g (f₂ v) := by
    intro g v
    have he := congrArg Prod.snd (haction 1 g 0 v)
    simpa [f₂, V] using he
  obtain ⟨a, ha⟩ := commuting_endomorphism_scalar m f₁ hf₁
  obtain ⟨b, hb⟩ := commuting_endomorphism_scalar m f₂ hf₂
  refine ⟨a, b, ?_⟩
  rintro ⟨x, y⟩
  rw [show (x, y) = (x, 0) + (0, y) by simp, map_add]
  apply Prod.ext
  · change (f (x, 0)).1 + (f (0, y)).1 = _
    rw [hcross₁, add_zero]
    simpa [f₁, V] using ha x
  · change (f (x, 0)).2 + (f (0, y)).2 = _
    rw [hcross₂, zero_add]
    simpa [f₂, V] using hb y

/-- A commuting order-three action on the two-factor natural module is trivial. -/
theorem commuting_pair_endomorphism_eq_one_of_cube (m : ℕ)
    (f : Module.End (ZMod 2) ((Fin 4 → BinaryGaloisField (2 * m + 1)) ×
      (Fin 4 → BinaryGaloisField (2 * m + 1))))
    (hf : ∀ g, ∀ v, f (naturalPair m g v) = naturalPair m g (f v))
    (hcube : f ^ 3 = 1) : f = 1 := by
  obtain ⟨a, b, hab⟩ := commuting_pair_endomorphism_scalar m f hf
  have ha := congrArg (fun t : Module.End (ZMod 2)
    ((Fin 4 → BinaryGaloisField (2 * m + 1)) × (Fin 4 → BinaryGaloisField (2 * m + 1))) =>
      (t ((fun _ => 1), 0)).1 0) hcube
  have hb := congrArg (fun t : Module.End (ZMod 2)
    ((Fin 4 → BinaryGaloisField (2 * m + 1)) × (Fin 4 → BinaryGaloisField (2 * m + 1))) =>
      (t (0, (fun _ => 1))).2 0) hcube
  have ha3 : a ^ 3 = 1 := by
    simpa [pow_succ, Module.End.mul_apply, hab, Pi.smul_apply, smul_eq_mul, mul_assoc] using ha
  have hb3 : b ^ 3 = 1 := by
    simpa [pow_succ, Module.End.mul_apply, hab, Pi.smul_apply, smul_eq_mul, mul_assoc] using hb
  have ha1 := field_scalar_eq_one_of_cube m a ha3
  have hb1 := field_scalar_eq_one_of_cube m b hb3
  apply LinearMap.ext
  intro v
  change f v = v
  simp [hab, ha1, hb1]

end CFSG.Quasithin.Chapter13.Section08.Components.Suzuki
