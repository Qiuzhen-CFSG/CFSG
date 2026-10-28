module

public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Bialgebra.TensorProduct
public import Mathlib.RingTheory.Jacobson.Artinian

/-!
# Finite local Hopf algebras in characteristic zero

A finite-dimensional local commutative Hopf algebra over a characteristic-zero
field has no nontrivial infinitesimal direction: it is a field, and its counit
identifies it with the base field. In particular it is reduced and its
nilradical vanishes. This is the finite-local ingredient in the standard proof
of Cartier's reducedness theorem for finite-type commutative Hopf algebras.

The proof studies the cotangent space `m / m ^ 2` at the augmentation. A
nonzero cotangent vector has a dual functional, which extends to an
infinitesimal functional `f` on the Hopf algebra. Pulling convolution powers
of `f` back along multiplication and applying the binomial theorem gives

`(f ^ n) (a ^ n) = n! * f a ^ n`

for augmentation-zero `a`. Finite-dimensionality makes the local ring
Artinian, so a power of its maximal ideal is zero. The displayed identity then
contradicts the nonvanishing of factorials in characteristic zero. The
cotangent-space criterion for local fields finishes the argument. All
convolution and cotangent constructions used in this reduction are private;
the exported interface records fieldness, triviality, reducedness, and
nilradical vanishing.
-/

open Coalgebra Bialgebra WithConv
open scoped TensorProduct

universe u v

namespace Theory.AlgebraicGroup

variable {k : Type u} {A : Type v} [Field k] [CommRing A] [HopfAlgebra k A]

private abbrev ConvDual (k : Type u) (A : Type v) [Field k] [CommRing A]
    [Bialgebra k A] := WithConv (A →ₗ[k] k)

private abbrev ConvTensorDual (k : Type u) (A : Type v) [Field k]
    [CommRing A] [Bialgebra k A] := WithConv ((A ⊗[k] A) →ₗ[k] k)

private def convTensor (f g : ConvDual k A) : ConvTensorDual k A :=
  toConv <| (TensorProduct.lid k k).toLinearMap.comp
    (TensorProduct.map f.ofConv g.ofConv)

@[simp]
private lemma convTensor_tmul (f g : ConvDual k A) (a b : A) :
    convTensor f g (a ⊗ₜ[k] b) = f a * g b := by
  simp [convTensor]

private def convPreMul (f : ConvDual k A) : ConvTensorDual k A :=
  toConv <| f.ofConv.comp (Bialgebra.mulCoalgHom k A).toLinearMap

@[simp]
private lemma convPreMul_tmul (f : ConvDual k A) (a b : A) :
    convPreMul f (a ⊗ₜ[k] b) = f (a * b) := by
  rfl

@[simp]
private lemma convPreMul_one :
    convPreMul (1 : ConvDual k A) = 1 := by
  ext a b
  simp [Bialgebra.counit_mul, mul_comm]

@[simp]
private lemma convPreMul_mul (f g : ConvDual k A) :
    convPreMul (f * g) = convPreMul f * convPreMul g := by
  apply WithConv.ext
  exact LinearMap.convMul_comp_coalgHom_distrib f g
    (Bialgebra.mulCoalgHom k A)

@[simp]
private lemma convPreMul_pow (f : ConvDual k A) (n : ℕ) :
    convPreMul (f ^ n) = convPreMul f ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, ih]

@[simp]
private lemma convTensor_one_one :
    convTensor (1 : ConvDual k A) 1 = 1 := by
  ext a b
  simp [mul_comm]

@[simp]
private lemma convTensor_mul (f g h q : ConvDual k A) :
    convTensor f g * convTensor h q = convTensor (f * h) (g * q) := by
  ext a b
  simp [((ℛ k a).tmul (ℛ k b)).convMul_apply,
    (ℛ k a).convMul_apply, (ℛ k b).convMul_apply,
    Finset.sum_product, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

@[simp]
private lemma convTensor_pow_left (f : ConvDual k A) (n : ℕ) :
    convTensor f 1 ^ n = convTensor (f ^ n) 1 := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, ih]

@[simp]
private lemma convTensor_pow_right (f : ConvDual k A) (n : ℕ) :
    convTensor 1 f ^ n = convTensor 1 (f ^ n) := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, ih]

private lemma convTensor_left_right_commute (f : ConvDual k A) :
    Commute (convTensor f 1) (convTensor 1 f) := by
  change convTensor f 1 * convTensor 1 f = convTensor 1 f * convTensor f 1
  simp

private lemma convPow_mul (f : ConvDual k A)
    (hf : ∀ a b : A,
      f (a * b) = f a * counit b + counit a * f b)
    (n : ℕ) (a b : A) :
    (f ^ n) (a * b) = ∑ i ∈ Finset.range (n + 1),
      (f ^ i) a * (f ^ (n - i)) b * (n.choose i : k) := by
  let x : ConvTensorDual k A := convTensor f 1
  let y : ConvTensorDual k A := convTensor 1 f
  have hprimitive : convPreMul f = x + y := by
    ext c d
    simp [x, y, hf]
  have hmul_natCast (g : ConvTensorDual k A) (m : ℕ) :
      g * (m : ConvTensorDual k A) = m • g := by
    simpa [nsmul_eq_mul] using (Nat.cast_commute m g).eq.symm
  calc
    (f ^ n) (a * b) = (convPreMul f ^ n) (a ⊗ₜ[k] b) := by
      change convPreMul (f ^ n) (a ⊗ₜ[k] b) = _
      rw [convPreMul_pow]
    _ = ((x + y) ^ n) (a ⊗ₜ[k] b) := by rw [hprimitive]
    _ = (∑ i ∈ Finset.range (n + 1),
        x ^ i * y ^ (n - i) * (n.choose i : ConvTensorDual k A))
          (a ⊗ₜ[k] b) := by
        rw [(convTensor_left_right_commute f).add_pow]
    _ = ∑ i ∈ Finset.range (n + 1),
        (f ^ i) a * (f ^ (n - i)) b * (n.choose i : k) := by
      rw [WithConv.ofConv_sum]
      rw [LinearMap.sum_apply]
      change (∑ i ∈ Finset.range (n + 1),
        (x ^ i * y ^ (n - i) * (n.choose i : ConvTensorDual k A))
          (a ⊗ₜ[k] b)) = _
      apply Finset.sum_congr rfl
      intro i hi
      rw [hmul_natCast]
      rw [WithConv.ofConv_smul]
      change (n.choose i) •
        (x ^ i * y ^ (n - i)).ofConv (a ⊗ₜ[k] b) = _
      simp [x, y, nsmul_eq_mul, mul_comm]

private lemma convPow_pow (f : ConvDual k A)
    (hf : ∀ a b : A,
      f (a * b) = f a * counit b + counit a * f b)
    (a : A) (ha : counit (R := k) a = 0) (n : ℕ) :
    (∀ j < n, (f ^ j) (a ^ n) = 0) ∧
      (f ^ n) (a ^ n) = (n.factorial : k) * f a ^ n := by
  induction n with
  | zero =>
      constructor
      · intro j hj
        omega
      · simp
  | succ n ih =>
      constructor
      · intro j hj
        rw [show a ^ n.succ = a ^ n * a by rw [pow_succ], convPow_mul f hf]
        apply Finset.sum_eq_zero
        intro i hi
        have hij : i ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        have hjn : j ≤ n := Nat.le_of_lt_succ hj
        by_cases hin : i < n
        · rw [ih.1 i hin]
          simp
        · have hni : n ≤ i := Nat.le_of_not_gt hin
          have hi_eq : i = n := le_antisymm (hij.trans hjn) hni
          have hj_eq : j = n := le_antisymm hjn (hni.trans hij)
          subst i
          subst j
          simp [ha]
      · rw [show a ^ n.succ = a ^ n * a by rw [pow_succ], convPow_mul f hf]
        rw [Finset.sum_eq_single n]
        · simp [ih.2, Nat.factorial_succ, pow_succ]
          ring
        · intro i hi hin
          have hi_le : i ≤ n + 1 := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
          by_cases hil : i < n
          · rw [ih.1 i hil]
            simp
          · have hnl : n ≤ i := Nat.le_of_not_gt hil
            have hni : n < i := lt_of_le_of_ne hnl (Ne.symm hin)
            have hi_eq : i = n + 1 := le_antisymm hi_le (Nat.succ_le_of_lt hni)
            subst i
            simp [ha]
        · simp

private lemma counit_ker_eq_maximalIdeal [IsLocalRing A] :
    RingHom.ker (Bialgebra.counitAlgHom k A).toRingHom =
      IsLocalRing.maximalIdeal A := by
  apply IsLocalRing.ker_eq_maximalIdeal
  intro x
  obtain ⟨a, ha⟩ := Bialgebra.counit_surjective (R := k) (A := A) x
  exact ⟨a, ha⟩

private def augmentationIdealPart
    [IsLocalRing A]
    (hker : RingHom.ker (Bialgebra.counitAlgHom k A).toRingHom =
      IsLocalRing.maximalIdeal A) :
    A →ₗ[k] IsLocalRing.maximalIdeal A where
  toFun a :=
    ⟨a - algebraMap k A (counit a), by
      rw [← hker, RingHom.mem_ker]
      simp⟩
  map_add' a b := by
    ext
    simp
    ring
  map_smul' r a := by
    ext
    simp [Algebra.smul_def]
    ring

@[simp]
private lemma coe_augmentationIdealPart
    [IsLocalRing A]
    (hker : RingHom.ker (Bialgebra.counitAlgHom k A).toRingHom =
      IsLocalRing.maximalIdeal A) (a : A) :
    (augmentationIdealPart hker a : A) =
      a - algebraMap k A (counit (R := k) a) := by
  rfl

private def infinitesimalFunctional
    [IsLocalRing A]
    (hker : RingHom.ker (Bialgebra.counitAlgHom k A).toRingHom =
      IsLocalRing.maximalIdeal A)
    (phi : Module.Dual k (IsLocalRing.CotangentSpace A)) : ConvDual k A :=
  toConv <| phi.comp <|
    ((IsLocalRing.maximalIdeal A).toCotangent.restrictScalars k).comp
      (augmentationIdealPart hker)

@[simp]
private lemma infinitesimalFunctional_apply
    [IsLocalRing A]
    (hker : RingHom.ker (Bialgebra.counitAlgHom k A).toRingHom =
      IsLocalRing.maximalIdeal A)
    (phi : Module.Dual k (IsLocalRing.CotangentSpace A)) (a : A) :
    infinitesimalFunctional hker phi a =
      phi ((IsLocalRing.maximalIdeal A).toCotangent
        (augmentationIdealPart hker a)) := by
  rfl

private lemma infinitesimalFunctional_mul
    [IsLocalRing A]
    (hker : RingHom.ker (Bialgebra.counitAlgHom k A).toRingHom =
      IsLocalRing.maximalIdeal A)
    (phi : Module.Dual k (IsLocalRing.CotangentSpace A)) (a b : A) :
    infinitesimalFunctional hker phi (a * b) =
      infinitesimalFunctional hker phi a * counit b +
        counit a * infinitesimalFunctional hker phi b := by
  let m := IsLocalRing.maximalIdeal A
  let t : m →ₗ[k] m.Cotangent := m.toCotangent.restrictScalars k
  have hcot : m.toCotangent (augmentationIdealPart hker (a * b)) =
      (counit (R := k) b : k) •
          m.toCotangent (augmentationIdealPart hker a) +
        (counit (R := k) a : k) •
          m.toCotangent (augmentationIdealPart hker b) := by
    change t (augmentationIdealPart hker (a * b)) =
      (counit (R := k) b : k) • t (augmentationIdealPart hker a) +
        (counit (R := k) a : k) • t (augmentationIdealPart hker b)
    rw [← map_smul t, ← map_smul t, ← map_add t]
    apply m.toCotangent_eq.mpr
    change ((augmentationIdealPart hker (a * b) -
      ((counit (R := k) b : k) • augmentationIdealPart hker a +
        (counit (R := k) a : k) • augmentationIdealPart hker b) : m) : A) ∈ m ^ 2
    rw [pow_two]
    convert Ideal.mul_mem_mul (augmentationIdealPart hker a).property
      (augmentationIdealPart hker b).property using 1
    rw [Submodule.coe_sub, Submodule.coe_add,
      Submodule.coe_smul_of_tower, Submodule.coe_smul_of_tower,
      coe_augmentationIdealPart, coe_augmentationIdealPart,
      coe_augmentationIdealPart]
    rw [Algebra.smul_def, Algebra.smul_def]
    change (a * b - algebraMap k A (counit (R := k) (a * b))) -
      (algebraMap k A (counit (R := k) b) *
          (a - algebraMap k A (counit (R := k) a)) +
        algebraMap k A (counit (R := k) a) *
          (b - algebraMap k A (counit (R := k) b))) =
        (a - algebraMap k A (counit (R := k) a)) *
          (b - algebraMap k A (counit (R := k) b))
    rw [Bialgebra.counit_mul]
    rw [map_mul]
    ring
  simp only [infinitesimalFunctional_apply]
  rw [hcot, map_add, map_smul, map_smul]
  ring

/-- A finite-dimensional local commutative Hopf algebra over a
characteristic-zero field is a field. -/
public theorem finiteDimensional_local_commutativeHopfAlgebra_isField
    (k : Type u) (A : Type v) [Field k] [CharZero k] [CommRing A]
    [HopfAlgebra k A] [FiniteDimensional k A] [IsLocalRing A] : IsField A := by
  let _ : IsNoetherianRing A := IsNoetherianRing.of_finite k A
  apply IsLocalRing.subsingleton_cotangentSpace_iff.mp
  constructor
  intro x y
  suffices hzero : ∀ z : IsLocalRing.CotangentSpace A, z = 0 by
    rw [hzero x, hzero y]
  intro z
  by_contra hz
  let m := IsLocalRing.maximalIdeal A
  obtain ⟨a, rfl⟩ := m.toCotangent_surjective z
  obtain ⟨phi, hphi⟩ := Module.Projective.exists_dual_eq_one k hz
  let hker := counit_ker_eq_maximalIdeal (k := k) (A := A)
  let f := infinitesimalFunctional hker phi
  have ha : counit (R := k) (a : A) = 0 := by
    have hamem := a.property
    change (a : A) ∈ IsLocalRing.maximalIdeal A at hamem
    rw [← hker, RingHom.mem_ker] at hamem
    exact hamem
  have hqa : augmentationIdealPart hker (a : A) = a := by
    ext
    simp [ha]
  have hfa : f (a : A) = 1 := by
    change infinitesimalFunctional hker phi (a : A) = 1
    rw [infinitesimalFunctional_apply, hqa]
    change phi (m.toCotangent a) = 1
    exact hphi
  have _ : IsArtinianRing A := isArtinian_of_tower k inferInstance
  obtain ⟨n, hn⟩ :=
    (isArtinianRing_iff_isNilpotent_maximalIdeal A).mp (inferInstance : IsArtinianRing A)
  have han_mem : (a : A) ^ n ∈ m ^ n := Ideal.pow_mem_pow a.property n
  have han : (a : A) ^ n = 0 := by
    rw [hn] at han_mem
    exact han_mem
  have hdiag := (convPow_pow f (infinitesimalFunctional_mul hker phi)
    (a : A) ha n).2
  rw [han] at hdiag
  have hfac : (n.factorial : k) = 0 := by
    simpa [hfa] using hdiag.symm
  exact (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)) hfac

/-- The structure map of a finite-dimensional local commutative Hopf algebra
over a characteristic-zero field is bijective, so the Hopf algebra is trivial. -/
public theorem finiteDimensional_local_commutativeHopfAlgebra_algebraMap_bijective
    (k : Type u) (A : Type v) [Field k] [CharZero k] [CommRing A]
    [HopfAlgebra k A] [FiniteDimensional k A] [IsLocalRing A] :
    Function.Bijective (algebraMap k A) := by
  have hfield := finiteDimensional_local_commutativeHopfAlgebra_isField k A
  have hker : RingHom.ker (Bialgebra.counitAlgHom k A).toRingHom = ⊥ := by
    rw [counit_ker_eq_maximalIdeal]
    exact IsLocalRing.isField_iff_maximalIdeal_eq.mp hfield
  have hinjective : Function.Injective (Bialgebra.counitAlgHom k A) :=
    (RingHom.injective_iff_ker_eq_bot _).mpr hker
  constructor
  · exact Bialgebra.algebraMap_injective A
  · intro a
    refine ⟨counit a, ?_⟩
    apply hinjective
    simp

/-- A finite-dimensional local commutative Hopf algebra over a
characteristic-zero field is reduced. -/
public theorem finiteDimensional_local_commutativeHopfAlgebra_isReduced
    (k : Type u) (A : Type v) [Field k] [CharZero k] [CommRing A]
    [HopfAlgebra k A] [FiniteDimensional k A] [IsLocalRing A] :
    IsReduced A := by
  have hfield := finiteDimensional_local_commutativeHopfAlgebra_isField k A
  have hker : RingHom.ker (Bialgebra.counitAlgHom k A).toRingHom = ⊥ := by
    rw [counit_ker_eq_maximalIdeal]
    exact IsLocalRing.isField_iff_maximalIdeal_eq.mp hfield
  apply isReduced_of_injective (Bialgebra.counitAlgHom k A)
  exact (RingHom.injective_iff_ker_eq_bot _).mpr hker

/-- The nilradical of a finite-dimensional local commutative Hopf algebra over
a characteristic-zero field vanishes. -/
public theorem finiteDimensional_local_commutativeHopfAlgebra_nilradical_eq_bot
    (k : Type u) (A : Type v) [Field k] [CharZero k] [CommRing A]
    [HopfAlgebra k A] [FiniteDimensional k A] [IsLocalRing A] :
    nilradical A = ⊥ :=
  nilradical_eq_bot_iff.mpr
    (finiteDimensional_local_commutativeHopfAlgebra_isReduced k A)

end Theory.AlgebraicGroup
