module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.Reduction
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Relative adjoint covariance and odd-characteristic centrality

An integral tensor from the E6 adjoint lattice to endomorphisms of a higher
representation is specified by its values on the 78 source basis vectors.
Generator covariance is a finite matrix identity over `ℤ[X]`. Specializing
that identity and extending linearly gives equivariance over every field;
products and inverse letters then propagate it to all six-node words.
A source-trivial word consequently commutes with the tensor image.

The actual E7 and E8 simple-root curves have zero cubic coefficient: all their
roots have squared length two, so a displacement by three times a root is
impossible. Divided-power convolution expresses twice the quadratic coefficient
as the square of the first coefficient. Hence in odd characteristic, including
characteristic three, pinning of the first operators in the tensor image gives
commutation with every root curve and every six-node evaluation.

`IntegralAdjointData` records only the integral basis tensor, generator
covariance and pinning; construction of these data remains a separate
representation calculation. In particular it contains no word-kernel,
center-exponent, diagram-action or group-isomorphism premise.

Source: GLS3 §§1.12 and 2.6.2 (`refs/KGroup/GLS3/chapter2.tex`), the common
integral lattice construction of subsystem representations. The geometric
cubic-vanishing argument follows the existing F4 `Intertwining.Simple.RootGeometry`
proof, applied here to the literal E7 and E8 root sets.
-/

@[expose] public section
noncomputable section
open Matrix RootPairing.SimpleGeckGroup
namespace TwistedE6.FoldedSubsystem.HigherRealizations.KernelCentrality
attribute [local instance] Classical.decEq

section Words
variable {m n α S : Type*} [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n] [CommRing S]

private theorem inverse_covariance
    (A : (Matrix m m S)ˣ) (B : (Matrix n n S)ˣ)
    (J : (m → S) →ₗ[S] Matrix n n S)
    (h : ∀ x, B.val * J x = J (A.val *ᵥ x) * B.val) (x : m → S) :
    B⁻¹.val * J x = J (A⁻¹.val *ᵥ x) * B⁻¹.val := by
  have hx := h (A⁻¹.val *ᵥ x)
  simp only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at hx
  calc
    B⁻¹.val * J x = B⁻¹.val * (J x * B.val) * B⁻¹.val := by
      simp [Matrix.mul_assoc]
    _ = B⁻¹.val * (B.val * J (A⁻¹.val *ᵥ x)) * B⁻¹.val := by rw [hx]
    _ = J (A⁻¹.val *ᵥ x) * B⁻¹.val := by simp [← Matrix.mul_assoc]

/-- Equivariance for generators propagates to every word, including inverse letters. -/
theorem word_covariance
    (a : FreeGroup α →* (Matrix m m S)ˣ) (b : FreeGroup α →* (Matrix n n S)ˣ)
    (J : (m → S) →ₗ[S] Matrix n n S)
    (h : ∀ z x, (b (FreeGroup.of z)).val * J x =
      J ((a (FreeGroup.of z)).val *ᵥ x) * (b (FreeGroup.of z)).val)
    (w : FreeGroup α) (x : m → S) :
    (b w).val * J x = J ((a w).val *ᵥ x) * (b w).val := by
  induction w using FreeGroup.induction_on generalizing x with
  | C1 => simp
  | of z => exact h z x
  | inv_of z ih => simpa only [map_inv] using inverse_covariance _ _ J ih x
  | mul w z hw hz =>
    simp only [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec]
    rw [Matrix.mul_assoc, hz, ← Matrix.mul_assoc, hw, Matrix.mul_assoc]

/-- Source-trivial words centralize the image of the adjoint tensor. -/
theorem commute_tensor_of_source_one
    (a : FreeGroup α →* (Matrix m m S)ˣ) (b : FreeGroup α →* (Matrix n n S)ˣ)
    (J : (m → S) →ₗ[S] Matrix n n S)
    (h : ∀ z x, (b (FreeGroup.of z)).val * J x =
      J ((a (FreeGroup.of z)).val *ᵥ x) * (b (FreeGroup.of z)).val)
    (w : FreeGroup α) (hw : a w = 1) (x : m → S) :
    Commute (b w).val (J x) := by
  change (b w).val * J x = J x * (b w).val
  have hh := word_covariance a b J h w x
  simpa only [hw, Units.val_one, Matrix.one_mulVec] using hh

/-- Commutation with the generating letters implies commutation with every evaluation. -/
theorem commute_word {G : Type*} [Group G] (b : FreeGroup α →* G) (g : G)
    (h : ∀ x, Commute g (b (FreeGroup.of x))) (w : FreeGroup α) : Commute g (b w) := by
  induction w using FreeGroup.induction_on with
  | C1 => simpa only [map_one] using Commute.one_right g
  | of x => exact h x
  | inv_of x hx => simpa only [map_inv] using hx.inv_right
  | mul x y hx hy => simpa only [map_mul] using hx.mul_right hy
end Words

section Tensor
variable {m n : Type*} [Fintype m]

/-- Scalar extension of an integral tensor, with one matrix for each source basis vector. -/
def tensorMap (T : m → Matrix n n ℤ) (S : Type*) [CommRing S] :
    (m → S) →ₗ[S] Matrix n n S where
  toFun x := ∑ j, x j • (T j).map (Int.castRingHom S)
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [mul_smul, Finset.smul_sum]

@[simp] theorem tensorMap_apply (T : m → Matrix n n ℤ) (S : Type*) [CommRing S]
    (x : m → S) : tensorMap T S x = ∑ j, x j • (T j).map (Int.castRingHom S) := rfl

theorem tensorMap_single [DecidableEq m] (T : m → Matrix n n ℤ)
    (S : Type*) [CommRing S] (j : m) :
    tensorMap T S (Pi.single j 1) = (T j).map (Int.castRingHom S) := by
  simp [tensorMap, Pi.single_apply]

variable [Fintype n] [DecidableEq n]

/-- Checking covariance on the integral basis suffices after scalar extension. -/
theorem covariance_of_basis (T : m → Matrix n n ℤ) (S : Type*) [CommRing S]
    (A : Matrix m m S) (B : Matrix n n S)
    (h : ∀ j, B * (T j).map (Int.castRingHom S) =
      (∑ k, A k j • (T k).map (Int.castRingHom S)) * B) (x : m → S) :
    B * tensorMap T S x = tensorMap T S (A *ᵥ x) * B := by
  simp only [tensorMap_apply, Matrix.mul_sum, Matrix.mul_smul, h,
    Matrix.sum_mul, smul_mul_assoc, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Matrix.mulVec, dotProduct, Finset.sum_smul, mul_comm (x _)]
end Tensor

section Curves
variable {κ n : Type*} [Fintype n] [DecidableEq n]
    (D : IntegralCubicFamily κ n) {F : Type*} [Field F]

/-- Only division by two is needed for quadratic root curves. In particular this includes
characteristic three; vanishing of the integral cubic coefficient is checked separately. -/
theorem commute_curve_of_first_coefficient (htwo : (2 : F) ≠ 0)
    (i : κ) (hthree : D.dividedPower i 3 = 0)
    (C : Matrix n n F) (h : Commute C (D.coefficient i 1)) (t : F) :
    Commute C (D.curve i t) := by
  have hsq : D.coefficient (S := F) i 1 ^ 2 = (2 : F) • D.coefficient i 2 := by
    simpa [pow_two] using
      D.coefficient_mul (S := F) i 1 1
  have htwo' : Commute C (D.coefficient i 2) := by
    have hh := (h.pow_right 2).eq
    rw [hsq, mul_smul_comm, smul_mul_assoc] at hh
    exact (smul_right_injective _ htwo) hh
  have hzero : D.coefficient (S := F) i 3 = 0 := by
    simp [IntegralCubicFamily.coefficient, hthree]
  change C * D.curve i t = D.curve i t * C
  simp only [IntegralCubicFamily.curve, hzero, smul_zero, add_zero, mul_add, add_mul,
    mul_one, one_mul, mul_smul_comm, smul_mul_assoc, h.eq, htwo'.eq]
end Curves

open Theory.AlgebraicGroup.StandardRootSystem
local instance : Fintype typeE7Roots := Fintype.ofFinite _
local instance : Fintype typeE8Roots := Fintype.ofFinite _

/-- Use the same signed, numbered six-node alphabet for each integral family. -/
def numberedFamily {ι R M N : Type*} [CommRing R] [IsDomain R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
    {b : P.Base} [Fintype ι] [DecidableEq ι] (node : Fin 6 → b.support) :
    IntegralCubicFamily (Bool × Fin 6) (b.support ⊕ ι) where
  dividedPower a k := (simpleFamily (b := b)).dividedPower (a.1, node a.2) k
  mul a := (simpleFamily (b := b)).mul (a.1, node a.2)
  vanish a := (simpleFamily (b := b)).vanish (a.1, node a.2)

/-- The literal source E6 divided powers. -/
def sourceFamily : IntegralCubicFamily (Bool × Fin 6) Index := numberedFamily simpleIndex

/-- The first six E7 nodes, in the numbering used by `e7Six`. -/
def e7Family : IntegralCubicFamily (Bool × Fin 6)
    (typeE7RootPairing_base.support ⊕ typeE7Roots) :=
  numberedFamily fun i => typeE7RootPairing_baseEquiv (i.castLE (by decide))

/-- The first six E8 nodes, in the numbering used by `e8Six`. -/
def e8Family : IntegralCubicFamily (Bool × Fin 6)
    (typeE8RootPairing_base.support ⊕ typeE8Roots) :=
  numberedFamily fun i => typeE8RootPairing_baseEquiv (i.castLE (by decide))


private theorem no_triple_displacement {r : ℕ} (i j k : Vec r)
    (hi : dot i i = 2) (hj : dot j j = 2) (hk : dot k k = 2) :
    k ≠ j + (3 : ℝ) • i := by
  intro h
  have hpos : 0 ≤ dot (k + j) (k + j) :=
    Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)
  have hdiff : dot (k - j) (k - j) = 9 * dot i i := by
    have hd : k - j = (3 : ℝ) • i := by rw [h]; abel
    rw [hd]
    change ((3 : ℝ) • i) ⬝ᵥ ((3 : ℝ) • i) = 9 * (i ⬝ᵥ i)
    rw [smul_dotProduct, dotProduct_smul]
    simp only [smul_eq_mul]
    ring
  have hpar : dot (k - j) (k - j) + dot (k + j) (k + j) =
      2 * (dot k k + dot j j) := by
    change (k - j) ⬝ᵥ (k - j) + (k + j) ⬝ᵥ (k + j) = 2 * (k ⬝ᵥ k + j ⬝ᵥ j)
    simp only [sub_dotProduct, dotProduct_sub, add_dotProduct, dotProduct_add]
    ring
  nlinarith

private theorem e7_no_triple (i j k : typeE7Roots) :
    typeE7RootPairing.root k ≠
      typeE7RootPairing.root j + (3 : ℕ) • typeE7RootPairing.root i := by
  intro h
  have hh := congrArg (fun x : typeE7Space => (x : Vec 8)) h
  change k.val = j.val + (3 : ℕ) • i.val at hh
  apply no_triple_displacement i.val j.val k.val
    (typeE7Root_dot_self i) (typeE7Root_dot_self j) (typeE7Root_dot_self k)
  simpa only [ofNat_smul_eq_nsmul] using hh

private theorem e8_no_triple (i j k : typeE8Roots) :
    typeE8RootPairing.root k ≠
      typeE8RootPairing.root j + (3 : ℕ) • typeE8RootPairing.root i := by
  simpa only [typeE8RootPairing_root, ofNat_smul_eq_nsmul] using
    no_triple_displacement i.val j.val k.val
      (typeE8Root_dot_self i) (typeE8Root_dot_self j) (typeE8Root_dot_self k)

/-- The actual integral E7 simple curves are quadratic, before any specialization. -/
theorem e7_cubic_zero (a : Bool × Fin 6) : e7Family.dividedPower a 3 = 0 := by
  have he (i : typeE7RootPairing_base.support) :
      RootPairing.IntegralGeckConstruction.eDividedPower i 3 = 0 := by
    ext (j | j) (k | k)
    · rfl
    · rfl
    · rfl
    · exact if_neg (e7_no_triple i k j)
  rcases a with ⟨s, i⟩
  cases s
  · simp only [e7Family, numberedFamily, simpleFamily,
      RootPairing.IntegralGeckConstruction.fDividedPower, he, Matrix.mul_zero, Matrix.zero_mul]
  · exact he _

/-- The same quadratic truncation for the actual E8 simple curves. -/
theorem e8_cubic_zero (a : Bool × Fin 6) : e8Family.dividedPower a 3 = 0 := by
  have he (i : typeE8RootPairing_base.support) :
      RootPairing.IntegralGeckConstruction.eDividedPower i 3 = 0 := by
    ext (j | j) (k | k)
    · rfl
    · rfl
    · rfl
    · exact if_neg (e8_no_triple i k j)
  rcases a with ⟨s, i⟩
  cases s
  · simp only [e8Family, numberedFamily, simpleFamily,
      RootPairing.IntegralGeckConstruction.fDividedPower, he, Matrix.mul_zero, Matrix.zero_mul]
  · exact he _

section Data
variable {n : Type*} [Fintype n] [DecidableEq n]
    (D : IntegralCubicFamily (Bool × Fin 6) n)

/-- A finite integral adjoint calculation. The covariance equations are checked on
source basis vectors and single generators over `ℤ[X]`, before specialization.
Pinning asks only that each higher simple operator lie in the image of the tensor.
No relation,
center, exponent, diagram action, or group isomorphism is a field of this structure. -/
structure IntegralAdjointData where
  tensor : Index → Matrix n n ℤ
  covariance : ∀ (a : Bool × Fin 6) (j : Index),
    D.curve a (Polynomial.X : Polynomial ℤ) *
        (tensor j).map (Int.castRingHom (Polynomial ℤ)) =
      (∑ k, (sourceFamily.curve a (Polynomial.X : Polynomial ℤ)) k j •
        (tensor k).map (Int.castRingHom (Polynomial ℤ))) *
          D.curve a (Polynomial.X : Polynomial ℤ)
  pinning : ∀ a, ∃ x : Index → ℤ, ∑ j, x j • tensor j = D.dividedPower a 1

namespace IntegralAdjointData
variable {D} (d : IntegralAdjointData D)

private theorem map_smul_matrix {S T : Type*} [CommRing S] [CommRing T]
    (f : S →+* T) (r : S) (A : Matrix n n S) :
    f.mapMatrix (r • A) = f r • f.mapMatrix A := by
  ext i j
  exact f.map_mul _ _

/-- A polynomial identity gives the required generator identity in every field,
without division by factorials in the target characteristic. -/
theorem covariance_specialize (F : Type*) [Field F]
    (a : Bool × Fin 6) (t : F) (x : Index → F) :
    D.curve a t * tensorMap d.tensor F x =
      tensorMap d.tensor F (sourceFamily.curve a t *ᵥ x) * D.curve a t := by
  apply covariance_of_basis
  intro j
  let ev : Polynomial ℤ →+* F := Polynomial.eval₂RingHom (Int.castRingHom F) t
  have hm (A : Matrix n n ℤ) :
      ev.mapMatrix (A.map (Int.castRingHom (Polynomial ℤ))) = A.map (Int.castRingHom F) := by
    ext i j
    exact map_intCast ev (A i j)
  have hs : (sourceFamily.curve a (Polynomial.X : Polynomial ℤ)).map ev =
      sourceFamily.curve a t := by
    simpa [ev] using sourceFamily.map_curve ev a Polynomial.X
  have ht : (D.curve a (Polynomial.X : Polynomial ℤ)).map ev = D.curve a t := by
    simpa [ev] using D.map_curve ev a Polynomial.X
  have ht' : ev.mapMatrix (D.curve a (Polynomial.X : Polynomial ℤ)) = D.curve a t := ht
  have hh := congrArg ev.mapMatrix (d.covariance a j)
  simp only [map_mul, map_sum, map_smul_matrix, hm, ht'] at hh
  have he (k : Index) :
      ev ((sourceFamily.curve a (Polynomial.X : Polynomial ℤ)) k j) =
        (sourceFamily.curve a t) k j := congrFun (congrFun hs k) j
  simpa only [he] using hh

/-- The integral pinning remains valid after changing coefficients. -/
theorem coefficient_one_mem_range (F : Type*) [Field F] (a : Bool × Fin 6) :
    D.coefficient (S := F) a 1 ∈ Set.range (tensorMap d.tensor F) := by
  obtain ⟨x, hx⟩ := d.pinning a
  refine ⟨fun j => (x j : F), ?_⟩
  have hh := congrArg (Int.castRingHom F).mapMatrix hx
  simpa only [map_sum, map_zsmul, RingHom.mapMatrix_apply,
    ← Int.cast_smul_eq_zsmul F, tensorMap_apply, IntegralCubicFamily.coefficient] using hh

include d in
/-- From the local tensor calculation to centrality of every source-trivial word. -/
theorem kernel_central (F : Type*) [Field F] (htwo : (2 : F) ≠ 0)
    (hcubic : ∀ a, D.dividedPower a 3 = 0)
    (a : SixNodeWord F →* (Matrix Index Index F)ˣ)
    (b : SixNodeWord F →* (Matrix n n F)ˣ)
    (ha : ∀ s i t, (a (FreeGroup.of (s, i, t))).val = sourceFamily.curve (s, i) t)
    (hb : ∀ s i t, (b (FreeGroup.of (s, i, t))).val = D.curve (s, i) t)
    (w : SixNodeWord F) (hw : a w = 1) (z : SixNodeWord F) :
    Commute (b w) (b z) := by
  have hc (x : Index → F) : Commute (b w).val (tensorMap d.tensor F x) := by
    apply commute_tensor_of_source_one a b _ _ w hw
    rintro ⟨s, i, t⟩ y
    rw [ha, hb]
    exact d.covariance_specialize F (s, i) t y
  apply commute_word
  rintro ⟨s, i, t⟩
  apply Units.ext
  change Commute (b w).val (b (FreeGroup.of (s, i, t))).val
  rw [hb]
  apply commute_curve_of_first_coefficient D htwo (s, i) (hcubic (s, i))
  obtain ⟨x, hx⟩ := d.coefficient_one_mem_range F (s, i)
  rw [← hx]
  exact hc x
end IntegralAdjointData
end Data

/-- Odd characteristic makes two invertible, including in characteristic three. -/
theorem two_ne_zero_of_odd (F : Type*) [Field F] (hodd : Odd (ringChar F)) :
    (2 : F) ≠ 0 := by
  intro h
  rcases (Nat.dvd_prime Nat.prime_two).mp (ringChar.dvd h) with hc | hc
  · exact CharP.ringChar_ne_one (R := F) hc
  · exact hodd.not_two_dvd_nat (by rw [hc])

end TwistedE6.FoldedSubsystem.HigherRealizations.KernelCentrality
