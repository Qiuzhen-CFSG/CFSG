module

public import Theory.Character.ModularBlock.BrauerCoefficientExtension
public import Mathlib.RepresentationTheory.Character
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly

/-!
# Brauer characters at a prescribed modular place

For the actual principal congruence datum, lift odd-order eigenvalues from its
splitting residue field to its cyclotomic order and then to the complex numbers.
The character is the sum over characteristic-polynomial roots, with algebraic
multiplicity. It is not obtained by lifting a residue-field trace: reduction of
the eigenvalue sum gives that trace, but the sum retains integer multiplicities.

The root equivalences in `BrauerCoefficientExtension` provide the lifts at the
chosen prime. Eigenvectors show that eigenvalues of an odd-order group element
have odd order dividing the group order. Similarity invariance of characteristic
polynomials proves invariance under conjugation and representation equivalence.
Thus the sums define complex functions on two-regular conjugacy classes.

This is the shared representation-level definition for principal-block Brauer
bases and the modular characters occurring in ABG III.6, pp.88–89, equation (4).
It does not assume a basis, decomposition coefficients, or Cartan invariants.
-/

public section
noncomputable section

open scoped Classical

namespace ModularBlock.BrauerCharacter

open PrincipalBlockConstruction BrauerCoefficientExtension

universe u v w
variable {G : Type u} [Group G] [Finite G]

/-- A root in the cyclotomic order determined by its reduction and odd order. -/
@[expose] def liftAtOrder (d : PrincipalCongruenceBlockData G)
    (n : ℕ) (hn : Odd n) (hdiv : n ∣ Nat.card G)
    (value : splittingField d) (hvalue : value ^ n = 1) : cyclotomicOrder d.eta := by
  have hnonzero : n ≠ 0 := by intro hzero; simp [hzero] at hn
  let unit := (IsUnit.of_pow_eq_one hvalue hnonzero).unit
  let root : rootsOfUnity n (splittingField d) :=
    ⟨unit, (mem_rootsOfUnity' n unit).mpr (by simpa [unit] using hvalue)⟩
  exact (((rootEquiv d n hn hdiv).symm root).val : cyclotomicOrder d.eta)

theorem reduction_liftAtOrder (d : PrincipalCongruenceBlockData G)
    (n : ℕ) (hn : Odd n) (hdiv : n ∣ Nat.card G)
    (value : splittingField d) (hvalue : value ^ n = 1) :
    reduction d (liftAtOrder d n hn hdiv value hvalue) = value := by
  unfold liftAtOrder
  rw [rootEquiv_symm_reduction]
  exact IsUnit.unit_spec _

theorem liftAtOrder_pow (d : PrincipalCongruenceBlockData G)
    (n : ℕ) (hn : Odd n) (hdiv : n ∣ Nat.card G)
    (value : splittingField d) (hvalue : value ^ n = 1) :
    liftAtOrder d n hn hdiv value hvalue ^ n = 1 := by
  unfold liftAtOrder
  exact (mem_rootsOfUnity' n _).mp ((rootEquiv d n hn hdiv).symm _).property

theorem odd_root_eq_of_reduction_eq (d : PrincipalCongruenceBlockData G)
    {first second : cyclotomicOrder d.eta} {n m : ℕ}
    (hn : Odd n) (hm : Odd m) (hnG : n ∣ Nat.card G) (hmG : m ∣ Nat.card G)
    (hfirst : first ^ n = 1) (hsecond : second ^ m = 1)
    (hreduction : reduction d first = reduction d second) : first = second := by
  have hbound : Odd (Nat.lcm n m) := (hn.mul hm).of_dvd_nat (Nat.lcm_dvd_mul n m)
  have hnonzero : Nat.lcm n m ≠ 0 := by intro hzero; simp [hzero] at hbound
  have hfirstBound : first ^ Nat.lcm n m = 1 := by
    obtain ⟨factor, hfactor⟩ := Nat.dvd_lcm_left n m
    rw [hfactor, pow_mul, hfirst, one_pow]
  have hsecondBound : second ^ Nat.lcm n m = 1 := by
    obtain ⟨factor, hfactor⟩ := Nat.dvd_lcm_right n m
    rw [hfactor, pow_mul, hsecond, one_pow]
  let firstRoot : rootsOfUnity (Nat.lcm n m) (cyclotomicOrder d.eta) :=
    ⟨(IsUnit.of_pow_eq_one hfirstBound hnonzero).unit,
      (mem_rootsOfUnity' _ _).mpr (by simpa using hfirstBound)⟩
  let secondRoot : rootsOfUnity (Nat.lcm n m) (cyclotomicOrder d.eta) :=
    ⟨(IsUnit.of_pow_eq_one hsecondBound hnonzero).unit,
      (mem_rootsOfUnity' _ _).mpr (by simpa using hsecondBound)⟩
  have heq : firstRoot = secondRoot := by
    apply (rootEquiv d (Nat.lcm n m) hbound (Nat.lcm_dvd hnG hmG)).injective
    rw [rootEquiv_apply, rootEquiv_apply]
    apply Subtype.ext
    apply Units.ext
    simpa [firstRoot, secondRoot] using hreduction
  have hvalues := congrArg (fun root : rootsOfUnity (Nat.lcm n m) (cyclotomicOrder d.eta) =>
    (root.val : cyclotomicOrder d.eta)) heq
  simpa [firstRoot, secondRoot] using hvalues

/-- The domain of eigenvalues needed for finite-group Brauer characters. -/
@[expose] def IsLiftable (d : PrincipalCongruenceBlockData G)
    (value : splittingField d) : Prop :=
  ∃ n : ℕ, Odd n ∧ n ∣ Nat.card G ∧ value ^ n = 1

/-- Lift an odd-order root through the actual modular prime; zero elsewhere.
The arbitrary value off `IsLiftable` is never used at a two-regular element. -/
@[expose] def eigenvalueLift (d : PrincipalCongruenceBlockData G)
    (value : splittingField d) : cyclotomicOrder d.eta :=
  if hvalue : IsLiftable d value then
    liftAtOrder d hvalue.choose hvalue.choose_spec.1 hvalue.choose_spec.2.1
      value hvalue.choose_spec.2.2
  else 0

theorem reduction_eigenvalueLift (d : PrincipalCongruenceBlockData G)
    (value : splittingField d) (hvalue : IsLiftable d value) :
    reduction d (eigenvalueLift d value) = value := by
  rw [eigenvalueLift, dif_pos hvalue, reduction_liftAtOrder]

theorem eigenvalueLift_eq_liftAtOrder (d : PrincipalCongruenceBlockData G)
    (n : ℕ) (hn : Odd n) (hdiv : n ∣ Nat.card G)
    (value : splittingField d) (hvalue : value ^ n = 1) :
    eigenvalueLift d value = liftAtOrder d n hn hdiv value hvalue := by
  have hlift : IsLiftable d value := ⟨n, hn, hdiv, hvalue⟩
  rw [eigenvalueLift, dif_pos hlift]
  apply odd_root_eq_of_reduction_eq d hlift.choose_spec.1 hn hlift.choose_spec.2.1 hdiv
    (liftAtOrder_pow _ _ _ _ _ _) (liftAtOrder_pow _ _ _ _ _ _)
  rw [reduction_liftAtOrder, reduction_liftAtOrder]

@[simp] theorem eigenvalueLift_one (d : PrincipalCongruenceBlockData G) :
    eigenvalueLift d 1 = 1 := by
  rw [eigenvalueLift_eq_liftAtOrder d 1 odd_one (one_dvd _) 1 (one_pow _)]
  simpa only [pow_one] using liftAtOrder_pow d 1 odd_one (one_dvd _) 1 (one_pow _)

variable (d : PrincipalCongruenceBlockData G)
variable {V : Type v} [AddCommGroup V] [Module (splittingField d) V]
  [FiniteDimensional (splittingField d) V]

theorem eigenvalue_pow_orderOf (representation : Representation (splittingField d) G V)
    (element : G) (value : splittingField d)
    (hvalue : value ∈ (representation element).charpoly.roots) :
    value ^ orderOf element = 1 := by
  have heigen := (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr
    ((Polynomial.mem_roots (LinearMap.charpoly_monic _).ne_zero).mp hvalue)
  obtain ⟨vector, hvector⟩ := heigen.exists_hasEigenvector
  have hpower := hvector.pow_apply (orderOf element)
  rw [← map_pow, pow_orderOf_eq_one, map_one] at hpower
  have hneq := hvector.2
  exact (smul_left_injective (splittingField d) hneq)
    (by simpa only [one_smul, Module.End.one_apply] using hpower.symm)

theorem eigenvalue_isLiftable (representation : Representation (splittingField d) G V)
    (element : G) (hodd : Odd (orderOf element)) (value : splittingField d)
    (hvalue : value ∈ (representation element).charpoly.roots) : IsLiftable d value :=
  ⟨orderOf element, hodd, orderOf_dvd_natCard element,
    eigenvalue_pow_orderOf d representation element value hvalue⟩

/-- The cyclotomic-valued eigenvalue sum, retaining algebraic multiplicities. -/
@[expose] def integralValue (representation : Representation (splittingField d) G V)
    (element : G) : cyclotomicOrder d.eta :=
  ((representation element).charpoly.roots.map (eigenvalueLift d)).sum

/-- Characteristic-zero value of the lifted eigenvalue sum. -/
@[expose] def value (representation : Representation (splittingField d) G V)
    (element : G) : ℂ := (integralValue d representation element : ℂ)

theorem reduction_integralValue (representation : Representation (splittingField d) G V)
    (element : G) (hodd : Odd (orderOf element)) :
    reduction d (integralValue d representation element) = representation.character element := by
  rw [integralValue, map_multiset_sum, Multiset.map_map]
  have hmap : (representation element).charpoly.roots.map
      (reduction d ∘ eigenvalueLift d) = (representation element).charpoly.roots := by
    conv_rhs => rw [← Multiset.map_id (representation element).charpoly.roots]
    apply Multiset.map_congr rfl
    intro root hroot
    exact reduction_eigenvalueLift d root
      (eigenvalue_isLiftable d representation element hodd root hroot)
  rw [hmap]
  exact (Module.End.trace_eq_sum_roots_charpoly_of_splits
    (IsAlgClosed.splits _)).symm

theorem integralValue_conj (representation : Representation (splittingField d) G V)
    (element conjugator : G) :
    integralValue d representation (conjugator * element * conjugator⁻¹) =
      integralValue d representation element := by
  let equiv : V ≃ₗ[splittingField d] V :=
    LinearEquiv.ofLinearMap (representation conjugator) (representation conjugator⁻¹)
      (by change representation conjugator * representation conjugator⁻¹ = 1
          rw [← map_mul, mul_inv_cancel, map_one])
      (by change representation conjugator⁻¹ * representation conjugator = 1
          rw [← map_mul, inv_mul_cancel, map_one])
  have heq : representation (conjugator * element * conjugator⁻¹) =
      equiv.conj (representation element) := by
    ext vector
    simp [equiv, map_mul, LinearEquiv.conj_apply]
  simp only [integralValue, heq, LinearEquiv.charpoly_conj]

theorem value_conj (representation : Representation (splittingField d) G V)
    (element conjugator : G) :
    value d representation (conjugator * element * conjugator⁻¹) =
      value d representation element := by
  exact congrArg Subtype.val (integralValue_conj d representation element conjugator)

variable {W : Type w} [AddCommGroup W] [Module (splittingField d) W]
  [FiniteDimensional (splittingField d) W]

theorem integralValue_equiv
    {representation : Representation (splittingField d) G V}
    {other : Representation (splittingField d) G W}
    (equiv : representation.Equiv other) (element : G) :
    integralValue d representation element = integralValue d other element := by
  have heq := equiv.toLinearEquiv.charpoly_conj (representation element)
  rw [Representation.Equiv.conj_apply_self] at heq
  simp only [integralValue, heq]

theorem value_equiv
    {representation : Representation (splittingField d) G V}
    {other : Representation (splittingField d) G W}
    (equiv : representation.Equiv other) (element : G) :
    value d representation element = value d other element := by
  exact congrArg Subtype.val (integralValue_equiv d equiv element)

/-- Conjugacy classes containing an element of odd order. -/
@[expose] def TwoRegularClasses (G : Type u) [Group G] :=
  {conjugacyClass : ConjClasses G //
    ∃ element : G, Odd (orderOf element) ∧ ConjClasses.mk element = conjugacyClass}

/-- The two-regular conjugacy class of a specified odd-order element. -/
@[expose] def twoRegularClass (element : G) (hodd : Odd (orderOf element)) :
    TwoRegularClasses G := ⟨ConjClasses.mk element, element, hodd, rfl⟩

/-- Genuine Brauer character, defined only on two-regular conjugacy classes. -/
@[expose] def character (representation : Representation (splittingField d) G V) :
    TwoRegularClasses G → ℂ :=
  fun conjugacyClass => conjClassFunctionOfInvariant (value d representation)
    (value_conj d representation) conjugacyClass.val

@[simp] theorem character_apply (representation : Representation (splittingField d) G V)
    (element : G) (hodd : Odd (orderOf element)) :
    character d representation (twoRegularClass element hodd) =
      value d representation element := rfl

theorem character_equiv
    {representation : Representation (splittingField d) G V}
    {other : Representation (splittingField d) G W}
    (equiv : representation.Equiv other) :
    character d representation = character d other := by
  funext conjugacyClass
  obtain ⟨element, hodd, heq⟩ := conjugacyClass.property
  have hclass : conjugacyClass = twoRegularClass element hodd := Subtype.ext heq.symm
  rw [hclass, character_apply, character_apply, value_equiv d equiv]

end ModularBlock.BrauerCharacter
