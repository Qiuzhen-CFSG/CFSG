module

public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.PrincipalBlock.Nilpotence
public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.PrincipalBlock.SelectorScalar

/-!
# Primitivity over the actual cyclotomic residue field

Lift a central idempotent factor coefficientwise on conjugacy classes. Its
ordinary scalars vanish outside the selected block and agree inside it.
Scalar nilpotence forces a nonzero scalar, so they are exactly the block
indicator. Applying nilpotence to the complementary idempotent proves it zero.

Adapted from `ModularBlock/PrincipalPrimitivity.lean`, originally ported from
`public/lean-eval/glauberman_zStar` at c3503435. This proof uses arbitrary
prime data, not the characteristic-two principal data. Source: Feit III.8--9.
-/

public section
noncomputable section
namespace Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.PrincipalBlock
open ModularBlock ModularBlock.PrimeBlockConstruction
open ModularBlock.PrincipalBlockConstruction ModularBlock.BlockOrthogonality
attribute [local instance] Fintype.ofFinite
open scoped BigOperators
variable {p : ℕ}
private theorem localizationToResidue_localizedCentralScalar_eq_zero_of_map_eq_zero
    {G : Type*} [Group G] [Finite G]
    (d : PrimeCongruenceBlockData p G)
    (i : d.I)
    (z : Subring.center
      (MonoidAlgebra (Localization.AtPrime d.primeIdeal) G))
    (hz : MonoidAlgebra.mapRingHom G
        (toResidue d) z.1 = 0) :
    toResidue d
        (CentralScalarCongruence.localizedCentralScalar d.eta_spec
          d.primeIdeal (d.chi i) (d.complete.1 i) z) = 0 := by
  classical
  rw [CentralScalarCongruence.localizedCentralScalar, map_sum]
  apply Finset.sum_eq_zero
  intro c _hc
  rw [map_mul]
  have hc := congrArg
    (fun a : MonoidAlgebra
        (residueField d) G =>
      a.coeff (CentralScalarCongruence.classRepresentative c)) hz
  change toResidue d
      (z.1.coeff (CentralScalarCongruence.classRepresentative c)) = 0 at hc
  have hcoeff : toResidue d
      (CentralScalarCongruence.centralClassCoefficient z c) = 0 := by
    exact hc
  rw [hcoeff, zero_mul]


variable [Fact p.Prime]

theorem reducedPrincipalBlockElement_isCentrallyPrimitive
    {G : Type*} [Group G] [Finite G]
    (d : PrimeCongruenceBlockData p G) :
    IsCentrallyPrimitive
      (reducedPrincipal d (toResidue d)) := by
  classical
  let : d.primeIdeal.IsMaximal := d.primeIdeal_maximal
  let : Field (residueField d) :=
    Ideal.Quotient.field d.primeIdeal
  let R := Localization.AtPrime d.primeIdeal
  let q := toResidue d
  let eR : Subring.center (MonoidAlgebra R G) :=
    ⟨PrimeSelector.localizedBlockElement d d.principal,
      PrimeSelector.localizedBlockElement_mem_center d d.principal⟩
  let eK := reducedPrincipal d (toResidue d)
  have hemap : MonoidAlgebra.mapRingHom G q eR.1 = eK := rfl
  have hecenter : eK ∈ Set.center
      (MonoidAlgebra (residueField d) G) :=
    reducedPrincipal_mem_center d (toResidue d)
  have heidem : IsIdempotentElem eK :=
    reducedPrincipal_isIdempotent d (toResidue d)
  have hene : eK ≠ 0 := by
    intro hzero
    have h := reducedPrincipal_augmentation d (toResidue d)
    change groupAlgebraAugmentation (residueField d) G eK = 1 at h
    rw [hzero, map_zero] at h
    exact zero_ne_one h
  refine ⟨hecenter, heidem, hene, ?_⟩
  intro f hf hfid hfactor hfne
  have hqsurj : Function.Surjective q := by
    intro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨algebraMap (cyclotomicOrder d.eta) R a, ?_⟩
    exact toResidue_algebraMap d a
  obtain ⟨x, hxcenter, hxmap⟩ :=
    CentralLift.exists_monoidAlgebra_lift_mem_center q hqsurj f hf
  let xz : Subring.center (MonoidAlgebra R G) := ⟨x, hxcenter⟩
  have hfactorzero :
      MonoidAlgebra.mapRingHom G q ((xz * eR - xz).1) = 0 := by
    change MonoidAlgebra.mapRingHom G q (x *
        PrimeSelector.localizedBlockElement d d.principal - x) = 0
    rw [map_sub, map_mul, hxmap]
    change f * eK - f = 0
    rw [hfactor, sub_self]
  have hidemzero :
      MonoidAlgebra.mapRingHom G q ((xz * xz - xz).1) = 0 := by
    change MonoidAlgebra.mapRingHom G q (x * x - x) = 0
    rw [map_sub, map_mul, hxmap, hfid, sub_self]
  let scalar : d.I → R := fun i =>
    CentralScalarCongruence.localizedCentralScalar d.eta_spec
      d.primeIdeal (d.chi i) (d.complete.1 i) xz
  have houtside : ∀ i : d.I, i ∉ d.block → q (scalar i) = 0 := by
    intro i hi
    have hy :=
      localizationToResidue_localizedCentralScalar_eq_zero_of_map_eq_zero
        d i (xz * eR - xz) hfactorzero
    rw [localizedCentralScalar_sub, localizedCentralScalar_mul,
      localizedCentralScalar_selector] at hy
    have hi' : i ∉ d.blockOf d.principal := hi
    simpa [scalar, hi'] using hy
  have hidemScalar : ∀ i : d.I,
      q (scalar i) * q (scalar i) = q (scalar i) := by
    intro i
    have hy :=
      localizationToResidue_localizedCentralScalar_eq_zero_of_map_eq_zero
        d i (xz * xz - xz) hidemzero
    rw [localizedCentralScalar_sub, localizedCentralScalar_mul] at hy
    simpa [scalar, map_sub, map_mul, sub_eq_zero] using hy
  have hexScalar : ∃ i : d.I, q (scalar i) ≠ 0 := by
    by_contra hnone
    push Not at hnone
    have hnonunit : ∀ i : d.I, ¬ IsUnit (scalar i) := by
      intro i
      exact (toResidue_eq_zero_iff d _).mp
        (hnone i)
    obtain ⟨N, hN, hpow⟩ :=
      exists_pow_reduce_eq_zero_of_all_localizedCentralScalar_nonunit
        d xz hnonunit
    have hfzero : f = 0 := by
      calc
        f = f ^ N := (hfid.pow_eq (Nat.ne_of_gt hN)).symm
        _ = (MonoidAlgebra.mapRingHom G q x) ^ N := by rw [hxmap]
        _ = MonoidAlgebra.mapRingHom G q (x ^ N) := by rw [map_pow]
        _ = MonoidAlgebra.mapRingHom G q (xz.1 ^ N) := rfl
        _ = 0 := by simpa using hpow
    exact hfne hfzero
  obtain ⟨i₀, hi₀ne⟩ := hexScalar
  have hi₀block : i₀ ∈ d.block := by
    by_contra hi
    exact hi₀ne (houtside i₀ hi)
  have hqScalar₀ : q (scalar i₀) = 1 := by
    have hpoly := hidemScalar i₀
    have hprod : q (scalar i₀) * (q (scalar i₀) - 1) = 0 := by
      rw [mul_sub, mul_one, hpoly, sub_self]
    rcases mul_eq_zero.mp hprod with hzero | hone
    · exact (hi₀ne hzero).elim
    · exact sub_eq_zero.mp hone
  have hscalar_eq (i : d.I) (hi : i ∈ d.block) :
      q (scalar i) = q (scalar i₀) := by
    have hsame : BlockPreliminaries.SameTwoBlock d.eta_spec d.primeIdeal
        (d.chi i) (d.chi i₀) (d.complete.1 i) (d.complete.1 i₀) := by
      exact BlockPreliminaries.sameTwoBlock_trans d.eta_spec d.primeIdeal
        ((d.mem_blockOf_iff i d.principal).mp hi)
        (BlockPreliminaries.sameTwoBlock_symm d.eta_spec d.primeIdeal
          ((d.mem_blockOf_iff i₀ d.principal).mp hi₀block))
    have hdiff :=
      CentralScalarCongruence.localizedCentralScalar_sub_mem_maximalIdeal
        d.eta_spec d.primeIdeal (d.chi i) (d.chi i₀)
        (d.complete.1 i) (d.complete.1 i₀) hsame xz
    have hnonunit : ¬ IsUnit (scalar i - scalar i₀) := by
      apply mem_nonunits_iff.mp
      exact (IsLocalRing.mem_maximalIdeal _).mp hdiff
    have hzero :=
      (toResidue_eq_zero_iff d _).2 hnonunit
    have hzero' : q (scalar i) - q (scalar i₀) = 0 := by
      simpa [scalar, map_sub] using hzero
    exact sub_eq_zero.mp hzero'
  have hinside : ∀ i : d.I, i ∈ d.block → q (scalar i) = 1 := by
    intro i hi
    rw [hscalar_eq i hi, hqScalar₀]
  let dz : Subring.center (MonoidAlgebra R G) := eR - xz
  have hdzzero : MonoidAlgebra.mapRingHom G q dz.1 = eK - f := by
    change MonoidAlgebra.mapRingHom G q (eR.1 - x) = _
    rw [map_sub, hemap, hxmap]
  have hdzNonunit : ∀ i : d.I,
      ¬ IsUnit
        (CentralScalarCongruence.localizedCentralScalar d.eta_spec
          d.primeIdeal (d.chi i) (d.complete.1 i) dz) := by
    intro i
    apply (toResidue_eq_zero_iff d _).mp
    rw [localizedCentralScalar_sub,
      localizedCentralScalar_selector]
    change q ((if i ∈ d.block then (1 : R) else 0) - scalar i) = 0
    rw [map_sub]
    by_cases hi : i ∈ d.block
    · rw [if_pos hi, map_one, hinside i hi, sub_self]
    · rw [if_neg hi, map_zero, houtside i hi, sub_zero]
  obtain ⟨N, hN, hpow⟩ :=
    exists_pow_reduce_eq_zero_of_all_localizedCentralScalar_nonunit
      d dz hdzNonunit
  have hefactor : eK * f = f := by
    calc
      eK * f = f * eK := (Semigroup.mem_center_iff.mp hecenter f).symm
      _ = f := hfactor
  have hsubidem : IsIdempotentElem (eK - f) :=
    IsIdempotentElem.sub hfid heidem hfactor hefactor
  have hsubpow : (eK - f) ^ N = eK - f :=
    hsubidem.pow_eq (Nat.ne_of_gt hN)
  have hsubzero : eK - f = 0 := by
    have hpow' : (eK - f) ^ N = 0 := by
      calc
        (eK - f) ^ N =
            MonoidAlgebra.mapRingHom G q (dz.1 ^ N) := by
              rw [map_pow, hdzzero]
        _ = 0 := by simpa using hpow
    exact hsubpow.symm.trans hpow'
  exact (sub_eq_zero.mp hsubzero).symm


end Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.PrincipalBlock
