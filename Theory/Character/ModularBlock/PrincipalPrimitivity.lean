module

public import Theory.Character.ModularBlock.ScalarNilpotence
public import Theory.Character.ModularBlock.CentralLift
public import Theory.Character.ModularBlock.FiniteFieldPrimitivity

/-!
# Primitivity of the reduced principal congruence selector

Lift a nonzero central idempotent factor of the reduced selector to a central
element over the cyclotomic localization. Its reduced irreducible scalars
are idempotent, vanish outside the principal congruence class, and agree
inside that class. They cannot all vanish: the DVR scalar-nilpotence theorem
would make a positive power of the nonzero idempotent zero. Hence the scalars
are one exactly on the principal block. Applying nilpotence to the difference
from the selector proves that difference zero, establishing primitivity.

Finite-field extension then proves primitivity of the compatible local
selector in the ambient residue field. Its known nonzero intersection with
the involution Brauer image gives the local factor identity.

Ported from the reduced-selector proof and final three conclusions of
`c3503435:glauberman_zStar/Submission/ZStar/BlockPrimitivity.lean`.
The later unused ambient-localization scalar replay is replaced by the
source's final finite-field extension route. All central-primitivity claims
use the shared predicate and the actual modular selector constructions.
-/

public section
noncomputable section
namespace ModularBlock.BlockPrimitivity
attribute [local instance] Fintype.ofFinite
open scoped BigOperators

theorem reducedPrincipalBlockElement_isCentrallyPrimitive
    {G : Type*} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G) :
    IsCentrallyPrimitive
      (BrauerBlockReduction.reducedPrincipalBlockElement d) := by
  classical
  let : d.primeIdeal.IsMaximal := d.primeIdeal_maximal
  let : Field (BrauerBlockReduction.principalResidueField d) :=
    Ideal.Quotient.field d.primeIdeal
  let R := Localization.AtPrime d.primeIdeal
  let q := BrauerBlockReduction.localizationToResidue d
  let eR : Subring.center (MonoidAlgebra R G) :=
    ⟨BlockOrthogonality.localizedPrincipalBlockElement d,
      BlockOrthogonality.localizedPrincipalBlockElement_mem_center d⟩
  let eK := BrauerBlockReduction.reducedPrincipalBlockElement d
  have hemap : MonoidAlgebra.mapRingHom G q eR.1 = eK := rfl
  have hecenter : eK ∈ Set.center
      (MonoidAlgebra (BrauerBlockReduction.principalResidueField d) G) :=
    BrauerBlockReduction.reducedPrincipalBlockElement_mem_center d
  have heidem : IsIdempotentElem eK :=
    BrauerBlockReduction.reducedPrincipalBlockElement_isIdempotent d
  have hene : eK ≠ 0 := BrauerBlockReduction.reducedPrincipalBlockElement_ne_zero d
  refine ⟨hecenter, heidem, hene, ?_⟩
  intro f hf hfid hfactor hfne
  have hqsurj : Function.Surjective q := by
    intro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨algebraMap (cyclotomicOrder d.eta) R a, ?_⟩
    exact BrauerBlockReduction.localizationToResidue_algebraMap d a
  obtain ⟨x, hxcenter, hxmap⟩ :=
    CentralLift.exists_monoidAlgebra_lift_mem_center q hqsurj f hf
  let xz : Subring.center (MonoidAlgebra R G) := ⟨x, hxcenter⟩
  have hfactorzero :
      MonoidAlgebra.mapRingHom G q ((xz * eR - xz).1) = 0 := by
    change MonoidAlgebra.mapRingHom G q (x *
        BlockOrthogonality.localizedPrincipalBlockElement d - x) = 0
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
      localizedCentralScalar_localizedPrincipalBlockElement] at hy
    simpa [scalar, hi] using hy
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
      exact (localizationToResidue_eq_zero_iff_not_isUnit d _).mp
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
        ((d.mem_block_iff i).mp hi)
        (BlockPreliminaries.sameTwoBlock_symm d.eta_spec d.primeIdeal
          ((d.mem_block_iff i₀).mp hi₀block))
    have hdiff :=
      CentralScalarCongruence.localizedCentralScalar_sub_mem_maximalIdeal
        d.eta_spec d.primeIdeal (d.chi i) (d.chi i₀)
        (d.complete.1 i) (d.complete.1 i₀) hsame xz
    have hnonunit : ¬ IsUnit (scalar i - scalar i₀) := by
      apply mem_nonunits_iff.mp
      exact (IsLocalRing.mem_maximalIdeal _).mp hdiff
    have hzero :=
      (localizationToResidue_eq_zero_iff_not_isUnit d _).2 hnonunit
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
    apply (localizationToResidue_eq_zero_iff_not_isUnit d _).mp
    rw [localizedCentralScalar_sub,
      localizedCentralScalar_localizedPrincipalBlockElement]
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

/-- The compatible local principal selector stays primitive in the ambient residue field. -/
theorem localPrincipalBlockElementInAmbientResidue_isCentrallyPrimitive
    {G : Type*} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
    (H : Subgroup G) :
    IsCentrallyPrimitive
      (CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d H) := by
  exact FiniteFieldPrimitivity.localPrincipalBlockElementInAmbientResidue_isCentrallyPrimitive_of_source
    d H (reducedPrincipalBlockElement_isCentrallyPrimitive
      (CompatibleBrauerBlock.localData d H))

/-- Central primitivity of the reduced compatible local principal selector
upgrades its known nonzero intersection with the ambient Brauer selector to
the exact factor identity.  This is the conclusion supplied by primitivity;
it does not assert that the Brauer selector has no other local factors. -/

theorem localPrincipalBlockElement_mul_involutionBrauer_eq_self_of_primitive
    {G : Type*} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
    (z : G) (hz : z * z = 1)
    (hprimitive : IsCentrallyPrimitive
      (CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
        (Subgroup.centralizer ({z} : Set G)))) :
    CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
          (Subgroup.centralizer ({z} : Set G)) *
        BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z =
      CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
        (Subgroup.centralizer ({z} : Set G)) := by
  let eLocal :=
    CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
      (Subgroup.centralizer ({z} : Set G))
  let eBrauer := BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z
  obtain ⟨hcenter, hidem, hne⟩ :=
    CompatibleBrauerBlock.localPrincipalBlockElement_mul_involutionBrauer_isCentralIdempotent
      d z hz
  have hfactor : (eLocal * eBrauer) * eLocal = eLocal * eBrauer := by
    have heLocal := hprimitive.2.1
    have heLocalCenter := hprimitive.1
    have heBrauerCenter :=
      BrauerBlockReduction.involutionBrauerPrincipalBlockElement_mem_center d z
    have hcomm : eBrauer * eLocal = eLocal * eBrauer :=
      (Semigroup.mem_center_iff.mp heBrauerCenter eLocal).symm
    calc
      (eLocal * eBrauer) * eLocal = eLocal * (eBrauer * eLocal) :=
        mul_assoc _ _ _
      _ = eLocal * (eLocal * eBrauer) := by rw [hcomm]
      _ = (eLocal * eLocal) * eBrauer := (mul_assoc _ _ _).symm
      _ = eLocal * eBrauer := by rw [heLocal.eq]
  exact hprimitive.2.2.2 (eLocal * eBrauer) hcenter hidem hfactor hne

/-- The compatible local principal selector is a factor of the involution
Brauer image of the ambient principal selector. -/

theorem localPrincipalBlockElement_mul_involutionBrauer_eq_self
    {G : Type*} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
    (z : G) (hz : z * z = 1) :
    CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
          (Subgroup.centralizer ({z} : Set G)) *
        BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z =
      CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
        (Subgroup.centralizer ({z} : Set G)) := by
  exact localPrincipalBlockElement_mul_involutionBrauer_eq_self_of_primitive
    d z hz
    (localPrincipalBlockElementInAmbientResidue_isCentrallyPrimitive d
      (Subgroup.centralizer ({z} : Set G)))


end ModularBlock.BlockPrimitivity

