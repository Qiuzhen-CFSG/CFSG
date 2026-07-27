import Submission.ZStar.CompatibleBrauerBlock

/-!
# The exact obstruction to principal Brauer equality

The ambient Brauer selector and the compatible local principal selector both
come from explicit elements over the same localized cyclotomic order.  Their
difference therefore has a canonical lift.  This file proves that the desired
principal Brauer equality is equivalent to every coefficient of that lift
lying in the maximal ideal.

This isolates the remaining Brauer-correspondence input without assuming the
equality, local support, or projectivity.
-/

noncomputable section

namespace Submission.ZStar

namespace PrincipalBrauerEquality

open PrincipalBlockConstruction

universe u

attribute [local instance] Fintype.ofFinite

private instance principalPrime_isPrime
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) : d.primeIdeal.IsPrime :=
  d.primeIdeal_maximal.isPrime

private instance principalPrime_isMaximal
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) : d.primeIdeal.IsMaximal :=
  d.primeIdeal_maximal

/-- The coefficientwise restriction of the localized ambient principal-block
selector to the involution centralizer.  Its reduction is the ambient Brauer
selector. -/
noncomputable def ambientPrincipalBrauerLift
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G) :
    MonoidAlgebra (Localization.AtPrime d.primeIdeal)
      (Subgroup.centralizer ({z} : Set G)) :=
  BrauerMapScratch.centralizerRestriction
    (Localization.AtPrime d.primeIdeal) z
    (BlockOrthogonality.localizedPrincipalBlockElement d)

theorem ambientPrincipalBrauerLift_mem_center
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G) :
    ambientPrincipalBrauerLift d z ∈
      Set.center
        (MonoidAlgebra (Localization.AtPrime d.primeIdeal)
          (Subgroup.centralizer ({z} : Set G))) := by
  exact BrauerBlockReduction.centralizerRestriction_mem_center z
    (BlockOrthogonality.localizedPrincipalBlockElement d)
    (BlockOrthogonality.localizedPrincipalBlockElement_mem_center d)

/-- Reduction of the common-localization lift is exactly the ambient Brauer
selector. -/
theorem ambientPrincipalBrauerLift_reduce
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G) :
    MonoidAlgebra.mapRingHom
        (Subgroup.centralizer ({z} : Set G))
        (BrauerBlockReduction.localizationToResidue d)
        (ambientPrincipalBrauerLift d z) =
      BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z := by
  exact
    (BrauerBlockReduction.involutionBrauerPrincipalBlockElement_eq_map_restriction
      d z).symm

/-- The canonical localized lift of `e_Brauer - e_local`. -/
noncomputable def principalBrauerDifferenceLift
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G) :
    MonoidAlgebra (Localization.AtPrime d.primeIdeal)
      (Subgroup.centralizer ({z} : Set G)) :=
  ambientPrincipalBrauerLift d z -
    CompatibleBrauerBlock.localPrincipalBlockElementInAmbientLocalization d
      (Subgroup.centralizer ({z} : Set G))

theorem principalBrauerDifferenceLift_mem_center
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G) :
    principalBrauerDifferenceLift d z ∈
      Set.center
        (MonoidAlgebra (Localization.AtPrime d.primeIdeal)
          (Subgroup.centralizer ({z} : Set G))) := by
  apply (Semigroup.mem_center_iff).2
  intro a
  have hambient := Semigroup.mem_center_iff.mp
    (ambientPrincipalBrauerLift_mem_center d z) a
  have hlocal := Semigroup.mem_center_iff.mp
    (CompatibleBrauerBlock.localPrincipalBlockElementInAmbientLocalization_mem_center
      d (Subgroup.centralizer ({z} : Set G))) a
  change a * (ambientPrincipalBrauerLift d z -
      CompatibleBrauerBlock.localPrincipalBlockElementInAmbientLocalization d
        (Subgroup.centralizer ({z} : Set G))) =
    (ambientPrincipalBrauerLift d z -
      CompatibleBrauerBlock.localPrincipalBlockElementInAmbientLocalization d
        (Subgroup.centralizer ({z} : Set G))) * a
  calc
    a * (ambientPrincipalBrauerLift d z -
        CompatibleBrauerBlock.localPrincipalBlockElementInAmbientLocalization d
          (Subgroup.centralizer ({z} : Set G))) =
      a * ambientPrincipalBrauerLift d z -
        a * CompatibleBrauerBlock.localPrincipalBlockElementInAmbientLocalization d
          (Subgroup.centralizer ({z} : Set G)) :=
      mul_sub a (ambientPrincipalBrauerLift d z)
        (CompatibleBrauerBlock.localPrincipalBlockElementInAmbientLocalization d
          (Subgroup.centralizer ({z} : Set G)))
    _ = ambientPrincipalBrauerLift d z * a -
        CompatibleBrauerBlock.localPrincipalBlockElementInAmbientLocalization d
          (Subgroup.centralizer ({z} : Set G)) * a := by rw [hambient, hlocal]
    _ = (ambientPrincipalBrauerLift d z -
        CompatibleBrauerBlock.localPrincipalBlockElementInAmbientLocalization d
          (Subgroup.centralizer ({z} : Set G))) * a :=
      (sub_mul (ambientPrincipalBrauerLift d z)
        (CompatibleBrauerBlock.localPrincipalBlockElementInAmbientLocalization d
          (Subgroup.centralizer ({z} : Set G))) a).symm

/-- The lifted obstruction reduces to the literal difference between the two
selectors. -/
theorem principalBrauerDifferenceLift_reduce
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G) :
    MonoidAlgebra.mapRingHom
        (Subgroup.centralizer ({z} : Set G))
        (BrauerBlockReduction.localizationToResidue d)
        (principalBrauerDifferenceLift d z) =
      BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z -
        CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
          (Subgroup.centralizer ({z} : Set G)) := by
  rw [principalBrauerDifferenceLift, map_sub,
    ambientPrincipalBrauerLift_reduce,
    CompatibleBrauerBlock.localPrincipalBlockElementInAmbientLocalization_reduce]

@[simp] theorem localizationToResidue_principalBrauerDifferenceLift_apply
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G)
    (x : Subgroup.centralizer ({z} : Set G)) :
    BrauerBlockReduction.localizationToResidue d
        (principalBrauerDifferenceLift d z x) =
      (BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z -
        CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
          (Subgroup.centralizer ({z} : Set G))) x := by
  have h := congrArg
    (fun a : MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
        (Subgroup.centralizer ({z} : Set G)) => a x)
    (principalBrauerDifferenceLift_reduce d z)
  simpa only [MonoidAlgebra.mapRingHom_apply] using h

private theorem localizationToResidue_surjective
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) :
    Function.Surjective (BrauerBlockReduction.localizationToResidue d) := by
  intro y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨algebraMap (Representation.cyclotomicOrder d.eta)
    (Localization.AtPrime d.primeIdeal) a, ?_⟩
  exact BrauerBlockReduction.localizationToResidue_algebraMap d a

/-- Reduction to the residue field vanishes exactly on the maximal ideal of
the localized cyclotomic order. -/
theorem localizationToResidue_eq_zero_iff_mem_maximalIdeal
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G)
    (a : Localization.AtPrime d.primeIdeal) :
    BrauerBlockReduction.localizationToResidue d a = 0 ↔
      a ∈ IsLocalRing.maximalIdeal (Localization.AtPrime d.primeIdeal) := by
  letI : Field (BrauerBlockReduction.principalResidueField d) :=
    Ideal.Quotient.field d.primeIdeal
  have hkerMaximal :
      (RingHom.ker (BrauerBlockReduction.localizationToResidue d)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective
      (BrauerBlockReduction.localizationToResidue d)
      (localizationToResidue_surjective d)
  have hker :
      RingHom.ker (BrauerBlockReduction.localizationToResidue d) =
        IsLocalRing.maximalIdeal (Localization.AtPrime d.primeIdeal) :=
    IsLocalRing.eq_maximalIdeal hkerMaximal
  rw [← RingHom.mem_ker, hker]

/-- The concrete principal Brauer equality is exactly the assertion that all
coefficients of the canonical lifted difference lie in the local maximal
ideal.  This is the minimal coefficientwise form of the missing Third Main
Theorem input. -/
theorem involutionBrauerPrincipalBlockElement_eq_local_iff
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G) :
    BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z =
        CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
          (Subgroup.centralizer ({z} : Set G)) ↔
      ∀ x : Subgroup.centralizer ({z} : Set G),
        principalBrauerDifferenceLift d z x ∈
          IsLocalRing.maximalIdeal (Localization.AtPrime d.primeIdeal) := by
  constructor
  · intro heq x
    apply (localizationToResidue_eq_zero_iff_mem_maximalIdeal d _).mp
    rw [localizationToResidue_principalBrauerDifferenceLift_apply, heq,
      sub_self]
    rfl
  · intro hcoeff
    apply sub_eq_zero.mp
    rw [← principalBrauerDifferenceLift_reduce]
    ext x
    rw [MonoidAlgebra.mapRingHom_apply]
    exact (localizationToResidue_eq_zero_iff_mem_maximalIdeal d _).mpr
      (hcoeff x)

/-- Prop-packaged orientation of the same exact obstruction theorem. -/
theorem involutionPrincipalBrauerEquality_iff
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G) :
    CompatibleBrauerBlock.InvolutionPrincipalBrauerEquality d z ↔
      ∀ x : Subgroup.centralizer ({z} : Set G),
        principalBrauerDifferenceLift d z x ∈
          IsLocalRing.maximalIdeal (Localization.AtPrime d.primeIdeal) := by
  rw [CompatibleBrauerBlock.InvolutionPrincipalBrauerEquality, eq_comm]
  exact involutionBrauerPrincipalBlockElement_eq_local_iff d z

end PrincipalBrauerEquality

end Submission.ZStar
