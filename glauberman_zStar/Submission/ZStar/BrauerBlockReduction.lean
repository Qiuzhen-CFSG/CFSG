import Submission.ZStar.BlockOrthogonality
import Submission.ZStar.BrauerMapScratch
import Mathlib.Algebra.CharP.Two

/-!
# Reduction of the principal block idempotent and its involution Brauer image

This file connects the localized characteristic-zero principal-block element
constructed in `BlockOrthogonality` with the characteristic-two Brauer
restriction constructed in `BrauerMapScratch`.

No block-correspondence statement is used here.  The endpoint is an explicit
central idempotent in the group algebra of the involution centralizer.  The
remaining Nagao/Brauer step is to identify the local block components of this
idempotent and the section module it selects.
-/

noncomputable section

namespace Submission.ZStar

namespace BrauerBlockReduction

open PrincipalBlockConstruction

universe u

attribute [local instance] Fintype.ofFinite

variable {G : Type u} [Group G] [Finite G]

private instance principalPrimeIdeal_isPrime
    (d : PrincipalCongruenceBlockData G) : d.primeIdeal.IsPrime :=
  d.primeIdeal_maximal.isPrime

private instance principalPrimeIdeal_isMaximal
    (d : PrincipalCongruenceBlockData G) : d.primeIdeal.IsMaximal :=
  d.primeIdeal_maximal

/-- The residue field of the cyclotomic prime used to define the ambient
principal congruence block. -/
abbrev principalResidueField (d : PrincipalCongruenceBlockData G) :=
  (Representation.cyclotomicOrder d.eta) ⧸ d.primeIdeal

/-- Reduction from the localized cyclotomic order to its residue field. -/
noncomputable def localizationToResidue
    (d : PrincipalCongruenceBlockData G) :
    Localization.AtPrime d.primeIdeal →+* principalResidueField d := by
  letI : Field (principalResidueField d) :=
    Ideal.Quotient.field d.primeIdeal
  let A := Representation.cyclotomicOrder d.eta
  let q : A →+* principalResidueField d := Ideal.Quotient.mk d.primeIdeal
  exact IsLocalization.lift
    (M := d.primeIdeal.primeCompl)
    (S := Localization.AtPrime d.primeIdeal)
    (g := q) (by
      intro y
      apply isUnit_iff_ne_zero.mpr
      exact Ideal.Quotient.eq_zero_iff_mem.not.mpr y.2)

theorem localizationToResidue_algebraMap
    (d : PrincipalCongruenceBlockData G)
    (a : Representation.cyclotomicOrder d.eta) :
    localizationToResidue d
        (algebraMap _ (Localization.AtPrime d.primeIdeal) a) =
      Ideal.Quotient.mk d.primeIdeal a := by
  apply IsLocalization.lift_eq

instance principalResidueField_charTwo
    (d : PrincipalCongruenceBlockData G) :
    CharP (principalResidueField d) 2 :=
  CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero (by
    change Ideal.Quotient.mk d.primeIdeal
      (2 : Representation.cyclotomicOrder d.eta) = 0
    exact d.two_eq_zero_mod_primeIdeal)

/-- Coefficientwise reduction of the ambient localized group algebra. -/
noncomputable def reduceLocalizedGroupAlgebra
    (d : PrincipalCongruenceBlockData G) :
    MonoidAlgebra (Localization.AtPrime d.primeIdeal) G →+*
      MonoidAlgebra (principalResidueField d) G :=
  MonoidAlgebra.mapRingHom G (localizationToResidue d)

@[simp] theorem reduceLocalizedGroupAlgebra_apply
    (d : PrincipalCongruenceBlockData G)
    (a : MonoidAlgebra (Localization.AtPrime d.primeIdeal) G) (g : G) :
    reduceLocalizedGroupAlgebra d a g = localizationToResidue d (a g) := by
  exact MonoidAlgebra.mapRingHom_apply _ _ _

/-- Mapping coefficients along a commutative-ring homomorphism preserves
centrality of group-algebra elements. -/
private theorem mapRingHom_mem_center
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (e : MonoidAlgebra R G)
    (he : e ∈ Set.center (MonoidAlgebra R G)) :
    MonoidAlgebra.mapRingHom G f e ∈
      Set.center (MonoidAlgebra S G) := by
  apply (Semigroup.mem_center_iff).2
  intro a
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [add_mul, mul_add, hx, hy]
  | single g r =>
      have hcomm := Semigroup.mem_center_iff.mp he
        (MonoidAlgebra.single g (1 : R))
      have hmap := congrArg (MonoidAlgebra.mapRingHom G f) hcomm
      have hcommOne :
          (MonoidAlgebra.single g (1 : S)) *
              MonoidAlgebra.mapRingHom G f e =
            MonoidAlgebra.mapRingHom G f e *
              MonoidAlgebra.single g (1 : S) := by
        simpa using hmap
      rw [show (MonoidAlgebra.single g r : MonoidAlgebra S G) =
          r • MonoidAlgebra.single g 1 by simp]
      simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
      exact congrArg (fun x : MonoidAlgebra S G => r • x) hcommOne

/-- Restricting the coefficients of a central group-algebra element to an
element centralizer remains central in the centralizer group algebra. -/
theorem centralizerRestriction_mem_center
    {R : Type*} [CommRing R] (z : G) (e : MonoidAlgebra R G)
    (he : e ∈ Set.center (MonoidAlgebra R G)) :
    BrauerMapScratch.centralizerRestriction R z e ∈
      Set.center
        (MonoidAlgebra R (Subgroup.centralizer ({z} : Set G))) := by
  apply (Semigroup.mem_center_iff).2
  intro a
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [add_mul, mul_add, hx, hy]
  | single g r =>
      ext x
      have hcoeff :=
        CentralIdempotentSupport.coeff_conj_eq_of_mem_center e he
          ((g : G)⁻¹) ((x : G) * (g : G)⁻¹)
      simp only [MonoidAlgebra.single_mul_apply,
        MonoidAlgebra.mul_single_apply,
        BrauerMapScratch.centralizerRestriction_apply]
      change r * e ((g : G)⁻¹ * (x : G)) =
        e ((x : G) * (g : G)⁻¹) * r
      have hconj :
          (g : G)⁻¹ * ((x : G) * (g : G)⁻¹) * ((g : G)⁻¹)⁻¹ =
            (g : G)⁻¹ * (x : G) := by group
      rw [hconj] at hcoeff
      rw [hcoeff, mul_comm]

/-- The ambient principal-block idempotent after reduction modulo the chosen
prime above `2`. -/
noncomputable def reducedPrincipalBlockElement
    (d : PrincipalCongruenceBlockData G) :
    MonoidAlgebra (principalResidueField d) G :=
  reduceLocalizedGroupAlgebra d
    (BlockOrthogonality.localizedPrincipalBlockElement d)

theorem reducedPrincipalBlockElement_mem_center
    (d : PrincipalCongruenceBlockData G) :
    reducedPrincipalBlockElement d ∈
      Set.center (MonoidAlgebra (principalResidueField d) G) := by
  exact mapRingHom_mem_center (localizationToResidue d)
    (BlockOrthogonality.localizedPrincipalBlockElement d)
    (BlockOrthogonality.localizedPrincipalBlockElement_mem_center d)

theorem reducedPrincipalBlockElement_isIdempotent
    (d : PrincipalCongruenceBlockData G) :
    IsIdempotentElem (reducedPrincipalBlockElement d) := by
  change reduceLocalizedGroupAlgebra d
      (BlockOrthogonality.localizedPrincipalBlockElement d) *
      reduceLocalizedGroupAlgebra d
        (BlockOrthogonality.localizedPrincipalBlockElement d) =
    reduceLocalizedGroupAlgebra d
      (BlockOrthogonality.localizedPrincipalBlockElement d)
  rw [← map_mul]
  exact congrArg (reduceLocalizedGroupAlgebra d)
    (BlockOrthogonality.localizedPrincipalBlockElement_isIdempotent d)

/-- The characteristic-two Brauer image of the ambient principal-block
idempotent at an involution. -/
noncomputable def involutionBrauerPrincipalBlockElement
    (d : PrincipalCongruenceBlockData G) (z : G) :
    MonoidAlgebra (principalResidueField d)
      (Subgroup.centralizer ({z} : Set G)) :=
  BrauerMapScratch.centralizerRestriction (principalResidueField d) z
    (reducedPrincipalBlockElement d)

/-- Reduction modulo the ambient prime and involution Brauer restriction
commute on the localized principal-block idempotent. -/
theorem involutionBrauerPrincipalBlockElement_eq_map_restriction
    (d : PrincipalCongruenceBlockData G) (z : G) :
    involutionBrauerPrincipalBlockElement d z =
      MonoidAlgebra.mapRingHom
        (Subgroup.centralizer ({z} : Set G)) (localizationToResidue d)
        (BrauerMapScratch.centralizerRestriction
          (Localization.AtPrime d.primeIdeal) z
          (BlockOrthogonality.localizedPrincipalBlockElement d)) := by
  exact BrauerMapScratch.centralizerRestriction_mapRingHom
    (localizationToResidue d) z
      (BlockOrthogonality.localizedPrincipalBlockElement d)

theorem involutionBrauerPrincipalBlockElement_isIdempotent
    (d : PrincipalCongruenceBlockData G) (z : G)
    (hz : z * z = 1) :
    IsIdempotentElem (involutionBrauerPrincipalBlockElement d z) := by
  exact BrauerMapScratch.centralizerRestriction_isIdempotent_of_mem_center
    z hz (reducedPrincipalBlockElement d)
      (reducedPrincipalBlockElement_mem_center d)
      (reducedPrincipalBlockElement_isIdempotent d)

theorem involutionBrauerPrincipalBlockElement_mem_center
    (d : PrincipalCongruenceBlockData G) (z : G) :
    involutionBrauerPrincipalBlockElement d z ∈
      Set.center
        (MonoidAlgebra (principalResidueField d)
          (Subgroup.centralizer ({z} : Set G))) := by
  exact centralizerRestriction_mem_center z
    (reducedPrincipalBlockElement d)
    (reducedPrincipalBlockElement_mem_center d)

end BrauerBlockReduction

end Submission.ZStar
