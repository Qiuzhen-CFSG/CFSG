module

public import Theory.Character.ModularBlock.PrincipalElement
public import Theory.Character.ModularBlock.BrauerMap
public import Mathlib.Algebra.CharP.Two

/-!
# Reduction of the principal block idempotent and its involution Brauer image

This file connects the localized characteristic-zero principal-block element
constructed in `PrincipalElement` with the characteristic-two Brauer
restriction constructed in `BrauerMap`.

No block-correspondence statement is used here.  The endpoint is an explicit
central idempotent in the group algebra of the involution centralizer.  The
remaining Nagao/Brauer step is to identify the local block components of this
idempotent and the section module it selects.

The residue map extends from the cyclotomic order to its localization because
all denominators lie outside the prime. Mapping coefficients preserves
centrality and idempotence. Augmentation commutes with this map and is one
on the principal selector, proving that its reduction is nonzero. In
characteristic two the involution Brauer restriction preserves both these
properties and the augmentation.

Ported from `public/lean-eval/glauberman_zStar`,
`Submission/ZStar/BrauerBlockReduction.lean` and `AugmentationScratch.lean`
(revision `c3503435`). The existing global group-algebra augmentation API is
used throughout. The explicit residue and reduction maps are exposed because
subsequent compatibility arguments compare their coefficient formulas.
-/

public section

noncomputable section

namespace ModularBlock

namespace BrauerBlockReduction

open PrincipalBlockConstruction

universe u

attribute [local instance] Fintype.ofFinite

variable {G : Type u} [Group G] [Finite G]

instance principalPrimeIdeal_isMaximal
    (d : PrincipalCongruenceBlockData G) : d.primeIdeal.IsMaximal :=
  d.primeIdeal_maximal

/-- The residue field of the cyclotomic prime used to define the ambient
principal congruence block. -/
abbrev principalResidueField (d : PrincipalCongruenceBlockData G) :=
  (cyclotomicOrder d.eta) ⧸ d.primeIdeal

/-- Reduction from the localized cyclotomic order to its residue field. -/
@[expose] noncomputable def localizationToResidue
    (d : PrincipalCongruenceBlockData G) :
    Localization.AtPrime d.primeIdeal →+* principalResidueField d := by
  let : Field (principalResidueField d) :=
    Ideal.Quotient.field d.primeIdeal
  let A := cyclotomicOrder d.eta
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
    (a : cyclotomicOrder d.eta) :
    localizationToResidue d
        (algebraMap _ (Localization.AtPrime d.primeIdeal) a) =
      Ideal.Quotient.mk d.primeIdeal a := by
  apply IsLocalization.lift_eq

instance principalResidueField_charTwo
    (d : PrincipalCongruenceBlockData G) :
    CharP (principalResidueField d) 2 :=
  CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero (by
    change Ideal.Quotient.mk d.primeIdeal
      (2 : cyclotomicOrder d.eta) = 0
    exact d.two_eq_zero_mod_primeIdeal)

/-- Coefficientwise reduction of the ambient localized group algebra. -/
@[expose] noncomputable def reduceLocalizedGroupAlgebra
    (d : PrincipalCongruenceBlockData G) :
    MonoidAlgebra (Localization.AtPrime d.primeIdeal) G →+*
      MonoidAlgebra (principalResidueField d) G :=
  MonoidAlgebra.mapRingHom G (localizationToResidue d)

@[simp] theorem reduceLocalizedGroupAlgebra_apply
    (d : PrincipalCongruenceBlockData G)
    (a : MonoidAlgebra (Localization.AtPrime d.primeIdeal) G) (g : G) :
    (reduceLocalizedGroupAlgebra d a).coeff g = localizationToResidue d (a.coeff g) := by
  rfl

omit [Finite G] in
/-- Mapping coefficients along a commutative-ring homomorphism preserves
centrality of group-algebra elements. -/
theorem mapRingHom_mem_center
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (e : MonoidAlgebra R G)
    (he : e ∈ Set.center (MonoidAlgebra R G)) :
    MonoidAlgebra.mapRingHom G f e ∈
      Set.center (MonoidAlgebra S G) := by
  exact groupAlgebra_mapRingHom_mem_center f e he

omit [Finite G] in
/-- Restricting the coefficients of a central group-algebra element to an
element centralizer remains central in the centralizer group algebra. -/
theorem centralizerRestriction_mem_center
    {R : Type*} [CommRing R] (z : G) (e : MonoidAlgebra R G)
    (he : e ∈ Set.center (MonoidAlgebra R G)) :
    BrauerMap.centralizerRestriction R z e ∈
      Set.center
        (MonoidAlgebra R (Subgroup.centralizer ({z} : Set G))) := by
  exact BrauerMap.centralizerRestriction_mem_center z e he

/-- The ambient principal-block idempotent after reduction modulo the chosen
prime above `2`. -/
@[expose] noncomputable def reducedPrincipalBlockElement
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
@[expose] noncomputable def involutionBrauerPrincipalBlockElement
    (d : PrincipalCongruenceBlockData G) (z : G) :
    MonoidAlgebra (principalResidueField d)
      (Subgroup.centralizer ({z} : Set G)) :=
  BrauerMap.centralizerRestriction (principalResidueField d) z
    (reducedPrincipalBlockElement d)

/-- Reduction modulo the ambient prime and involution Brauer restriction
commute on the localized principal-block idempotent. -/
theorem involutionBrauerPrincipalBlockElement_eq_map_restriction
    (d : PrincipalCongruenceBlockData G) (z : G) :
    involutionBrauerPrincipalBlockElement d z =
      MonoidAlgebra.mapRingHom
        (Subgroup.centralizer ({z} : Set G)) (localizationToResidue d)
        (BrauerMap.centralizerRestriction
          (Localization.AtPrime d.primeIdeal) z
          (BlockOrthogonality.localizedPrincipalBlockElement d)) := by
  exact BrauerMap.centralizerRestriction_mapRingHom
    (localizationToResidue d) z
      (BlockOrthogonality.localizedPrincipalBlockElement d)

theorem involutionBrauerPrincipalBlockElement_isIdempotent
    (d : PrincipalCongruenceBlockData G) (z : G)
    (hz : z * z = 1) :
    IsIdempotentElem (involutionBrauerPrincipalBlockElement d z) := by
  exact BrauerMap.centralizerRestriction_isIdempotent_of_mem_center
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


/-- The complex principal selector acts identically on the trivial module. -/
theorem principalBlockElement_augmentation_eq_one
    (d : PrincipalCongruenceBlockData G) :
    groupAlgebraAugmentation ℂ G (BlockOrthogonality.principalBlockElement d) = 1 := by
  rw [groupAlgebraAugmentation_apply]
  exact BlockOrthogonality.principalBlockElement_sum_coeff_eq_one d

/-- The localized selector has augmentation one. -/
theorem localizedPrincipalBlockElement_augmentation_eq_one
    (d : PrincipalCongruenceBlockData G) :
    groupAlgebraAugmentation (Localization.AtPrime d.primeIdeal) G
      (BlockOrthogonality.localizedPrincipalBlockElement d) = 1 := by
  rw [groupAlgebraAugmentation_apply]
  exact BlockOrthogonality.localizedPrincipalBlockElement_sum_coeff_eq_one d

/-- The reduced principal idempotent acts identically on the trivial module. -/
theorem reducedPrincipalBlockElement_augmentation_eq_one
    (d : PrincipalCongruenceBlockData G) :
    groupAlgebraAugmentation (principalResidueField d) G
      (reducedPrincipalBlockElement d) = 1 := by
  change groupAlgebraAugmentation (principalResidueField d) G
    (MonoidAlgebra.mapRingHom G (localizationToResidue d)
      (BlockOrthogonality.localizedPrincipalBlockElement d)) = 1
  rw [groupAlgebraAugmentation_mapRingHom,
    localizedPrincipalBlockElement_augmentation_eq_one, map_one]

theorem reducedPrincipalBlockElement_ne_zero
    (d : PrincipalCongruenceBlockData G) :
    reducedPrincipalBlockElement d ≠ 0 := by
  intro h
  have haug := reducedPrincipalBlockElement_augmentation_eq_one d
  rw [h, map_zero] at haug
  exact zero_ne_one haug

/-- The involution Brauer image also has augmentation one. -/
theorem involutionBrauerPrincipalBlockElement_augmentation_eq_one
    (d : PrincipalCongruenceBlockData G) (z : G) (hz : z * z = 1) :
    groupAlgebraAugmentation (principalResidueField d)
      (Subgroup.centralizer ({z} : Set G))
      (involutionBrauerPrincipalBlockElement d z) = 1 := by
  change groupAlgebraAugmentation (principalResidueField d)
    (Subgroup.centralizer ({z} : Set G))
    (BrauerMap.centralizerRestriction (principalResidueField d) z
      (reducedPrincipalBlockElement d)) = 1
  rw [BrauerMap.augmentation_centralizerRestriction z hz _
    (reducedPrincipalBlockElement_mem_center d)]
  exact reducedPrincipalBlockElement_augmentation_eq_one d

theorem involutionBrauerPrincipalBlockElement_ne_zero
    (d : PrincipalCongruenceBlockData G) (z : G) (hz : z * z = 1) :
    involutionBrauerPrincipalBlockElement d z ≠ 0 := by
  intro h
  have haug := involutionBrauerPrincipalBlockElement_augmentation_eq_one d z hz
  rw [h, map_zero] at haug
  exact zero_ne_one haug

end BrauerBlockReduction

end ModularBlock
