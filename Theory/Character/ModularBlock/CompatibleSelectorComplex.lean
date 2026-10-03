module

public import Theory.Character.ModularBlock.IsotypicLattice
public import Theory.Character.ModularBlock.CompatibleBrauerBlock

/-!
# Compatible Selector Complex

The compatible local principal selector, expressed over the ambient
cyclotomic localization, maps to the ordinary complex principal selector of
the subgroup. The proof compares the two maps out of the subgroup
localization on generators from its cyclotomic order, then uses coefficient
change for the localized selector. This identifies the integral and complex
local selectors without any block-correspondence hypothesis.

Ported from `public/lean-eval/glauberman_zStar`,
`Submission/ZStar/CharacterwiseProjection.lean` (revision `c3503435`).
-/

public section

noncomputable section

open scoped BigOperators

namespace ModularBlock.CharacterwiseProjection

open ModularBlock PrincipalBlockConstruction

universe u v

attribute [local instance] Fintype.ofFinite

variable {G : Type u} [Group G] [finG : Finite G]

/-! Coefficient change sends the compatible local selector to its ordinary
complex principal-block idempotent. -/

private instance principalPrime_isPrime
    (d : PrincipalCongruenceBlockData G) : d.primeIdeal.IsPrime :=
  d.primeIdeal_maximal.isPrime

set_option maxHeartbeats 1200000 in
theorem map_localPrincipalBlockElementInAmbientLocalization
    (d : PrincipalCongruenceBlockData G) (H : Subgroup G) :
    MonoidAlgebra.mapRingHom H (IsotypicLattice.localizationToComplex d)
        (CompatibleBrauerBlock.localPrincipalBlockElementInAmbientLocalization
          d H) =
      BlockOrthogonality.principalBlockElement
        (CompatibleBrauerBlock.localData d H) := by
  let l : PrincipalCongruenceBlockData H :=
    CompatibleBrauerBlock.localData d H
  let phi : Localization.AtPrime d.primeIdeal →+* ℂ :=
    IsotypicLattice.localizationToComplex d
  let incl : Localization.AtPrime l.primeIdeal →+*
      Localization.AtPrime d.primeIdeal :=
    CompatibleLocalBlock.compatibleSubgroupLocalizationInclusion d H
  let phiLocal : Localization.AtPrime l.primeIdeal →+* ℂ :=
    IsotypicLattice.localizationToComplex l
  have hf : ∀ a : cyclotomicOrder l.eta,
      phiLocal (algebraMap _ (Localization.AtPrime l.primeIdeal) a) =
        (a : ℂ) := by
    intro a
    exact IsotypicLattice.localizationToComplex_algebraMap l a
  have hlocal0 :=
    BlockOrthogonality.mapRingHom_localizedPrincipalBlockElement_eq_principalBlockElement
      (G := H) l phiLocal hf
  have hhom : phi.comp incl = phiLocal := by
    apply IsLocalization.ringHom_ext l.primeIdeal.primeCompl
    apply RingHom.ext
    intro a
    change phi (incl (algebraMap _ (Localization.AtPrime l.primeIdeal) a)) =
      phiLocal (algebraMap _ (Localization.AtPrime l.primeIdeal) a)
    rw [show incl (algebraMap _ (Localization.AtPrime l.primeIdeal) a) =
        algebraMap _ (Localization.AtPrime d.primeIdeal)
          (CompatibleLocalBlock.cyclotomicOrderInclusion
            (CompatibleLocalBlock.subgroupRoot_mem d H) a) by
      exact CompatibleLocalBlock.compatibleSubgroupLocalizationInclusion_algebraMap
        d H a]
    rw [show phi (algebraMap _ (Localization.AtPrime d.primeIdeal)
          (CompatibleLocalBlock.cyclotomicOrderInclusion
            (CompatibleLocalBlock.subgroupRoot_mem d H) a)) =
        ((CompatibleLocalBlock.cyclotomicOrderInclusion
          (CompatibleLocalBlock.subgroupRoot_mem d H) a :
            cyclotomicOrder d.eta) : ℂ) by
      exact IsotypicLattice.localizationToComplex_algebraMap d _]
    rw [show phiLocal (algebraMap _ (Localization.AtPrime l.primeIdeal) a) =
        (a : ℂ) by
      exact IsotypicLattice.localizationToComplex_algebraMap l a]
    exact Subring.coe_inclusion _ a
  rw [CompatibleBrauerBlock.localPrincipalBlockElementInAmbientLocalization]
  change MonoidAlgebra.mapRingHom H phi
      (MonoidAlgebra.mapRingHom H incl
        (BlockOrthogonality.localizedPrincipalBlockElement l)) =
    BlockOrthogonality.principalBlockElement l
  have hmap :
      MonoidAlgebra.mapRingHom H phi
          (MonoidAlgebra.mapRingHom H
            incl (BlockOrthogonality.localizedPrincipalBlockElement l)) =
        MonoidAlgebra.mapRingHom H phiLocal
          (BlockOrthogonality.localizedPrincipalBlockElement l) := by
    ext g
    simp only [MonoidAlgebra.coeff_mapRingHom]
    exact DFunLike.congr_fun hhom
      ((BlockOrthogonality.localizedPrincipalBlockElement l).coeff g)
  exact hmap.trans hlocal0


end ModularBlock.CharacterwiseProjection

