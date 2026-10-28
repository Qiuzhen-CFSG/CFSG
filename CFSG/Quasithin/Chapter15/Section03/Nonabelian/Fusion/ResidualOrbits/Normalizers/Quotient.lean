module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.Normalizers.Lifting

/-!
# The quotient of the relative block normalizer

Restriction of `H → H*` gives the actual normalizer map. Its kernel is the
relative copy of `U`, and its range is the full normalizer of `B*` once the
block geometry is established. An `S₄` model for that range therefore gives
an `S₄` quotient of the relative ambient normalizer.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), p.1151.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.Normalizers
open Recognition
variable {G : Type*} [Group G]

/-- The genuine restriction of the actor projection to `N_H(B)`. -/
def blockNormalizerActorMap (Z B : Subgroup G) :
    (normalizer (B : Set G)).subgroupOf (centralizerH Z) →* ActorQuotient Z :=
  (actorProjection Z).comp ((normalizer (B : Set G)).subgroupOf (centralizerH Z)).subtype

/-- The kernel is the literal relative intersection with `U`. -/
theorem blockNormalizerActorMap_ker (Z ZS B : Subgroup G)
    (hU : closureU Z ZS = coreQ Z) :
    (blockNormalizerActorMap Z B).ker =
      ((closureU Z ZS).subgroupOf (centralizerH Z)).subgroupOf
        ((normalizer (B : Set G)).subgroupOf (centralizerH Z)) := by
  ext n
  exact actorProjection_eq_one_iff Z ZS hU n

variable (Z ZS : Subgroup G) [(Z.subgroupOf (closureU Z ZS)).Normal]

/-- The range of the restricted map, with its literal ambient subgroup. -/
theorem blockNormalizerActorMap_range (B : Subgroup G) (hBH : B ≤ centralizerH Z)
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (hZU : Z ≤ closureU Z ZS) (hZB : Z ≤ B)
    (hfixed : vectorImage Z ZS (B ⊓ closureU Z ZS) =
      (actorAction Z ZS hkernel).commonFixed (actorImage Z B))
    (hcentral : B = centralizerH Z ⊓
      centralizer ((B ⊓ closureU Z ZS : Subgroup G) : Set G)) :
    (blockNormalizerActorMap Z B).range =
      normalizer (actorImage Z B : Set (ActorQuotient Z)) := by
  rw [blockNormalizerActorMap, MonoidHom.range_comp, range_subtype]
  exact block_normalizer_image Z ZS B hBH hkernel hZU hZB hfixed hcentral

/-- An actual `S₄` model identifies the quotient by the tracked kernel.
It does not assign order 24 to the relative ambient normalizer. -/
noncomputable def blockNormalizerQuotientEquiv (B : Subgroup G)
    (hBH : B ≤ centralizerH Z)
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (hZU : Z ≤ closureU Z ZS) (hZB : Z ≤ B)
    (hfixed : vectorImage Z ZS (B ⊓ closureU Z ZS) =
      (actorAction Z ZS hkernel).commonFixed (actorImage Z B))
    (hcentral : B = centralizerH Z ⊓
      centralizer ((B ⊓ closureU Z ZS : Subgroup G) : Set G))
    (eN : normalizer (actorImage Z B : Set (ActorQuotient Z)) ≃* Equiv.Perm (Fin 4)) :
    (((normalizer (B : Set G)).subgroupOf (centralizerH Z)) ⧸
      (blockNormalizerActorMap Z B).ker) ≃* Equiv.Perm (Fin 4) :=
  (QuotientGroup.quotientKerEquivRange (blockNormalizerActorMap Z B)).trans
    ((MulEquiv.subgroupCongr (blockNormalizerActorMap_range Z ZS B hBH hkernel hZU hZB
      hfixed hcentral)).trans eN)

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.Normalizers
