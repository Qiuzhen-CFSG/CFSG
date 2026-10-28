module

public import Theory.GroupTheory.ZStar.Nagao.Complement

/-!
# Complement Action

The represented principal Nagao complement commutes with the action of
every element of the involution centralizer. The ambient principal selector
is central; the compatible local selector commutes with its whole local
group algebra. Embed the latter in the ambient group algebra and apply the
representation homomorphism. Their complementary product therefore commutes
with the centralizer as well, allowing restriction to its projective range.

Ported from `public/lean-eval/glauberman_zStar`,
`Submission/ZStar/CharacterwiseNagao.lean` (revision `c3503435`).
-/

public section

noncomputable section

open scoped BigOperators

namespace Glauberman.ZStar.CharacterwiseNagao

open ModularBlock PrincipalBlockConstruction

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

/-- In every representation, the Nagao complement commutes with the action
of every element of the involution centralizer. -/
theorem principalComplement_action_commutes_centralizer
    {G : Type u} {V : Type*} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G)
    [AddCommGroup V] [Module (Localization.AtPrime d.primeIdeal) V]
    (rho : Representation (Localization.AtPrime d.primeIdeal) G V)
    (z : G) (x : Subgroup.centralizer ({z} : Set G)) :
    Commute (rho.asAlgebraHom (NagaoComplement.principalComplement d z))
      (rho (x : G)) := by
  let R := Localization.AtPrime d.primeIdeal
  let H := Subgroup.centralizer ({z} : Set G)
  let e : MonoidAlgebra R G :=
    BlockOrthogonality.localizedPrincipalBlockElement d
  let b : MonoidAlgebra R H :=
    CompatibleBrauerBlock.localPrincipalBlockElementInAmbientLocalization d H
  let B : MonoidAlgebra R G := ModularBlock.NagaoComplement.centralizerSubtypeMap z b
  let X : MonoidAlgebra R G := MonoidAlgebra.of R G (x : G)
  have he : Commute e X :=
    (Semigroup.mem_center_iff.mp
      (BlockOrthogonality.localizedPrincipalBlockElement_mem_center d) X).symm
  have hb : Commute b (MonoidAlgebra.of R H x) :=
    (Semigroup.mem_center_iff.mp
      (CompatibleBrauerBlock.localPrincipalBlockElementInAmbientLocalization_mem_center
        d H) (MonoidAlgebra.of R H x)).symm
  have hB : Commute B X := by
    have hmap := hb.map (ModularBlock.NagaoComplement.centralizerSubtypeMap z)
    simpa [B, X, ModularBlock.NagaoComplement.centralizerSubtypeMap,
      MonoidAlgebra.of] using hmap
  have hemap := he.map rho.asAlgebraHom
  have hBmap := hB.map rho.asAlgebraHom
  have hemap' : Commute (rho.asAlgebraHom e) (rho (x : G)) := by
    simpa [X, Representation.asAlgebraHom_single_one] using hemap
  have hBmap' : Commute (rho.asAlgebraHom B) (rho (x : G)) := by
    simpa [X, Representation.asAlgebraHom_single_one] using hBmap
  have hresult : Commute
      (rho.asAlgebraHom e - rho.asAlgebraHom e * rho.asAlgebraHom B)
      (rho (x : G)) :=
    hemap'.sub_left (hemap'.mul_left hBmap')
  simpa [NagaoComplement.principalComplement, ModularBlock.NagaoComplement.complement,
    e, b, B, map_sub, map_mul] using hresult


end Glauberman.ZStar.CharacterwiseNagao

