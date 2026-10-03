module

public import Theory.GroupTheory.ZStar.Nagao.SupportFromEquality
public import Theory.GroupTheory.ZStar.BrauerThirdMain

/-!
# Unconditional characterwise local core support

The principal Brauer equality proved by Third Main supplies the sole
block-theoretic hypothesis of the characterwise Nagao/projection argument.
Consequently, for every principal-block character and involution, its
section has no outside-local-principal-block component on the local odd
core. The local datum is the canonical compatible centralizer datum,
formed with the contracted ambient cyclotomic prime.

This assembly closes the ordinary-character support input to section
invariance in the Z* proof. It assumes neither local support nor section
invariance. The conditional adapter is re-exported by the public import.
Ported from `public/lean-eval/glauberman_zStar`,
`Submission/ZStar/CharacterwiseSupport.lean` (revision `c3503435`).
-/

public section

namespace Glauberman.ZStar.CharacterwiseSupport

open ModularBlock PrincipalBlockConstruction

universe u

/-- Unconditional local principal-block core support. The block-theoretic
input to the characterwise argument is supplied by the Third Main theorem. -/
theorem canonicalLocalPrincipalBlockCoreSupport
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (i : d.I)
    (hi : i ∈ d.block) (z : G) (hzI : IsInvolution z) :
    LocalBlockSection.CanonicalLocalPrincipalBlockCoreSupport d i z := by
  exact canonicalLocalPrincipalBlockCoreSupport_of_brauerEquality
    d i hi z hzI
    (Glauberman.ZStar.involutionPrincipalBrauerEquality d z hzI)

end Glauberman.ZStar.CharacterwiseSupport

