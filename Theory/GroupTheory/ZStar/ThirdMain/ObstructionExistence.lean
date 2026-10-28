module

public import Theory.GroupTheory.ZStar.ThirdMain.ExtraObstruction
public import Theory.GroupTheory.ZStar.ThirdMain.NonprincipalFactor

/-!
# Failed Brauer equality produces an extra obstruction

The admissible primitive-factor construction from the Third Main reduction
already supplies a two-subgroup and an augmentation-zero primitive factor
of its direct extra Brauer image. Map that subgroup from the involution
centralizer into the ambient group and package these exact components as
an extra obstruction. This is the existence input for maximal-obstruction
selection; no normalizer-support argument is used here.

Ported from `public/lean-eval/glauberman_zStar`,
`Submission/ZStar/BrauerThirdMain.lean` (revision `c3503435`).
-/

public section

noncomputable section

namespace Glauberman.ZStar.BrauerThirdMain

open ModularBlock PrincipalBlockConstruction

universe v

/-- Failure of the involution equality supplies at least one extra
obstruction in the ambient group. -/
theorem exists_extraObstruction_of_not_brauerEquality
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G)
    (hzI : IsInvolution z)
    (hne : ¬ CompatibleBrauerBlock.InvolutionPrincipalBrauerEquality d z) :
    ∃ Q : Subgroup G, IsExtraObstruction d Q := by
  obtain ⟨Q, b, hQ, hbPrimitive, hbAug, _hbAmbient,
      _hbLocal, hbExtra, _hQadmissible⟩ :=
    ThirdMainReduction.exists_admissible_primitiveAmbientBrauerFactor_orthogonal_principal_of_not_brauerEquality
      d z hzI hne
  let H := Subgroup.centralizer ({z} : Set G)
  let QG : Subgroup G := Q.map H.subtype
  exact ⟨QG, hQ, b, hbPrimitive, hbAug, hbExtra⟩

end Glauberman.ZStar.BrauerThirdMain

