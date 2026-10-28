module

public import Theory.AlgebraicGroup.Borel.AdjointCenter
public import Theory.AlgebraicGroup.Borel.RootStructure.theorem_1_12_4

/-!
# Type-C center image

This module proves the isogeny-transfer half of the type `C_m` row in GLS3,
Theorem 1.12.5(d), Table 1.12.5.  For `m >= 2`, the universal-center
calculation identifies the source center with `rootsOfUnity 2 k`.  Proposition
1.10.3(b) then says that an isogeny from that connected universal version maps
its center onto the center of any target version.  Composing these maps makes
the latter center a homomorphic image of the second roots of unity.

The universal source, its isogeny, and its center shape remain explicit here.
Their geometric construction and the type-C Cartan-kernel calculation are
separate lower-level inputs; in particular, this proof does not use the
placeholder-backed classification clause `theorem_1_12_5`.
-/

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- The center of an arbitrary semisimple simple type-`C_m` version is a
homomorphic image of the universal center along a universal isogeny. -/
public theorem typeC_center_homomorphic_image
    (m : ℕ)
    {K Ku : Variety k} [AlgebraicGroup K] [AlgebraicGroup Ku]
    (_hK : IsSemisimpleAlgebraicGroup K)
    (_hSimple : IsSimpleAlgebraicGroup K)
    (_hType : HasRootSystemType K ⟨.C, m⟩)
    (_hValid : IsValidGeneratorTableClassification ⟨.C, m⟩)
    (hKu : IsUniversalVersion Ku)
    (φ : AlgebraicGroup.Morphism Ku K) (hφ : IsIsogeny φ)
    (hKuShape : HasCenterShape (K := Ku)
      (universalCenterShape ⟨.C, m⟩)) :
    IsCenterHomomorphicImageOfShape (K := K)
      (universalCenterShape ⟨.C, m⟩) := by
  have hCenter : Nonempty
      (Subgroup.center (Variety.Point Ku) ≃* rootsOfUnity 2 k) := by
    simpa [universalCenterShape, HasCenterShape] using hKuShape
  obtain ⟨sourceCenterEquiv⟩ := hCenter
  have hImage := center_homomorphic_image_of_isogeny φ hφ hKu.1.1
    sourceCenterEquiv.symm
  simpa [universalCenterShape, IsCenterHomomorphicImageOfShape] using hImage

end Theory.AlgebraicGroup
