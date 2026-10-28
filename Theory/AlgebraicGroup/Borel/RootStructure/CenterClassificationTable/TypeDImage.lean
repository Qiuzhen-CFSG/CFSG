module

public import Theory.AlgebraicGroup.Borel.RootStructure.theorem_1_12_4
public import Theory.AlgebraicGroup.Borel.AdjointCenter
public import Theory.AlgebraicGroup.Semisimple.Versions

/-!
The arbitrary-version half of the type `D` row in GLS3, Theorem 1.12.5(c)-(d).

The geometric input is a universal-version isogeny `Ku -> K`.  The proved
connected-isogeny center theorem identifies the image of the source center
with the target center, so an isomorphism from the universal center shape to
the source center can be composed with the inverse isomorphism.  The two
parity cases in `universalCenterShape` are handled explicitly: even rank uses
the product of two second-root groups, while odd rank uses fourth roots of
unity.  The universal cover, its isogeny, and the source shape are explicit
hypotheses here; constructing those data belongs to the separate universal
type-`D` leaf and does not require the unresolved global center-classification
theorem.
-/

set_option warningAsError false

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Type `D` arbitrary-version center image, with both parity shapes.

The explicit `Ku`, `hKu`, `φ`, and `hφ` arguments are the universal-cover
bridge.  The source `hKuShape` is the universal type-`D` calculation from
GLS3 (Theorem 1.12.5(c)); the present theorem performs the (d) transfer. -/
public theorem typeD_center_homomorphic_image
    (m : ℕ)
    {K Ku : Variety k} [AlgebraicGroup K] [AlgebraicGroup Ku]
    (_hSemisimple : IsSemisimpleAlgebraicGroup K)
    (_hSimple : IsSimpleAlgebraicGroup K)
    (_hType : HasRootSystemType K ⟨.D, m⟩)
    (_hValid : IsValidGeneratorTableClassification ⟨.D, m⟩)
    (hKu : IsUniversalVersion Ku)
    (φ : AlgebraicGroup.Morphism Ku K) (hφ : IsIsogeny φ)
    (hKuShape : HasCenterShape (K := Ku)
      (universalCenterShape ⟨.D, m⟩)) :
    IsCenterHomomorphicImageOfShape (K := K)
      (universalCenterShape ⟨.D, m⟩) := by
  by_cases hm : m % 2 = 0
  · have hCenter : Nonempty
        (Subgroup.center (Variety.Point Ku) ≃*
          (rootsOfUnity 2 k × rootsOfUnity 2 k)) := by
      simpa [universalCenterShape, HasCenterShape, hm] using hKuShape
    obtain ⟨sourceCenterEquiv⟩ := hCenter
    have hImage := center_homomorphic_image_of_isogeny φ hφ hKu.1.1
      sourceCenterEquiv.symm
    simpa [universalCenterShape, IsCenterHomomorphicImageOfShape, hm] using hImage
  · have hCenter : Nonempty
        (Subgroup.center (Variety.Point Ku) ≃* rootsOfUnity 4 k) := by
      simpa [universalCenterShape, HasCenterShape, hm] using hKuShape
    obtain ⟨sourceCenterEquiv⟩ := hCenter
    have hImage := center_homomorphic_image_of_isogeny φ hφ hKu.1.1
      sourceCenterEquiv.symm
    simpa [universalCenterShape, IsCenterHomomorphicImageOfShape, hm] using hImage

end Theory.AlgebraicGroup
