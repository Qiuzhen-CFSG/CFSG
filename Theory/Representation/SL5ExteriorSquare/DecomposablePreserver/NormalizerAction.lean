module
public import Theory.Representation.SL5ExteriorSquare.DecomposablePreserver.Reconstruction
public import Theory.Representation.BinaryConjugationSection.NormalizerAction

/-!
# Realizing marked ambient normalizer actions

A marking of an ambient subgroup by the additive binary exterior square
transports its full normalizer action to linear equivalences. If the marked
conjugation preserves decomposable vectors, the preserver theorem realizes
that very action by an element of SL₅(2). The pointwise and ambient equations
retain the marking and the convention x ↦ n * x * n⁻¹.

This is the conditional application needed for native normalizer assembly;
the ambient class/decomposable matching supplies the sole preservation premise.
No assertion about a particular native group is made here.
-/

public section

namespace Representation.SL5ExteriorSquare
open SL5TenDimensional

theorem normalizerAction_eq_exteriorAction_of_preserves_decomposable
    {G : Type*} [_root_.Group G] (F : Subgroup G) (c : F ≃* Multiplicative V)
    (n : Subgroup.normalizer (F : Set G))
    (hD : ∀ x : F, InExteriorOrbit decomposable (c x).toAdd →
      InExteriorOrbit decomposable (c (F.normalizerMonoidHom n x)).toAdd) :
    ∃ g : Group, (BinaryConjugationSection.normalizerAction
      c.toMonoidHom c.bijective n).toLinearMap = exteriorAction 2 g := by
  apply exists_exteriorAction_of_preserves_decomposable
  intro v hv
  let x : F := c.symm (Multiplicative.ofAdd v)
  have hx : (c x).toAdd = v := congrArg Multiplicative.toAdd (c.apply_symm_apply _)
  have he := (congrArg (BinaryConjugationSection.normalizerAction
    c.toMonoidHom c.bijective n) hx).symm.trans
      (BinaryConjugationSection.normalizerAction_coordinates c.toMonoidHom c.bijective n x)
  exact (congrArg (InExteriorOrbit decomposable) he).mpr (hD x (hx.symm ▸ hv))

/-- The realized normalizer action uses the given marking and ambient
conjugation n * x * n⁻¹, with the same normalizer element throughout. -/
theorem normalizerAction_realization_of_preserves_decomposable
    {G : Type*} [_root_.Group G] (F : Subgroup G) (c : F ≃* Multiplicative V)
    (n : Subgroup.normalizer (F : Set G))
    (hD : ∀ x : F, InExteriorOrbit decomposable (c x).toAdd →
      InExteriorOrbit decomposable (c (F.normalizerMonoidHom n x)).toAdd) :
    ∃ g : Group,
      (BinaryConjugationSection.normalizerAction
        c.toMonoidHom c.bijective n).toLinearMap = exteriorAction 2 g ∧
      (∀ x : F, (c (F.normalizerMonoidHom n x)).toAdd = exteriorAction 2 g (c x).toAdd) ∧
      (∀ x : F, (F.normalizerMonoidHom n x : G) = (n : G) * (x : G) * (n : G)⁻¹) := by
  obtain ⟨g,hg⟩ := normalizerAction_eq_exteriorAction_of_preserves_decomposable F c n hD
  refine ⟨g,hg,?_,?_⟩
  · intro x
    exact (BinaryConjugationSection.normalizerAction_coordinates
      c.toMonoidHom c.bijective n x).symm.trans (LinearMap.congr_fun hg (c x).toAdd)
  · intro x
    exact Subgroup.normalizerMonoidHom_apply_apply_coe F n x

end Representation.SL5ExteriorSquare
