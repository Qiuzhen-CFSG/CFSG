module
public import Theory.Representation.AlternatingFivePairCubicCriterion
public import Theory.Representation.AlternatingFiveMovedPair.NaturalJointDisplacement
public import Theory.Representation.AlternatingFiveMovedPair.NaturalInnerIntertwiners
public import Theory.Representation.AlternatingFiveMovedPair.NaturalNormalizerInvolutions
public import Theory.Representation.SL2FourNaturalOrbits.ElementaryActors

/-!
# The strict cubic estimate for the natural moved pair

The full binary linear normalizer acts on the marked `SL₂(4) × SL₂(4)`
by conjugation. Its elementary two-subgroups inject into the automorphism
group because centralizing involutions are trivial. Rank at most two uses
the universal displacement bound six; rank three uses an inner involution
and displacement eight; rank four uses independently supported inner
involutions and displacement twelve. These are strict bounds for the original
normalizer actors, including all scalar adjustments.

Source: Aschbacher–Smith D.3.5, printed pp.195–196.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Module
namespace Representation.AlternatingFiveMovedPair.Natural
open SL2FourNatural BinaryOffender BinaryOffender.NaturalTensor
open Theory.SpecificGroups.Alternating.FiveSquareAutomorphisms

private theorem strict_cubic_bound_of_conjugation (κ : linearNormalizer action →* MulAut (SL × SL))
    (hκaction : ∀ t g v, action (κ t g) (t.val.val v) = t.val.val (action g v))
    (A : Subgroup (linearNormalizer action)) (hA : IsElementaryTwo A)
    (hκ : Function.Injective (κ.comp A.subtype))
    (hlow : ∀ t ∈ A, t ≠ 1 → 6 ≤ operatorFixedCodim t.val.val)
    (hinner : ∀ t ∈ A, ∀ r : SL × SL, r * r = 1 → r ≠ 1 → κ t = MulAut.conj r →
      8 ≤ operatorFixedCodim t.val.val) :
    2 * rank A < fixedCodim (normalizerRepresentation action) A := by
  let : Finite Space := Module.finite_of_finite (ZMod 2)
  let : Finite (Module.End (ZMod 2) Space) :=
    Finite.of_injective DFunLike.coe DFunLike.coe_injective
  let := hA.2
  let e : (SL × SL) ≃* Pair := alternatingFiveEquiv.prodCongr alternatingFiveEquiv
  let k : linearNormalizer action →* MulAut Pair := (MulAut.congr e).toMonoidHom.comp κ
  have hconj (t : linearNormalizer action) (r : Pair) (ht : k t = MulAut.conj r) :
      κ t = MulAut.conj (e.symm r) := by
    apply (MulAut.congr e).injective
    change k t = _
    rw [ht]
    apply MulEquiv.ext
    intro x
    change r * x * r⁻¹ = e (e.symm r * e.symm x * (e.symm r)⁻¹)
    simp only [map_mul, map_inv, e.apply_symm_apply]
  apply AlternatingFivePairCubicCriterion.strict_bound
    (normalizerRepresentation action) k A hA
    ((MulAut.congr e).injective.comp hκ)
  · exact hlow
  · intro t ht r hr hr2 htr
    apply hinner t ht (e.symm r)
    · simpa only [map_mul, map_pow, map_one, pow_two] using congrArg e.symm hr2
    · intro h
      apply hr
      simpa only [map_one, e.apply_symm_apply] using congrArg e h
    · exact hconj t r htr
  · intro t ht u hu r s hr hs hr2 hs2 htr hus
    let a : SL := alternatingFiveEquiv.symm r
    let b : SL := alternatingFiveEquiv.symm s
    have ha : a * a = 1 := by
      simpa only [a, map_mul, map_pow, map_one, pow_two] using congrArg alternatingFiveEquiv.symm hr2
    have hb : b * b = 1 := by
      simpa only [b, map_mul, map_pow, map_one, pow_two] using congrArg alternatingFiveEquiv.symm hs2
    have ha1 : a ≠ 1 := by
      intro h
      apply hr
      simpa only [a, map_one, MulEquiv.apply_symm_apply] using congrArg alternatingFiveEquiv h
    have hb1 : b ≠ 1 := by
      intro h
      apply hs
      simpa only [b, map_one, MulEquiv.apply_symm_apply] using congrArg alternatingFiveEquiv h
    have her : e.symm (r, 1) = (a, 1) := by
      exact Prod.ext rfl (alternatingFiveEquiv.symm.map_one)
    have htr' : κ t = MulAut.conj (a, 1) := by
      rw [← her]
      exact hconj t (r, 1) htr
    have hes : e.symm (1, s) = (1, b) := by
      exact Prod.ext (alternatingFiveEquiv.symm.map_one) rfl
    have hus' : κ u = MulAut.conj (1, b) := by
      rw [← hes]
      exact hconj u (1, s) hus
    have ht2 : t * t = 1 := by
      simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) t ht
    have hu2 : u * u = 1 := by
      simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) u hu
    have hte : t.val.val = action (a, 1) := by
      apply inner_involution_intertwiner_eq_action t.val.val
        (congrArg (fun x : linearNormalizer action => x.val.val) ht2) (a, 1)
        (Prod.ext ha (one_mul _))
      intro g v
      have h := hκaction t g v
      rw [htr'] at h
      exact h.symm
    have hue : u.val.val = action (1, b) := by
      apply inner_involution_intertwiner_eq_action u.val.val
        (congrArg (fun x : linearNormalizer action => x.val.val) hu2) (1, b)
        (Prod.ext (one_mul _) hb)
      intro g v
      have h := hκaction u g v
      rw [hus'] at h
      exact h.symm
    have htmem : action.asGroupHom (a, 1) ∈ A.map (linearNormalizer action).subtype := by
      refine ⟨t, ht, ?_⟩
      exact Units.ext hte
    have humem : action.asGroupHom (1, b) ∈ A.map (linearNormalizer action).subtype := by
      refine ⟨u, hu, ?_⟩
      exact Units.ext hue
    have hh := fixedCodim_ge_twelve_of_independent_inner
      (A.map (linearNormalizer action).subtype) a b ha hb ha1 hb1 htmem humem
    rw [← fixedCodim_map_equivariant (normalizerRepresentation action) (Units.coeHom _)
      (linearNormalizer action).subtype (LinearEquiv.refl _ _) (fun _ _ => rfl) A] at hh
    exact hh

/-- Every nontrivial elementary two-actor in the entire natural-pair linear
normalizer has fixed codimension strictly larger than twice its rank. -/
theorem normalizer_strict_cubic_bound
    (A : Subgroup (linearNormalizer action)) (hA : IsElementaryTwo A) :
    2 * rank A < fixedCodim (normalizerRepresentation action) A := by
  let := hA.2
  apply strict_cubic_bound_of_conjugation normalizerConjugation normalizerConjugation_action
    A hA (normalizerConjugation_elementary_injective A)
  · intro t ht ht1
    apply normalizer_involution_displacement t _ ht1
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) t ht
  · intro t _ r hr2 hr htr
    exact normalizer_inner_involution_displacement t r hr2 hr htr

end Representation.AlternatingFiveMovedPair.Natural
