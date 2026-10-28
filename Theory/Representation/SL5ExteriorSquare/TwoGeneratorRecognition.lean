module
public import Theory.Representation.SL5ExteriorSquare.TwoGeneratorRecognition.Normalizer
public import Theory.Representation.SL5ExteriorSquare.TwoGeneratorRecognition.Orbits

/-!
# Two-generator recognition of a marked exterior normalizer

This is the ready ambient application for the native J₄ octad-pullback F.
Given its actual marking, two left-conjugation certificates, preservation of
the decomposable orbit, and C_G(F)=F, `recognize_normalizer` constructs the
literal N_G(F)/F ≃ SL₅(2), with the same action, marking, and representatives.
`cover_nonidentity_from_native_actions` supplies the preceding fusion input
using only the two certificates, before preservation has been established.

The explicit natural matrices generate by short checked words and elementary
matrix induction. Orbit exhaustion and sizes reuse the existing exterior-square
geometry of Aschbacher–Smith 12.5.5 (printed p.819); the preserver theorem supplies
the normalizer upper bound for the native application in 12.5.1. No native
existence, fusion, centralizer, or global occurrence hypothesis is asserted here.
-/

@[expose] public noncomputable section
namespace Representation.SL5ExteriorSquare.TwoGeneratorRecognition
open SL5TenDimensional

/-- Ambient recognition from the native owner's literal conjugation certificates.
The decomposable-preservation and self-centralizer hypotheses are explicit inputs;
this theorem constructs the quotient and its actual exterior-module identification. -/
theorem recognize_normalizer
    {G : Type*} [_root_.Group G] (F : Subgroup G) (c : F ≃* Multiplicative V)
    (n0 n1 : Subgroup.normalizer (F : Set G))
    (h0 : ∀ x : F, (c (F.normalizerMonoidHom n0 x)).toAdd = exteriorAction 2 A0 (c x).toAdd)
    (h1 : ∀ x : F, (c (F.normalizerMonoidHom n1 x)).toAdd = exteriorAction 2 A1 (c x).toAdd)
    (hD : ∀ n : Subgroup.normalizer (F : Set G), ∀ x : F,
      InExteriorOrbit decomposable (c x).toAdd →
      InExteriorOrbit decomposable (c (F.normalizerMonoidHom n x)).toAdd)
    (hC : Subgroup.centralizer (F : Set G) = F) :
    ∃ e : (Subgroup.normalizer (F : Set G) ⧸
      F.subgroupOf (Subgroup.normalizer (F : Set G))) ≃* Group,
      (∀ n : Subgroup.normalizer (F : Set G),
        (BinaryConjugationSection.normalizerAction c.toMonoidHom c.bijective n).toLinearMap =
          exteriorAction 2 (e (QuotientGroup.mk n))) ∧
      (∀ (n : Subgroup.normalizer (F : Set G)) (x : F),
        (c.symm (Multiplicative.ofAdd
          (exteriorAction 2 (e (QuotientGroup.mk n)) (c x).toAdd)) : G) =
            (n : G) * (x : G) * (n : G)⁻¹) ∧
      e (QuotientGroup.mk n0) = A0 ∧ e (QuotientGroup.mk n1) = A1 := by
  have h0' := action_eq_of_coordinates F c n0 A0 h0
  have h1' := action_eq_of_coordinates F c n1 A1 h1
  refine ⟨normalizerQuotientEquiv F c hD n0 n1 h0' h1' hC,?_,?_,?_⟩
  · intro n
    exact congrArg LinearEquiv.toLinearMap (exteriorHom_normalizerToSL F c hD n).symm
  · exact normalizerQuotientEquiv_ambient F c hD n0 n1 h0' h1' hC
  · exact normalizerQuotientEquiv_generators F c hD n0 n1 h0' h1' hC

/-- The native fusion step can use its two conjugation certificates immediately,
before it proves the preservation hypothesis required by `recognize_normalizer`. -/
theorem cover_nonidentity_from_native_actions
    {G : Type*} [_root_.Group G] (F : Subgroup G) (c : F ≃* Multiplicative V)
    (n0 n1 : Subgroup.normalizer (F : Set G))
    (h0 : ∀ x : F, (c (F.normalizerMonoidHom n0 x)).toAdd = exteriorAction 2 A0 (c x).toAdd)
    (h1 : ∀ x : F, (c (F.normalizerMonoidHom n1 x)).toAdd = exteriorAction 2 A1 (c x).toAdd)
    (x0 x1 : F) (hx0 : (c x0).toAdd = decomposable)
    (hx1 : (c x1).toAdd = nondecomposable) (y : F) (hy : y ≠ 1) :
    (∃ n : Subgroup.normalizer (F : Set G),
      (n : G) * (x0 : G) * (n : G)⁻¹ = (y : G)) ∨
    (∃ n : Subgroup.normalizer (F : Set G),
      (n : G) * (x1 : G) * (n : G)⁻¹ = (y : G)) := by
  have h0' := action_eq_of_coordinates F c n0 A0 h0
  have h1' := action_eq_of_coordinates F c n1 A1 h1
  rcases normalizer_nonzero_orbits F c n0 n1 h0' h1' x0 x1 hx0 hx1 y hy with h | h
  · obtain ⟨n,hn⟩ := h
    exact Or.inl ⟨n,(Subgroup.normalizerMonoidHom_apply_apply_coe F n x0).symm.trans
      (congrArg Subtype.val hn)⟩
  · obtain ⟨n,hn⟩ := h
    exact Or.inr ⟨n,(Subgroup.normalizerMonoidHom_apply_apply_coe F n x1).symm.trans
      (congrArg Subtype.val hn)⟩

end Representation.SL5ExteriorSquare.TwoGeneratorRecognition
