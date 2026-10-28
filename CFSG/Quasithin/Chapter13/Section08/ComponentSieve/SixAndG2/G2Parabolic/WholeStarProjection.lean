module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.ModelExtension.CoverProjection
public import Theory.Representation.G2BinaryNaturalNormalizer
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizing
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Parabolic.LinePlacement

/-!
# Extending the marked component action to the whole star

The recognized component model is the literal quotient map on `K/O₂(K)`.  Its
image is the actual `starImage H K`; after the fitting equality makes that
image normal, the binary normalizer theorem extends the marked action to an
injective action of all of `H*` on the same natural six-space.  The extension
is proved by surjectivity of the literal component equivalence, so no abstract
or unmarked component is substituted for the source actor.

Source: Aschbacher–Smith, 13.8.27 and B.4.2(4).
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Parabolic
open TransvectionRecognition TransvectionRecognition.Component
open TransvectionRecognition.Component.ModelExtension
open Atlas.G2

variable {G W : Type*} [Group G] [Finite G]
  [AddCommGroup W] [Module (ZMod 2) W] {H K : Subgroup G}

/-- Extend a literal component marking to the whole star quotient. -/
theorem whole_star_natural_embedding
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hfit : generalizedFitting (Source.Hstar H) = Source.starImage H K)
    (ρ : Representation (ZMod 2) (Source.Hstar H) W)
    (hρ : Function.Injective ρ)
    (eK : (K ⧸ pCore 2 K) ≃* commutator (Model (ZMod 2)))
    (E : W ≃ₗ[ZMod 2] Natural.Space (ZMod 2))
    (hE : ∀ a v, E (ρ (modelActor hKH hK eK a) v) =
      Natural.derivedAction (ZMod 2) a (E v)) :
    ∃ f : Source.Hstar H →* Model (ZMod 2), Function.Injective f ∧
      (∀ a : Source.starImage H K,
        f a = ((Components.componentStarEquiv H K hKH hK).symm.trans eK a :
          Model (ZMod 2))) ∧
      ∀ g v, E (ρ g v) = Natural.action (ZMod 2) (f g) (E v) := by
  let : (Source.starImage H K).Normal := hfit ▸ inferInstance
  let eL : Source.starImage H K ≃* commutator (Model (ZMod 2)) :=
    (Components.componentStarEquiv H K hKH hK).symm.trans eK
  have hEl : ∀ (a : Source.starImage H K) v,
      E (ρ a v) = Natural.derivedAction (ZMod 2) (eL a) (E v) := by
    intro a v
    let q := (Components.componentStarEquiv H K hKH hK).symm a
    have hmodel : (modelActor hKH hK eK (eK q) : Source.Hstar H) = a := by
      change ((Components.componentStarEquiv H K hKH hK) (eK.symm (eK q)) :
        Source.Hstar H) = a
      rw [eK.symm_apply_apply]
      exact congrArg Subtype.val
        ((Components.componentStarEquiv H K hKH hK).apply_symm_apply a)
    rw [← hmodel]
    simpa [eL, q] using hE (eK q) v
  obtain ⟨f, hf, hrestriction, hwhole⟩ :=
    Natural.BinaryNormalizer.ambient_embedding ρ (Source.starImage H K) eL E hEl hρ
  refine ⟨f, hf, ?_, hwhole⟩
  intro a
  exact hrestriction a


open AlternatingAndLinear.FourStructure.CriticalTransfer CriticalGeometry

/-- Apply whole-star extension to the actual critical endpoint line. The
component intertwiner suffices; whole-star equivariance is a conclusion. -/
theorem Aone_le_of_component_natural
    [FiniteDimensional (ZMod 2) W]
    {L T V V₃ V₁ : Subgroup G}
    (c : CriticalPair L T H V)
    (ρ : Representation (ZMod 2) (Source.Hstar H) W)
    (s : ConjugationSection H (Source.UH H V₃) V₁ ρ)
    (hρ : Function.Injective ρ)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hfit : generalizedFitting (Source.Hstar H) = Source.starImage H K)
    (eK : (K ⧸ pCore 2 K) ≃* commutator (Model (ZMod 2)))
    (E : W ≃ₗ[ZMod 2] Natural.Space (ZMod 2))
    (hE : ∀ a v, E (ρ (modelActor hKH hK eK a) v) =
      Natural.derivedAction (ZMod 2) a (E v))
    (hUg : c.Ugamma V₃ ≤ H)
    (hreverse : Source.UH H V₃ ≤ H.map (MulAut.conj (c.gb : G)).toMonoidHom)
    (hcard : Nat.card V₁ = 2)
    (hcompare : Nat.log 2
      ((Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁)).relIndex
        (Source.UH H V₃)) ≤ rank (Source.starImage H (c.Ugamma V₃)))
    (hA : Representation.BinaryOffender.IsElementaryTwo (Source.starImage H (c.Ugamma V₃)))
    (hr : rank (Source.starImage H (c.Ugamma V₃)) < 3) :
    c.Aone V₁ ≤ Source.UH H V₃ := by
  obtain ⟨f, hf, _, he⟩ := whole_star_natural_embedding hKH hK hfit ρ hρ eK E hE
  exact Aone_le_of_natural_projection c s hUg hreverse hcard hcompare
    f hf E.toLinearMap E.surjective he hA hr

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Parabolic
end
