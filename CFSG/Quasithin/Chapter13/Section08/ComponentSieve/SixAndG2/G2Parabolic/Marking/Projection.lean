module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Parabolic.WholeStarProjection
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Parabolic.FaithfulDisplacement
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceG2Cover
public import Theory.Representation.BinaryOffender.NormalLayerQuotient
public import Theory.Representation.G2NaturalTransport

/-!
# The whole-star projection through a central G₂ cover

The recognized component section supplies a surjective natural projection.
Its kernel is precisely the component fixed space, hence is invariant under
the whole star. The resulting natural quotient is faithful because the
component is self-centralizing. The natural normalizer then embeds the whole
star in G₂(2), with the original component marking and projection retained.
This includes both the natural and seven-dimensional Weyl alternatives.

Source: Aschbacher–Smith 13.8.27, printed p.963, with B.4.2 and I.1.6.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Parabolic
open TransvectionRecognition TransvectionRecognition.Component
open TransvectionRecognition.Component.ModelExtension Atlas.G2

variable {G : Type*} [Group G] [Finite G] {H K V₃ V₁ : Subgroup G}
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]

/-- The actual covering projection is equivariant for all of H*, including
the possible outer involution, and the whole actor embeds faithfully. -/
theorem whole_star_projection_of_section
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hfit : generalizedFitting (Source.Hstar H) = Source.starImage H K)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (hgen : Source.UH H V₃ = ⁅Source.UH H V₃, K⁆)
    (eK : (K ⧸ pCore 2 K) ≃* commutator (Model (ZMod 2)))
    (hs : HasSectionModel H V₃ V₁ ρ K hKH
      (Natural.OrthogonalCover.binaryNatural (ZMod 2)) eK) :
    ∃ (f : Source.Hstar H →* Model (ZMod 2))
      (p : Additive (Source.Utilde H V₃ V₁) →ₗ[ZMod 2] Natural.Space (ZMod 2)),
      Function.Injective f ∧ Function.Surjective p ∧
      (∀ a : Source.starImage H K,
        f a = ((Components.componentStarEquiv H K hKH hK).symm.trans eK a : Model (ZMod 2))) ∧
      (∀ a v, p (ρ a v) = Natural.action (ZMod 2) (f a) (p v)) ∧
      p.ker = fixedSpace ρ (Source.starImage H K) := by
  let L := Source.starImage H K
  let : L.Normal := by dsimp only [L]; rw [← hfit]; infer_instance
  let e : L ≃* commutator (Model (ZMod 2)) :=
    (Components.componentStarEquiv H K hKH hK).symm.trans eK
  obtain ⟨p, hp⟩ := exists_cover_of_section hKH hK ρ hρ hgen _ eK hs
  have he (a : L) (v) : p (ρ a v) = Natural.derivedAction (ZMod 2) (e a) (p v) := by
    have ha : modelActor hKH hK eK (e a) = (a : Source.Hstar H) := by
      change ((Components.componentStarEquiv H K hKH hK)
        (eK.symm (eK ((Components.componentStarEquiv H K hKH hK).symm a))) :
          Source.Hstar H) = a
      simp only [eK.symm_apply_apply, MulEquiv.apply_symm_apply]
    have hh := LinearMap.congr_fun (p.isIntertwining' (e a)) v
    change p (ρ (modelActor hKH hK eK (e a)) v) =
      Natural.derivedAction (ZMod 2) (e a) (p v) at hh
    rwa [ha] at hh
  have hk : p.toLinearMap.ker = fixedSpace ρ L := by
    apply le_antisymm
    · intro v hv a
      have h := hp.2.1 hv (e a)
      change ρ (modelActor hKH hK eK (e a)) v = v at h
      simpa only [modelActor, e, MulEquiv.trans_apply, MonoidHom.comp_apply,
        MulEquiv.coe_toMonoidHom, eK.symm_apply_apply, MulEquiv.apply_symm_apply] using h
    · intro v hv
      apply Natural.Transport.fixed_eq_zero
      intro a
      have h := he (e.symm a) v
      rw [show ρ (e.symm a) v = v from hv (e.symm a), e.apply_symm_apply] at h
      exact h.symm
  let τ := (Natural.derivedAction (ZMod 2)).comp e.toMonoidHom
  have hτ : Function.Injective τ := Natural.BinaryNormalizer.faithful.comp e.injective
  obtain ⟨_, hc⟩ := component_properties_of_fitting L hfit e
  obtain ⟨σ, hσ, hpσ, hres⟩ := exists_faithful_action_of_normal_layer_quotient
    ρ L (hc.le.trans bot_le) τ hτ p.toLinearMap hp.1 hk he
  obtain ⟨f, hf, hrestrict, hwhole⟩ := Natural.BinaryNormalizer.ambient_embedding
    σ L e (LinearEquiv.refl _ _) (fun a v => hres a v) hσ
  exact ⟨f, p.toLinearMap, hf, hp.1, hrestrict,
    fun a v => (hpσ a v).trans (hwhole a (p v)), hk⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Parabolic
