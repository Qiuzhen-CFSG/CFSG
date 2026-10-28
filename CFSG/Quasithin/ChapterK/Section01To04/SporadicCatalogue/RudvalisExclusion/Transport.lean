module

public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.RudvalisExclusion.Contracts
public import Theory.Representation.RepEquiv

/-!
# Transport of the original cubic actor into the marked module's normalizer

Conjugating the ambient action by the module marking embeds it in the full
linear normalizer of the marked component. The same elementary subgroup,
its binary rank, its cubic action and its literal fixed-space codimension
survive this embedding. The source hypotheses concern the original ambient
group throughout; no SQTK assumption on the full normalizer is needed.

This is the assembly step for Aschbacher--Smith K.4, printed p.457.
-/

public section
namespace CFSG.Quasithin.ChapterK.SporadicCatalogue.RudvalisExclusion
open Subgroup Representation.BinaryOffender
open scoped ENNReal

/-- The marked action inherits irreducibility from the given component module. -/
theorem standardRepresentation_irreducible_of_marking
    {L V : Type*} [Group L] [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) L V) (e : L ≃* standardGroup)
    (E : V ≃ₗ[ZMod 2] Space)
    (he : ∀ l v, E (σ l v) = standardRepresentation (e l) (E v))
    (hi : σ.IsIrreducible) : standardRepresentation.IsIrreducible := by
  let f : Representation.RepEquiv σ (standardRepresentation.comp e.toMonoidHom) :=
    { E with
      isIntertwining' := fun l => LinearMap.ext (he l) }
  exact Representation.RepEquiv.irreducible_of_group_iso e (fun _ _ => rfl)
    ((Representation.RepEquiv.irreducible_euqiv f).mp hi)

private theorem cubic_le_two_map
    {G D V W : Type*} [Group G] [Finite G] [Group D] [Finite D]
    [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) D W)
    (f : G →* D) (hf : Function.Injective f) (E : V ≃ₗ[ZMod 2] W)
    (he : ∀ g v, E (ρ g v) = σ (f g) (E v))
    (hq : cubicRatio ρ ≤ 2) : cubicRatio σ ≤ 2 := by
  obtain ⟨A, hA, hc, hd⟩ := (cubicRatio_le_nat_iff ρ 2).mp hq
  let : IsElementaryAbelian 2 A := hA.2
  have hAm : IsElementaryTwo (A.map f) :=
    ⟨fun h => hA.1 ((A.map_eq_bot_iff_of_injective hf).mp h),
      IsElementaryAbelian.map f⟩
  have hdisp (g : G) (v : V) :
      displacement σ (f g) (E v) = E (displacement ρ g v) := by
    simp only [displacement, LinearMap.sub_apply, LinearMap.id_apply, map_sub, he]
  apply (cubicRatio_le_nat_iff σ 2).mpr
  refine ⟨A.map f, hAm, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨c, hc', rfl⟩ w
    obtain ⟨v, rfl⟩ := E.surjective w
    rw [hdisp, hdisp, hdisp, hc a ha b hb c hc' v, map_zero]
  · rw [← fixedCodim_map_equivariant ρ σ f E he, rank_map_injective f hf]
    exact hd

/-- A marking of the component action preserves the original ambient cubic
bound in the full linear normalizer, including outer actions. -/
theorem cubic_le_two_standardNormalizer
    {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (L : Subgroup G) [L.Normal]
    (hf : Function.Injective ρ) (e : L ≃* standardGroup)
    (E : V ≃ₗ[ZMod 2] Space)
    (he : ∀ (l : L) v, E (ρ l v) = standardRepresentation (e l) (E v))
    (hq : cubicRatio ρ ≤ 2) :
    cubicRatio (normalizerRepresentation standardRepresentation) ≤ 2 := by
  let τ : Representation (ZMod 2) G Space := E.conjRingEquiv.toMonoidHom.comp ρ
  have hτ (g : G) (v : V) : τ g (E v) = E (ρ g v) := by
    change E (ρ g (E.symm (E v))) = E (ρ g v)
    rw [E.symm_apply_apply]
  have hres (l : L) : τ l = standardRepresentation (e l) := by
    apply LinearMap.ext
    intro w
    obtain ⟨v, rfl⟩ := E.surjective w
    exact (hτ l v).trans (he l v)
  have him : actionImage (τ.comp L.subtype) = actionImage standardRepresentation := by
    ext x
    constructor
    · rintro ⟨l, rfl⟩
      exact ⟨e l, Units.ext (hres l).symm⟩
    · rintro ⟨m, rfl⟩
      obtain ⟨l, rfl⟩ := e.surjective m
      exact ⟨l, Units.ext (hres l)⟩
  let j : G →* linearNormalizer standardRepresentation :=
    τ.asGroupHom.codRestrict _ (fun g => by
      have hg := actionImage_le_linearNormalizer τ L ⟨g, rfl⟩
      change τ.asGroupHom g ∈ normalizer (actionImage (τ.comp L.subtype) : Set _) at hg
      change τ.asGroupHom g ∈ normalizer (actionImage standardRepresentation : Set _)
      rwa [him] at hg)
  have hj : Function.Injective j := by
    intro a b hab
    apply hf
    apply E.conjRingEquiv.injective
    exact congrArg (fun x : linearNormalizer standardRepresentation => x.val.val) hab
  apply cubic_le_two_map ρ (normalizerRepresentation standardRepresentation) j hj E
    (fun g v => ?_) hq
  exact (hτ g v).symm

end CFSG.Quasithin.ChapterK.SporadicCatalogue.RudvalisExclusion
