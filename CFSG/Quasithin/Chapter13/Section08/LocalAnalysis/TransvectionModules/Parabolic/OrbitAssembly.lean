module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.RankDoubling

/-!
# Connect the source parabolic marking to the literal orbit

The full H* coordinates supplied by the marking theorem restrict to a
surjective actor K₂ → A₄. Equality of the two definitions of a section image
then identifies the actual V₂/V₁ and V₃/V₁ with the marked model flag.
The intertwining equation is evaluated on actual conjugates in U_H.
Consequently the orbit-transport theorem needs no additional marking input.

Source: Aschbacher–Smith, 13.8.6, printed p.948 (PDF p.965).
-/

public section
open Subgroup Module BinaryPermutation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.SourceAssembly
open TransvectionRecognition
open Theory.SpecificGroups.SymmetricSix
variable {G : Type*} [Group G]
variable {H V₁ V₂ V₃ : Subgroup G} [IsElementaryAbelian 2 (Source.UH H V₃)]

/-- The two independently defined literal section images agree. -/
theorem flagImage_eq_sectionImage {X : Type*} [AddCommGroup X] [Module (ZMod 2) X]
    (E : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] X) (A : Subgroup G) :
    RankDoubling.MarkedOrbit.flagImage H V₁ V₃ E A =
      (Marking.sectionImage H V₃ V₁ A).map E.toLinearMap := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨_, ⟨u.toMul, hu, rfl⟩, rfl⟩
  · rintro ⟨x, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨Additive.ofMul u, hu, rfl⟩

/-- Restrict the source coordinates to the actual residual actor and flag. -/
noncomputable def orbitMarking_of_coordinates [Finite G]
    {X : Type*} [AddCommGroup X] [Module (ZMod 2) X]
    (r : Representation (ZMod 2) (Equiv.Perm (Fin 6)) X) (p s : X)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (φ : Source.Hstar H →* Equiv.Perm (Fin 6))
    (E : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] X)
    (he : ∀ a u, E (ρ a u) = r (φ a) (E u))
    (hp : (Marking.sectionImage H V₃ V₁ V₂).map E.toLinearMap = Submodule.span (ZMod 2) {p})
    (hs : (Marking.sectionImage H V₃ V₁ V₃).map E.toLinearMap = Submodule.span (ZMod 2) {p,s})
    (hi : ((Source.K2 H V₂).subgroupOf H).map
      (φ.comp (QuotientGroup.mk' (pCore 2 H))) = BinaryFlags.K) :
    RankDoubling.MarkedOrbit.Marking H V₁ V₂ V₃ r p s := by
  let f := Marking.imageSurjection H (Source.K2 H V₂) (Source.K2_le H V₂)
    (φ.comp (QuotientGroup.mk' (pCore 2 H))) BinaryFlags.K hi
  refine {
    equiv := E
    actor := f
    actor_surjective := Marking.imageSurjection_surjective H _ _ _ _ hi
    point_image := (flagImage_eq_sectionImage E V₂).trans hp
    plane_image := (flagImage_eq_sectionImage E V₃).trans hs
    intertwines := ?_ }
  intro k u
  change E (vector H V₃ V₁ _) =
    r (φ (QuotientGroup.mk' (pCore 2 H) ⟨k, Source.K2_le H V₂ k.property⟩))
      (E (vector H V₃ V₁ u))
  exact (congrArg E (hρ ⟨k, Source.K2_le H V₂ k.property⟩ u).symm).trans (he _ _)

/-- The constructed parabolic marking supplies the orbit marking in either dimension. -/
theorem orbitMarking_of_markedParabolic [Finite G] (K : Subgroup G) (T : Sylow 2 G)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ) (h : Marking.MarkedParabolic K V₂ T ρ) :
    Nonempty (RankDoubling.MarkedOrbit.NaturalMarking H V₁ V₂ V₃) ∨
      Nonempty (RankDoubling.MarkedOrbit.CoverMarking H V₁ V₂ V₃) := by
  obtain ⟨φ, _, _, hm, hi, _⟩ := h
  rcases hm with ⟨E, he, hp, hs⟩ | ⟨E, he, hp, hs, _⟩
  · refine Or.inl ⟨orbitMarking_of_coordinates (naturalRepresentation (Fin 6))
      OrbitModels.naturalPoint (coreToNatural (Fin 6) OrbitModels.seed) ρ hρ φ E he hp ?_ hi⟩
    simpa only [OrbitModels.plane, Submodule.map_span, Set.image_insert_eq,
      Set.image_singleton, OrbitModels.naturalPoint] using hs
  · exact Or.inr ⟨orbitMarking_of_coordinates (coreRepresentation (Fin 6))
      OrbitModels.point OrbitModels.seed ρ hρ φ E he hp hs hi⟩

end CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.SourceAssembly
