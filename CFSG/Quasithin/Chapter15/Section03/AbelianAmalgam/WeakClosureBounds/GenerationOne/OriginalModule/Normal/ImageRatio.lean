module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.OriginalModule.Normal.StableConstituentBorel

/-!
# Recognition from a quadratic bound on the faithful image

A local minimum-ratio actor may acquire a kernel upon restriction to one
component. Its surviving image still supplies the quadratic ratio needed by
B.4. The original centerless component embeds in that image, so recognition
and the actual Sylow-normalizer fixed-space calculation pull back unchanged.

Source: Aschbacher–Smith, D.2.5 and F.9.18(3–4), applied in 15.3.65.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalModule.Normal
open RepresentationReduction.SourceRestrictions.Cases
open Single.SmallRatio RepresentationReduction.SourceRestrictions.FFExclusions.ModelRigidity
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit.ActionImage.Structure

universe u
variable {D V : Type u} [Group D] [Finite D] [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) D V) (K : Subgroup D) [K.Normal]
    [IsQuasisimple K] {f : ℕ}

/-- Recognize the original irreducible component from the quadratic ratio of
the action image; the original quadratic actor need not remain faithful. -/
theorem natural_of_image_quadraticRatio
    (hs : IsSQTK KnownSimple.IsKnownSimple D)
    (hquot : IsPGroup 2 (D ⧸ K)) (hZ : center K = ⊥)
    (hi : IsIrreducible (ρ.comp K.subtype))
    (hn : ¬ (⊤ : Submodule (ZMod 2) V) ≤ fixedSpace ρ K)
    (hbound : quadraticRatio (imageRepresentation ρ) ≤ 2)
    (hm : SourceModel (K ⧸ center K) f) (hf : 1 < f) (ho : Odd f) :
    NaturalConstituent ρ K f := by
  have hsurvive : ¬ K ≤ (actionHom ρ).ker := by
    intro h
    apply hn
    intro v _ k
    exact (actionHom_eq_one_iff ρ k).mp (h k.property) v
  obtain ⟨hqs, hirr, hfit⟩ := image_structure ρ K hsurvive hquot hi
  let e : K ≃* generalizedFitting (actionImage ρ) :=
    (componentEquiv ρ K hsurvive hZ).trans (MulEquiv.subgroupCongr hfit.symm)
  have hyp : B4Hypotheses KnownSimple.IsKnownSimple (imageRepresentation ρ) := by
    refine ⟨image_sqtk ρ K hsurvive hs hquot hZ, imageRepresentation_injective ρ, ?_, ?_⟩
    · rw [hfit]
      exact hqs
    · rw [hfit]
      exact hirr
  have hrec := natural_of_B4_source (imageRepresentation ρ) hyp hbound
    (hm.transport (centralQuotientCongr e).symm) hf ho (centerless_of_equiv hZ e)
  cases hrec with
  | linearTwo F hF a =>
    exact .linearTwo F hF ⟨e.trans a.groupEquiv, a.linearEquiv, fun k v => a.intertwines (e k) v⟩
  | suzuki m hm he hF a =>
    exact .suzuki m hm he hF ⟨e.trans a.groupEquiv, a.linearEquiv, fun k v => a.intertwines (e k) v⟩
  | linearThree F hF a =>
    exact .linearThree F hF ⟨e.trans a.groupEquiv, a.linearEquiv, fun k v => a.intertwines (e k) v⟩
  | symplecticFour F hF a =>
    exact .symplecticFour F hF ⟨e.trans a.groupEquiv, a.linearEquiv, fun k v => a.intertwines (e k) v⟩

/-- The actual component Borel has zero fixed space when the faithful action
image has quadratic ratio at most two. -/
theorem fixedSpace_eq_bot_of_image_quadraticRatio
    (hs : IsSQTK KnownSimple.IsKnownSimple D)
    (hquot : IsPGroup 2 (D ⧸ K)) (hZ : center K = ⊥)
    (hi : IsIrreducible (ρ.comp K.subtype))
    (hn : ¬ (⊤ : Submodule (ZMod 2) V) ≤ fixedSpace ρ K)
    (hbound : quadraticRatio (imageRepresentation ρ) ≤ 2)
    (hm : SourceModel (K ⧸ center K) f) (hf : 1 < f) (ho : Odd f)
    (B : Subgroup K) (hB : ∃ P : Sylow 2 K, normalizer (P : Set K) = B) :
    fixedSpace (ρ.comp K.subtype) B = ⊥ :=
  fixedSpace_eq_bot_of_naturalConstituent ρ
    (natural_of_image_quadraticRatio ρ K hs hquot hZ hi hn hbound hm hf ho) hf B hB

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalModule.Normal
