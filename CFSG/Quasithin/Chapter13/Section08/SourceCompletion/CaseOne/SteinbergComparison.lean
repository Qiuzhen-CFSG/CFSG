module
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.OriginalCubic
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.SteinbergRecognition

/-!
# The original Steinberg comparison in the nonabelian-span branch

The original local planes generate U_L/V and survive in an irreducible
quotient. Their literal parabolic images recognize the tensor quotient.
The point parabolic supplies both the full barred S₆ coordinates and a
surjective lift of its cubic actor. OriginalMaps constructs the natural
V section and the local two-core quotient; SteinbergRecognition constructs
the tensor section and its exact kernel. The resulting lower bound eight
contradicts the proved H-side upper bound seven, establishing abelianness.

The ordinary quotient, original local-plane outputs and their two
parabolic markings remain explicit. No abelianness, chief count, tensor
identification, cubic lift or strict denominator is assumed. Their final
source instantiation and the later permutation/13.4.1 exclusion remain
with qt-d-138-a6-endgame-source; earlier ordinary setup remains with
qt-d-138-six-g2-source. This is not yet all of source 13.8.33.
Source: Aschbacher--Smith, 13.8.33, printed pp.966--967.
-/

public section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
open TransvectionRecognition.Component.ModelExtension A6Endgame.IntersectionBalance
open A6Endgame.ActionAnalysis33.ChiefModels
open TransvectionQuotients TransvectionQuotients.FourLocalFactors
open Theory.SpecificGroups.SymmetricSix
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H L₂ : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

/-- Abelianness from the original two local planes and parabolic markings.
The cubic actor and all three L-side section maps are constructed here. -/
theorem span_abelian_of_source_local_planes
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalGeometry.CriticalPair L (T : Subgroup G) H V) (hH : H = G₁)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (e : Source.Hstar H ≃* Equiv.Perm (Fin 6))
    (model : CompatibleModel H V₃ V₁ a e)
    (hmark : (Source.starImage H ((L ⊔ (T : Subgroup G)) ⊓ H)).map e.toMonoidHom = BinaryFlags.H2)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (s : SectionStructure.Data L H (T : Subgroup G) (sourceOne L T V₁) L₂ V V₂ V₃)
    (e₁ : (((((sourceOne L T V₁) ⊔ (T : Subgroup G)).subgroupOf (L ⊔ (T : Subgroup G))).map
      (barMap (L ⊔ (T : Subgroup G)) V s.normalizes_V).rangeRestrict) ⧸
      pCore 2 ((((sourceOne L T V₁) ⊔ (T : Subgroup G)).subgroupOf (L ⊔ (T : Subgroup G))).map
      (barMap (L ⊔ (T : Subgroup G)) V s.normalizes_V).rangeRestrict)) ≃* Equiv.Perm (Fin 3))
    (e₂ : ((((L₂ ⊔ (T : Subgroup G)).subgroupOf (L ⊔ (T : Subgroup G))).map
      (barMap (L ⊔ (T : Subgroup G)) V s.normalizes_V).rangeRestrict) ⧸
      pCore 2 (((L₂ ⊔ (T : Subgroup G)).subgroupOf (L ⊔ (T : Subgroup G))).map
      (barMap (L ⊔ (T : Subgroup G)) V s.normalizes_V).rangeRestrict)) ≃* Equiv.Perm (Fin 3))

    (hp : SourceLocalPlanes s e₁ e₂)
    (hpar : ((((L ⊔ (T : Subgroup G)) ⊓ H).subgroupOf (L ⊔ (T : Subgroup G))).map
      (Section07.NaturalAction.permutation (localNaturalSetup d))) = BinaryFlags.H1)
    (hplane : ((L₂ ⊔ (T : Subgroup G)).subgroupOf (L ⊔ (T : Subgroup G))).map
      (Section07.NaturalAction.permutation (localNaturalSetup d)) = BinaryFlags.H2)
    : IsMulCommutative (Source.UL L H V₃) := by
  classical
  by_contra hn
  obtain ⟨eb⟩ := exists_original_bar_equiv_of_parabolic d hpar
  obtain ⟨A,hAP,hA,f,hf,hactor⟩ := exists_original_cubic_actor d hpar
  let ebar := original_bar_equiv d eb
  have h₁ : ∀ g ∈ BinaryFlags.H1, ebar.symm g ∈
      (((sourceOne L T V₁) ⊔ (T : Subgroup G)).subgroupOf (L ⊔ (T : Subgroup G))).map
        (barMap (L ⊔ (T : Subgroup G)) V s.normalizes_V).rangeRestrict := by
    intro g hg
    have he := original_bar_local_image d eb ((sourceOne L T V₁) ⊔ (T : Subgroup G))
    have he' : (((sourceOne L T V₁) ⊔ (T : Subgroup G)).subgroupOf (L ⊔ (T : Subgroup G))).map
        (Section07.NaturalAction.permutation (localNaturalSetup d)) = BinaryFlags.H1 := by
      rw [original_point_parabolic_eq d hH,hpar]
    have he := he.trans he'
    have hm : g ∈ ((((sourceOne L T V₁) ⊔ (T : Subgroup G)).subgroupOf (L ⊔ (T : Subgroup G))).map
        (barMap (L ⊔ (T : Subgroup G)) V d.normalizes_V).rangeRestrict).map ebar.toMonoidHom :=
      he.symm ▸ hg
    obtain ⟨x,hx,hxg⟩ := hm
    have hx' : x = ebar.symm g := ebar.injective (hxg.trans (ebar.apply_symm_apply g).symm)
    exact hx' ▸ hx
  have h₂ : ∀ g ∈ BinaryFlags.H2, ebar.symm g ∈
      ((L₂ ⊔ (T : Subgroup G)).subgroupOf (L ⊔ (T : Subgroup G))).map
        (barMap (L ⊔ (T : Subgroup G)) V s.normalizes_V).rangeRestrict := by
    intro g hg
    have he := (original_bar_local_image d eb (L₂ ⊔ (T : Subgroup G))).trans hplane
    have hm : g ∈ (((L₂ ⊔ (T : Subgroup G)).subgroupOf (L ⊔ (T : Subgroup G))).map
        (barMap (L ⊔ (T : Subgroup G)) V d.normalizes_V).rangeRestrict).map ebar.toMonoidHom :=
      he.symm ▸ hg
    obtain ⟨x,hx,hxg⟩ := hm
    have hx' : x = ebar.symm g := ebar.injective (hxg.trans (ebar.apply_symm_apply g).symm)
    exact hx' ▸ hx
  obtain ⟨E,hVE,⟨t⟩⟩ := source_tensor_section s ebar e₁ e₂ hp h₁ h₂ A
    (hAP.trans inf_le_left) f (fun x => (original_bar_equiv_apply d eb _).trans (hactor x))
  exact nonabelian_exclusion_of_steinberg_sections d h c hH hDH hDg hcentral a e model hn hmark
    A E hAP hA f hf (original_natural_section d A (hAP.trans inf_le_left) f hactor) t
    (original_parabolic_quotient d h eL hpar A hAP f hactor) hVE

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
