module
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.AmbientMovement
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.OriginalComparison

/-!
# Excluding the original two-plane branch by ambient displacement

The original local planes first imply abelianness of U_L using the
checked cubic chief-factor comparison. The full-denominator geometry
constructs the actual S₆ bar and simultaneous parabolic markings, so the
same planes give an equivariant Steinberg quotient of the literal U_L/V.
Mutual normalization bounds the displacement of a barred involution by
five, whereas that quotient requires at least six. AmbientMovement
constructs the involution and supplies the contradiction, retaining the
whole natural or augmentation module and its central covering line.

There is no small-displacement, endpoint image bound, abelianness or
parabolic-marking premise in this application. The actual SourceLocalPlanes
and earlier ordinary setup remain explicit. The plane construction, cover
permutation argument, 13.4.1 application and final strict-denominator
assembly stay with qt-d-138-a6-endgame-source; the earlier ordinary setup
stays with qt-d-138-six-g2-source. This is not the full 13.8.33 theorem.
Source: Aschbacher--Smith, proof of 13.8.33, printed pp.966--967.
-/

public section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
open TransvectionRecognition.Component.ModelExtension A6Endgame.IntersectionBalance
open TransvectionQuotients TransvectionQuotients.FourLocalFactors
open Theory.SpecificGroups.SymmetricSix
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H L₂ : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

/-- The actual two local planes are impossible in the full-denominator branch. -/
theorem original_local_planes_impossible
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalGeometry.CriticalPair L (T : Subgroup G) H V) (hH : H = G₁)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (e : Source.Hstar H ≃* Equiv.Perm (Fin 6))
    (model : CompatibleModel H V₃ V₁ a e)
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
    (hL₂ : L₂ = BarQuotients.sourceResidual L (T : Subgroup G) V₂) :
    False := by
  have hab := span_abelian_of_original_planes d h c hH hDH hDg hcentral a e model
    eL s e₁ e₂ hp hL₂
  obtain ⟨eb⟩ := exists_full_denominators_bar_equiv d h c hDH hDg
  obtain ⟨d',hpar,hplane⟩ := exists_original_parabolic_coordinates d hH eb L₂ hL₂
  let ebar := original_bar_equiv d' eb
  have h₁ : ∀ g ∈ BinaryFlags.H1, ebar.symm g ∈
      (((sourceOne L T V₁) ⊔ (T : Subgroup G)).subgroupOf (L ⊔ (T : Subgroup G))).map
        (barMap (L ⊔ (T : Subgroup G)) V s.normalizes_V).rangeRestrict := by
    intro g hg
    have he := original_bar_local_image d' eb ((sourceOne L T V₁) ⊔ (T : Subgroup G))
    have he' : (((sourceOne L T V₁) ⊔ (T : Subgroup G)).subgroupOf (L ⊔ (T : Subgroup G))).map
        (Section07.NaturalAction.permutation (localNaturalSetup d')) = BinaryFlags.H1 := by
      rw [original_point_parabolic_eq d' hH,hpar]
    have he := he.trans he'
    have hm : g ∈ ((((sourceOne L T V₁) ⊔ (T : Subgroup G)).subgroupOf (L ⊔ (T : Subgroup G))).map
        (barMap (L ⊔ (T : Subgroup G)) V d'.normalizes_V).rangeRestrict).map ebar.toMonoidHom :=
      he.symm ▸ hg
    obtain ⟨x,hx,hxg⟩ := hm
    have hx' : x = ebar.symm g := ebar.injective (hxg.trans (ebar.apply_symm_apply g).symm)
    exact hx' ▸ hx
  have h₂ : ∀ g ∈ BinaryFlags.H2, ebar.symm g ∈
      ((L₂ ⊔ (T : Subgroup G)).subgroupOf (L ⊔ (T : Subgroup G))).map
        (barMap (L ⊔ (T : Subgroup G)) V s.normalizes_V).rangeRestrict := by
    intro g hg
    have he := (original_bar_local_image d' eb (L₂ ⊔ (T : Subgroup G))).trans hplane
    have hm : g ∈ (((L₂ ⊔ (T : Subgroup G)).subgroupOf (L ⊔ (T : Subgroup G))).map
        (barMap (L ⊔ (T : Subgroup G)) V d'.normalizes_V).rangeRestrict).map ebar.toMonoidHom :=
      he.symm ▸ hg
    obtain ⟨x,hx,hxg⟩ := hm
    have hx' : x = ebar.symm g := ebar.injective (hxg.trans (ebar.apply_symm_apply g).symm)
    exact hx' ▸ hx
  let _ := s.normal
  let _ := s.elementary
  obtain ⟨q,hq⟩ := source_tensor_quotient s ebar e₁ e₂ hp h₁ h₂
  exact full_denominators_no_tensor_quotient d h c hH hDH hDg hcentral a e model hab s ebar q hq

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
