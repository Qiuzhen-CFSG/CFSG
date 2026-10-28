module
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.OriginalCentralFiltration
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.Overgroup.Symmetry.Denominators
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.TerminalPoint.Coordinates
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.TerminalRanks
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Localization.EndpointGeometry.SourceActions

/-!
# Strict denominators for the original ordinary A₆ critical pair

For the symmetric-six actor, the retained natural or full-cover coordinates
construct the literal model needed for denominator symmetry. If either
denominator were full, symmetry would make both full, contradicting the
same-actor filtration calculation. For the alternating-six actor, the
faithful original quotient action admits no transvection; the F.9 geometry
then forces both denominators proper directly.

The combined application retains the original critical pair, central kernels,
parabolic markings and earlier-source assumptions. It removes both strictness
premises from the terminal source application in OriginalTerminal.
Source: Aschbacher--Smith, 13.8.7, 13.8.33, printed pp.948--949,966--968.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
open Subgroup Representation
open scoped IsMulCommutative
open TransvectionRecognition.Component.ModelExtension A6Endgame.IntersectionBalance
open CriticalGeometry CriticalGeometry.AsymmetricPair
open SolvableExclusion.Five.Localization.EndpointGeometry
variable {G : Type*} [Group G] {H V₃ V₁ : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

private noncomputable def natural_center_model
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (e : Source.Hstar H ≃* Equiv.Perm (Fin 6))
    (F : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6))
    (hF : ∀ g v, F (tildeRepresentation H _ V₁ a g v) =
      BinaryPermutation.naturalRepresentation (Fin 6) (e g) (F v)) :
    (centerAction a).Model (BinaryPermutation.naturalRepresentation (Fin 6)) := by
  let f : Source.Hstar H →* (centerAction a).action.range := a.action.codRestrict _ (by
    intro g
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) g
    exact ⟨x,rfl⟩)
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      apply e.injective
      apply BinaryPermutation.naturalRepresentation_injective (Fin 6) (by decide)
      apply LinearMap.ext
      intro v
      obtain ⟨w,rfl⟩ := F.surjective v
      rw [← hF,← hF]
      apply congrArg F
      exact congrArg (fun g : (centerAction a).action.range => Additive.ofMul (g.val w.toMul)) hxy
    · rintro ⟨x,hx⟩
      obtain ⟨g,rfl⟩ := hx
      exact ⟨QuotientGroup.mk' (pCore 2 H) g,rfl⟩
  let E := MulEquiv.ofBijective f hf
  refine ⟨E.symm.trans e,F,?_⟩
  intro x w
  obtain ⟨g,rfl⟩ := E.surjective x
  change F (Additive.ofMul (a.action g w)) =
    BinaryPermutation.naturalRepresentation (Fin 6) (e (E.symm (E g))) (F (Additive.ofMul w))
  rw [E.symm_apply_apply]
  exact hF g (Additive.ofMul w)

/-- Original 13.8.7 on the actual symmetric-six section. All model premises
of the source symmetry theorem are constructed from the retained coordinates. -/
theorem original_symmetric_strict_iff [Finite G]
    {T : Sylow 2 G} {L V V₂ M G₁ : Subgroup G}
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalPair L (T : Subgroup G) H V) (hH : H = G₁)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (e : Source.Hstar H ≃* Equiv.Perm (Fin 6))
    (model : CompatibleModel H V₃ V₁ a e) :
    Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) < Source.UH H V₃ ↔
      Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ < c.Ugamma V₃ := by
  have hlt : V₁ < V₂ := lt_of_le_of_ne d.line_le_plane (by
    intro he
    have hc := d.line_card
    rw [he,d.plane_card] at hc
    omega)
  obtain ⟨b,hb,hbZ⟩ := SetLike.exists_of_lt hlt
  let bU : Source.UH H V₃ := ⟨b,(d.plane_le_seed.trans (le_conjugateSpanBy V₃ H)) hb⟩
  apply ComponentSieve.SixAndG2.Overgroup.Symmetry.source_strict_iff d hHz h c hH
    hcentral (centerAction a) bU hb hbZ
  intro _
  rcases model.action_cases H V₃ V₁ a e with ⟨F,hF⟩ | ⟨F,hF⟩
  · exact Or.inl (Or.inr (Or.inl ⟨natural_center_model a e F hF⟩))
  · right
    exact ⟨{
      groupEquiv := e
      linearEquiv := F
      normalizes := le_normalizer_conjugateSpanBy V₃ H
      intertwines := fun g u =>
        (hF (QuotientGroup.mk' (pCore 2 H) g)
          (Additive.ofMul (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u))).symm.trans
          (congrArg (fun x => F (Additive.ofMul x)) (a.conjugation g u)) }⟩
end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne

namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
open Subgroup Representation
open scoped IsMulCommutative commutatorElement Pointwise
open TransvectionRecognition.Component.ModelExtension A6Endgame.IntersectionBalance
open TransvectionQuotients TransvectionQuotients.FourLocalFactors TransvectionParabolic FiveSeed
open A6Endgame.ActionAnalysis33.ChiefModels
open CriticalGeometry
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

/-- Both literal critical denominators are proper, using original symmetry
and the constructed full-denominator contradiction. -/
theorem original_symmetric_strict_denominators
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalGeometry.CriticalPair L (T : Subgroup G) H V)
    (hH : H = G₁)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (K : Subgroup G) (hK : (K.subgroupOf H).IsCComponent)
    (hprod : (H : Set G) = (K : Set G) * (T : Set G))
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (e : Source.Hstar H ≃* Equiv.Perm (Fin 6))
    (model : CompatibleModel H V₃ V₁ a e)
    (earlier1354 : EarlierCore.Earlier1354 T L V)
    (earlier1376 : Marking.NaturalSection.Earlier1376 L (EarlierCore.localResidual L V₁)
      T (normalizer (V₁ : Set G)) M V₂ V₃ V₁)
    (chief : ChiefGeneration.Earlier1376ChiefFactors (sourceOne L T V₁) T G₁ M V₃ V₁)
    (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥) :
    Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) < Source.UH H V₃ ∧
      Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ < c.Ugamma V₃ := by
  have hi := original_symmetric_strict_iff d hHz h c hH hcentral a e model
  have hs : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) < Source.UH H V₃ := by
    by_contra hn
    have hDH := eq_of_le_of_not_lt (commutatorPreimage_le _ _ _) hn
    have hDg := eq_of_le_of_not_lt (commutatorPreimage_le _ _ _) (fun hs => hn (hi.mpr hs))
    exact full_denominators_false d h c hDH hDg hH hcentral hHz
      K hK hprod eL a e model earlier1354 earlier1376 chief hcomm
  exact ⟨hs,hi.mp hs⟩
end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne

namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
open Subgroup Representation
open scoped IsMulCommutative
open TransvectionRecognition TransvectionRecognition.Component.ModelExtension
open A6Endgame.IntersectionBalance CriticalGeometry CriticalGeometry.AsymmetricPair
open CriticalGeometry.SectionActions
open SolvableExclusion.Five.Localization.EndpointGeometry
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

/-- An alternating-six star group has no nontrivial transvection in its
faithful literal action. The original F.9 actors therefore force both denominators
proper, without any additional module or point-model assumption. -/
theorem original_alternating_strict_denominators
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalPair L (T : Subgroup G) H V)
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (e : Source.Hstar H ≃* alternatingGroup (Fin 6)) :
    Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) < Source.UH H V₃ ∧
      Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ < c.Ugamma V₃ := by
  let ρ := tildeRepresentation H (Source.UH H V₃) V₁ a
  have hf : Function.Injective ρ := faithful_of_centralizer_le_core ρ
    (TerminalPoint.starAction_isConjugation a)
    ((f9_commutatorPreimage_eq _ h H le_rfl).le.trans inf_le_right)
  have hz : H ≤ normalizer (V₁ : Set G) :=
    h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)
  have hQ := h.commutator_UH_QH_le_point
  have hgeo := local_earlierGeometry d h c
  have hcentral : ⁅Source.VH H V, Source.HC H V₃⁆ ≤ V₁ := by
    rw [commutator_comm]
    exact Section07.centralizer_UH_commutator (localNaturalSetup d) h
  apply c.strict_denominators_of_no_uStar_transvection V₃ V₁ d.seed_le hz hQ hgeo
    d.line_card hcentral (f9_commutator_not_le_Aone _ h c hgeo.length)
  rw [← starAction_eq_uStar a hz hQ]
  intro g hn ht
  have hd := LinearEquiv.mem_dilatransvections_iff_finrank.mp
    (LinearEquiv.transvections_subset_dilatransvections ht)
  have hd' : Module.finrank (ZMod 2) (LinearMap.range
      ((ρ.comp e.symm.toMonoidHom) (e g) - LinearMap.id)) ≤ 1 := by
    have heq : (ρ.comp e.symm.toMonoidHom) (e g) =
        (binaryLinear (a.action g)).toLinearMap := by
      change ρ (e.symm (e g)) = _
      rw [e.symm_apply_apply]
      rfl
    exact heq.symm ▸ hd
  have he := Representation.SixLetterTransvections.alternating_eq_one_of_displacement_le_one
    (ρ.comp e.symm.toMonoidHom) (hf.comp e.symm.injective) (e g) hd'
  have hg : g = 1 := e.injective (he.trans (map_one e).symm)
  exact hn (hg ▸ map_one a.action)
end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne

namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
open Subgroup Representation
open scoped IsMulCommutative commutatorElement Pointwise
open TransvectionRecognition.Component.ModelExtension A6Endgame.IntersectionBalance
open TransvectionQuotients TransvectionQuotients.FourLocalFactors TransvectionParabolic FiveSeed
open A6Endgame.ActionAnalysis33.ChiefModels
open CriticalGeometry
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

/-- The original 13.8.33 conclusion for either surviving marked ordinary
actor. Both denominators are proved strict on the unchanged critical pair. -/
theorem original_strict_denominators
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalGeometry.CriticalPair L (T : Subgroup G) H V)
    (hH : H = G₁)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (K : Subgroup G) (hK : (K.subgroupOf H).IsCComponent)
    (hprod : (H : Set G) = (K : Set G) * (T : Set G))
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (models : TerminalRanks.MarkedModels H ((L ⊔ (T : Subgroup G)) ⊓ H) V₃ V₁)
    (earlier1354 : EarlierCore.Earlier1354 T L V)
    (earlier1376 : Marking.NaturalSection.Earlier1376 L (EarlierCore.localResidual L V₁)
      T (normalizer (V₁ : Set G)) M V₂ V₃ V₁)
    (chief : ChiefGeneration.Earlier1376ChiefFactors (sourceOne L T V₁) T G₁ M V₃ V₁)
    (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥) :
    Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) < Source.UH H V₃ ∧
      Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ < c.Ugamma V₃ := by
  obtain ⟨a,models⟩ := models
  rcases models with ⟨e,_⟩ | ⟨e,_,model⟩
  · exact original_alternating_strict_denominators d h c a e
  · exact original_symmetric_strict_denominators d h c hH hcentral hHz K hK hprod
      eL a e model earlier1354 earlier1376 chief hcomm
end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
