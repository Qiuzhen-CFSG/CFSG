module
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.OriginalCoverRecognition

/-!
# The fifteen-pair quotient on the whole original module

The cover recognition proves U₀ = U_L. Transport the previously constructed
permutation surjection along that equality onto the literal U_L/V, together
with its conjugation formula. The actor remains LT/C_LT(V); its actual
six-letter permutation map is bijective. The constant covering line and
central kernel are retained throughout the transport.

This supplies the whole permutation-module input in the next paragraph of
Aschbacher--Smith, proof of 13.8.33, printed p.967. It does not yet identify
U_L/V as the four-dimensional natural module or its five-dimensional cover.
That comparison, the 13.4.1 application, strict denominators and 13.8.34
remain with the endgame source assembly. The earlier ordinary setup and
13.5.4/13.7.6 assumptions are unchanged.
-/

public section
open Subgroup Representation
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
open TransvectionRecognition.Component.ModelExtension A6Endgame.IntersectionBalance
open TransvectionQuotients TransvectionQuotients.FourLocalFactors TransvectionParabolic FiveSeed
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}

/-- A fifteen-pair quotient on the whole U_L/V, with the original barred
actor and its centralizer kernel. -/
@[expose] def CoverPermutationData.WholeSection
    (p : CoverPermutationData L H K (T : Subgroup G) (sourceOne L T V₁) V₃ V) : Prop :=
  let _ := p.actor_normal
  ∃ hUL : L ⊔ (T : Subgroup G) ≤ normalizer (Source.UL L H V₃ : Set G),
    ∃ hN : (V.subgroupOf (Source.UL L H V₃)).Normal,
      let _ := hN
      ∃ hE : IsElementaryAbelian 2 (Source.ULsection L H V₃ V),
        let _ := hE
        ∃ ρ : Representation (ZMod 2)
            ((L ⊔ (T : Subgroup G) : Subgroup G) ⧸ actorKernel (L ⊔ (T : Subgroup G)) V)
            (Additive (Source.ULsection L H V₃ V)),
          SectionConjugationAlong (L ⊔ (T : Subgroup G)) (Source.UL L H V₃) V
            (QuotientGroup.mk' (actorKernel (L ⊔ (T : Subgroup G)) V)) hUL ρ ∧
          ∃ q : Representation.IntertwiningMap
            (BinaryPermutation.SixPairsQuadratic.action.comp p.permutation) ρ,
            Function.Surjective q

/-- Transfer the literal conjugation action and surjection along the proved
span equality. No isomorphism of an unconnected model is substituted. -/
theorem CoverPermutationData.wholeSection_of_eq
    (p : CoverPermutationData L H K (T : Subgroup G) (sourceOne L T V₁) V₃ V)
    (heq : Source.U0 L H K V₃ = Source.UL L H V₃) : p.WholeSection := by
  let _ := p.actor_normal
  have transport (U : Subgroup G) (hU : U = Source.U0 L H K V₃) :
      ∃ hUL : L ⊔ (T : Subgroup G) ≤ normalizer (U : Set G),
        ∃ hN : (V.subgroupOf U).Normal,
          let _ := hN
          ∃ hE : IsElementaryAbelian 2 (U ⧸ V.subgroupOf U),
            let _ := hE
            ∃ ρ : Representation (ZMod 2)
                ((L ⊔ (T : Subgroup G) : Subgroup G) ⧸ actorKernel (L ⊔ (T : Subgroup G)) V)
                (Additive (U ⧸ V.subgroupOf U)),
              SectionConjugationAlong (L ⊔ (T : Subgroup G)) U V
                (QuotientGroup.mk' (actorKernel (L ⊔ (T : Subgroup G)) V)) hUL ρ ∧
              ∃ q : Representation.IntertwiningMap
                (BinaryPermutation.SixPairsQuadratic.action.comp p.permutation) ρ,
                Function.Surjective q := by
    subst U
    exact ⟨p.normalizes,p.normal,p.elementary,p.action,p.conjugation,p.pair_surjection⟩
  exact transport (Source.UL L H V₃) heq.symm

variable [IsElementaryAbelian 2 (Source.UH H V₃)]

/-- The actual whole L-span quotient is a quotient of the fifteen-pair
permutation module. Both the span equality and faithful S₆ actor are proved. -/
theorem full_denominators_whole_permutation
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalGeometry.CriticalPair L (T : Subgroup G) H V)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
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
    (chief : ChiefGeneration.Earlier1376ChiefFactors (sourceOne L T V₁) T G₁ M V₃ V₁) :
    IsMulCommutative (Source.UL L H V₃) ∧ V < Source.UL L H V₃ ∧
    ∃ p : CoverPermutationData L H K (T : Subgroup G) (sourceOne L T V₁) V₃ V,
      (let _ := p.actor_normal; Function.Bijective p.permutation) ∧ p.WholeSection := by
  have heq := full_denominators_U0_eq_UL d h c hDH hDg hH hcentral hHz K hK hprod
    eL a e model earlier1354 earlier1376 chief
  obtain ⟨hab,p,hlt,_,_,_,_,_,hsur,_⟩ := full_denominators_cover_permutation d h c hDH hDg hH
    hcentral hHz K hK hprod eL a e model earlier1354 earlier1376 chief
  exact ⟨hab,heq ▸ hlt,p,⟨p.faithful,hsur⟩,p.wholeSection_of_eq heq⟩

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
