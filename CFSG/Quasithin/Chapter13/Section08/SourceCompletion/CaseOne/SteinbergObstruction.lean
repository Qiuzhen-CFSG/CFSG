module
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.NaturalCubicBounds
public import CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis33.ChiefFiltrations.Steinberg

/-!
# Comparing the two original case-one filtrations

The H-side source argument bounds the common local two-core's cubic
length by seven. A compatible natural V section, Steinberg quotient
of U_L/V, and original L-side parabolic quotient force length at least
eight. This contradiction discharges the numerical comparison in the
nonabelian branch without assuming its chief-factor totals.

The three L-side maps remain explicit: this is not yet an unconditional
proof that U_L is abelian. Their construction from the actual 13.8.6(4)
local planes, the later permutation comparison and 13.4.1 application
remain with qt-d-138-a6-endgame-source. The earlier ordinary setup and
markings remain with qt-d-138-six-g2-source. No source denominator is
replaced or assumed strict.

Source: Aschbacher--Smith, Lemma 13.8.33, printed p.967.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
open TransvectionRecognition.Component.ModelExtension A6Endgame.IntersectionBalance
open A6Endgame.ActionAnalysis33.ChiefModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

/-- The natural nonabelian branch is excluded once the original L-side
parabolic marking and the Steinberg quotient from 13.8.6(4) are supplied.
The earlier H-side filtration and the containment U_L≤O₂(LT) are proved
from the ordinary source setup in this application. -/
theorem nonabelian_exclusion_of_steinberg_sections
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalGeometry.CriticalPair L (T : Subgroup G) H V) (hH : H = G₁)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (e : Source.Hstar H ≃* Equiv.Perm (Fin 6))
    (model : CompatibleModel H V₃ V₁ a e)
    (hn : ¬ IsMulCommutative (Source.UL L H V₃))
    (hmark : (Source.starImage H ((L ⊔ (T : Subgroup G)) ⊓ H)).map e.toMonoidHom =
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.H2)
    (A E : Subgroup G) (hAP : A ≤ (L ⊔ (T : Subgroup G)) ⊓ H)
    (hA : IsPGroup 3 A) (f : A →* cubicActor) (hf : Function.Surjective f)
    (v : OppositeSection A ⊥ V f .natural)
    (t : OppositeTensorSection A E (Source.UL L H V₃) f)
    (q : LocalCoreQuotient A ((L ⊔ (T : Subgroup G)).pCoreIn 2)
      ((L ⊔ (T : Subgroup G)) ⊓ H) duadCubicActor
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.H1 (cubicActorEquiv.toMonoidHom.comp f))
    (hVE : V ≤ E) : False := by
  have hupper := nonabelian_parabolic_core_length_le_seven
    d h c hH hDH hDg hcentral a e model hn hmark A hAP hA
  have hULQ : Source.UL L H V₃ ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
    Section07.span_UH_L_le_core (localNaturalSetup d) h
      (show IsMulCommutative (Source.UH H V₃) from inferInstance)
  have hlower := steinberg_filtration_lower_bound A V E (Source.UL L H V₃)
    ((L ⊔ (T : Subgroup G)).pCoreIn 2) ((L ⊔ (T : Subgroup G)) ⊓ H)
    f hf hA (isPGroup_pCoreIn 2 _) v t q hVE hULQ
  omega
end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
