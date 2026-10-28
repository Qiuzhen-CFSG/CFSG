module
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.OriginalStarParabolic
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.SteinbergComparison
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.SteinbergSmallMovement

/-!
# The Steinberg comparison with the original source parabolics

Full denominators construct the symmetric bar. One inner change of the
original V coordinates identifies both literal residual/Sylow parabolics,
and the natural seed identifies the H-side parabolic, so the final
nonabelian-span comparison assumes none of the three exact markings.
The actual source local planes still supply the Steinberg quotient.

The two planes and the earlier ordinary setup remain explicit. Their source construction and the later abelian-span
permutation/13.4.1 argument are retained by qt-d-138-a6-endgame-source;
qt-d-138-six-g2-source owns the earlier ordinary configuration. This is
not yet the full strict-denominator conclusion of 13.8.33.
Source: Aschbacher--Smith, 13.8.33, printed pp.966--967.
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

/-- The two original parabolic markings and the full S₆ bar are derived
from the source flag and full denominators. -/
theorem span_abelian_of_original_local_planes
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
    (hL₂ : L₂ = BarQuotients.sourceResidual L (T : Subgroup G) V₂) :
    IsMulCommutative (Source.UL L H V₃) := by
  obtain ⟨eb⟩ := exists_full_denominators_bar_equiv d h c hDH hDg
  obtain ⟨d',hp₁,hp₂⟩ := exists_original_parabolic_coordinates d hH eb L₂ hL₂
  exact span_abelian_of_source_local_planes d' h c hH hDH hDg hcentral a e model hmark
    eL s e₁ e₂ hp hp₁ hp₂

/-- All three literal parabolic markings and the full bar are constructed.
Only the source local planes and earlier ordinary setup remain explicit. -/
theorem span_abelian_of_original_planes
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
    IsMulCommutative (Source.UL L H V₃) := by
  classical
  by_contra hn
  have hmark := nonabelian_star_parabolic d h c hH hDH hDg hcentral a e model hn
  exact hn (span_abelian_of_original_local_planes d h c hH hDH hDg hcentral a e model
    hmark eL s e₁ e₂ hp hL₂)

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
