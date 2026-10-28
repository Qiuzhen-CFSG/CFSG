module
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.OriginalStrictDenominators
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.TerminalPoint.Ordinary

/-!
# Terminal assembly after the original ordinary denominator exclusion

The maximal ordinary A₆ choice supplies its F.9 pair, ambient centralizer,
full-span abelianness and seed movement. The original 13.8.33 calculation
proves both strict denominators. The existing 13.8.34 and point-parabolic
constructions then give the terminal contradiction, with no case-one,
strictness, rank, movement or point-model callback.

Earlier 13.7.6 supplies the product H=KT and component commutator
generation from the actual component section. The component section,
earlier 13.5.4/13.7.6, plane-module and escape inputs retain their source
producers. The local consumer accepts the actual LocalSetup and thus also
supports the separately guarded earlier-source route. This conditional source application does not assert unconditional
13.8.1 before those inputs are supplied.
Source: Aschbacher--Smith, 13.8.33--34 and the final paragraph of 13.8.1,
printed pp.966--969.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.OrdinaryAssembly
open CriticalGeometry TransvectionRecognition TransvectionRecognition.Component
open TransvectionRecognition.Component.ModelExtension
open Theory.SpecificGroups.SymmetricSix
open Chapter14.Section08.LieTypeBranch
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ K : Subgroup G}

/-- The local source endgame from the actual component section. Earlier
13.7.6 supplies both H=KT and U_H=[U_H,K]; the denominator, rank and
point-parabolic conclusions are all constructed on this same source choice. -/
theorem contradiction_of_original_local_endgame
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hHz : G₁ ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ G₁).Hypothesis)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hcomm : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
    (hgen : G₁ = K ⊔ (sourceOne L T V₁ ⊔ (T : Subgroup G)))
    (hK : (K.subgroupOf G₁).IsCComponent) (hN : (K.subgroupOf G₁).Normal)
    (hqs : IsQuasisimple (Source.starImage G₁ K))
    (hU : IsElementaryAbelian 2 (Source.UH G₁ V₃))
    (a : letI := hU
      SolvableExclusion.Five.StarAction G₁ (Source.UH G₁ V₃) V₁)
    (models : letI := hU
      TerminalRanks.MarkedModels G₁ ((L ⊔ (T : Subgroup G)) ⊓ G₁) V₃ V₁)
    (eK : (K ⧸ pCore 2 K) ≃* A6)
    (hs : letI := hU
      HasSectionModel G₁ V₃ V₁ (A6Endgame.IntersectionBalance.tildeRepresentation G₁ (Source.UH G₁ V₃) V₁ a)
        K (show K ≤ G₁ from hgen ▸ le_sup_left) (BinaryPermutation.alternatingNaturalRepresentation (Fin 6)) eK)
    (earlier1354 : TransvectionParabolic.EarlierCore.Earlier1354 T L V)
    (earlier1376 : TransvectionParabolic.Marking.NaturalSection.Earlier1376 L
      (TransvectionParabolic.EarlierCore.localResidual L V₁)
      T (normalizer (V₁ : Set G)) M V₂ V₃ V₁)
    (chief : TransvectionQuotients.FourLocalFactors.ChiefGeneration.Earlier1376ChiefFactors
      (sourceOne L T V₁) T G₁ M V₃ V₁) : False := by
  let : IsElementaryAbelian 2 (Source.UH G₁ V₃) := hU
  have hres : sourceOne L T V₁ = TransvectionParabolic.EarlierCore.localResidual L V₁ :=
    TransvectionParabolic.EarlierCore.residual_relative_normalizer_eq L T V₁
      T.isPGroup' d.normalizes_L d.line_stable
  have hHz' : G₁ ∈ Source.Hz (TransvectionParabolic.EarlierCore.localResidual L V₁)
      (T : Subgroup G) (normalizer (V₁ : Set G)) M := by
    rw [← hres,← d.first_normalizer]
    exact hHz
  obtain ⟨hUK,_,hprod,_⟩ := earlier1376 G₁ hHz' (d.line_le_uh G₁)
    (A6Endgame.IntersectionBalance.tildeRepresentation G₁ (Source.UH G₁ V₃) V₁ a)
    (TerminalPoint.starAction_isConjugation a) K (show K ≤ G₁ from hgen ▸ le_sup_left)
    hK 6 (by decide) eK hs
  obtain ⟨c,_,_⟩ := (localNaturalSetup d).exists_criticalPair d.abelian_span hF9
  obtain ⟨hstrict,hDstrict⟩ := CaseOne.original_strict_denominators d hF9 c rfl
    hcentral hHz K hK hprod eL models earlier1354 earlier1376 chief hcomm
  exact TerminalPoint.contradiction_of_component_section d hHz hF9 c rfl hgen hK hN hqs
    hcentral hcomm hstrict hDstrict models a hUK eK hs

/-- Terminal assembly for the original maximal ordinary source choice.
The full-denominator case is excluded and both strict denominators are proved;
the literal point-parabolic model is then constructed from the component section.
Only the earlier ordinary setup, classification, escape and module inputs remain. -/
theorem contradiction_of_original_source_endgame
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hm : ⁅G₁.pCoreIn 2,V₂⁆ ≠ ⊥)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (modules : Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u})
    (escape : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hgen : G₁ = K ⊔ (sourceOne L T V₁ ⊔ (T : Subgroup G)))
    (hK : (K.subgroupOf G₁).IsCComponent) (hN : (K.subgroupOf G₁).Normal)
    (hqs : IsQuasisimple (Source.starImage G₁ K))
    (hU : IsElementaryAbelian 2 (Source.UH G₁ V₃))
    (a : letI := hU
      SolvableExclusion.Five.StarAction G₁ (Source.UH G₁ V₃) V₁)
    (models : letI := hU
      TerminalRanks.MarkedModels G₁ ((L ⊔ (T : Subgroup G)) ⊓ G₁) V₃ V₁)
    (eK : (K ⧸ pCore 2 K) ≃* A6)
    (hs : letI := hU
      HasSectionModel G₁ V₃ V₁ (A6Endgame.IntersectionBalance.tildeRepresentation G₁ (Source.UH G₁ V₃) V₁ a)
        K (show K ≤ G₁ from hgen ▸ le_sup_left) (BinaryPermutation.alternatingNaturalRepresentation (Fin 6)) eK)
    (earlier1354 : TransvectionParabolic.EarlierCore.Earlier1354 T L V)
    (earlier1376 : TransvectionParabolic.Marking.NaturalSection.Earlier1376 L
      (TransvectionParabolic.EarlierCore.localResidual L V₁)
      T (normalizer (V₁ : Set G)) M V₂ V₃ V₁)
    (chief : TransvectionQuotients.FourLocalFactors.ChiefGeneration.Earlier1376ChiefFactors
      (sourceOne L T V₁) T G₁ M V₃ V₁) : False := by
  let : IsElementaryAbelian 2 (Source.UH G₁ V₃) := hU
  have hHz := original_six_point_normalizer_mem_Hz d hmax eL escape
  have hspan := original_six_full_span_abelian d hmax eL hm h1332 modules
  let dl := d.toLocalSetup hspan
  have hF9 := original_six_f9_of_source d hmax eL hm hHz
  have hcentral := Section05.AmbientSource.source_parabolic_centralizer d eL
    (hypothesis1221_of_maximal_natural_six d hmax eL)
    (by rwa [← d.first_normalizer])
  have hcomm : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥ := by
    intro he
    apply hm
    apply bot_unique
    rw [commutator_comm] at he
    exact (commutator_mono le_rfl d.plane_le_seed).trans_eq he
  exact contradiction_of_original_local_endgame dl eL hHz hF9 hcentral hcomm
    hgen hK hN hqs hU a models eK hs earlier1354 earlier1376 chief

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.OrdinaryAssembly
