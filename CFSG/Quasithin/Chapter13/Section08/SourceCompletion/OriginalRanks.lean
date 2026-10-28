module
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.OriginalStrictDenominators

/-!
# All clauses of original 13.8.34

The endpoint image acts quadratically on the literal V_H/U_H section.
The marked permutation-quotient theorem therefore prevents it from
containing the two-core of the parabolic residual. This retains the
noncontainment clause as well as the final rank bound, with each H-conjugate
and each quotient map specified explicitly.

The second application constructs both strict denominators by 13.8.33 and
uses the existing reversal argument to obtain the line containments and
rank-one image on the unchanged critical pair. No denominator inequality,
index comparison or numerical rank conclusion is an input. Earlier ordinary
setup, component and module premises remain for their source producers.
Source: Aschbacher--Smith, 13.8.34(1)--(3), printed p.968.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.TerminalRanks
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open TransvectionRecognition.Component.ModelExtension
open scoped IsMulCommutative Pointwise
open CriticalGeometry CriticalGeometry.Reorientation
open A6Endgame A6Endgame.IntersectionBalance
open Theory.SpecificGroups.SymmetricSix
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}

/-- The noncontainment clause of 13.8.34(3) at every H-conjugate of the
original endpoint group. The parabolic residual and quotient map are literal. -/
theorem original_core_not_le_endpoint
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
    (models : letI := d.uh_elementary hHz
      MarkedModels H ((L ⊔ (T : Subgroup G)) ⊓ H) V₃ V₁)
    (c : CriticalPair L (T : Subgroup G) H V) (g : H) :
    ¬ (Source.starImage H ((pResidual 2 ↥(H ⊓ (L ⊔ (T : Subgroup G)))).map
      (H ⊓ (L ⊔ (T : Subgroup G))).subtype)).pCoreIn 2 ≤
        Source.starImage H (c.Vgamma.map (MulAut.conj (g : G)).toMonoidHom) := by
  classical
  let _ := Fintype.ofFinite (Source.Hstar H ⧸ Source.starImage H (H ⊓ (L ⊔ (T : Subgroup G))))
  let : IsElementaryAbelian 2 V := hF9.elementary
  let : IsElementaryAbelian 2 (Source.UH H V₃) := d.uh_elementary hHz
  let : IsElementaryAbelian 2 (conjugateSpanBy V G₁) := d.span_elementary
  let : IsElementaryAbelian 2 (Source.VH H V) :=
    IsElementaryAbelian.of_le (conjugateSpanBy_mono le_rfl hHz.2.1)
  have hflag : normalizer (V₁ : Set G) ⊓ normalizer (V₃ : Set G) ≤ M := by
    have hh := Section05.PointAction.normalizer_intersection_source (localNaturalSetup d) hcentral
    simpa only [d.first_normalizer] using hh.trans inf_le_left
  have hnc := Section07.source_noncentral_VH_quotient_of_earlier_geometry
    (localNaturalSetup d) hF9 inferInstance hHz.2.1 hHz.2.2 hflag hcomm
  obtain ⟨b,hb⟩ := Terminal.exists_rank_section_action d hF9 hHz.2.1 hcomm
  let σ := SolvableExclusion.Three.Supercritical.Offenders.linearAction b
  have hquadratic := Terminal.rank_section_quadratic d hF9 b c g
  let R := (pResidual 2 ↥(H ⊓ (L ⊔ (T : Subgroup G)))).map
    (H ⊓ (L ⊔ (T : Subgroup G))).subtype
  let Vα := c.Vgamma.map (MulAut.conj (g : G)).toMonoidHom
  have hnorm : H ⊓ (L ⊔ (T : Subgroup G)) ≤ normalizer (V : Set G) :=
    inf_le_right.trans d.normalizes_V
  obtain ⟨a,hm⟩ := models
  rcases hm with ⟨e,he⟩ | ⟨e,he,_⟩
  · have he' : (Source.starImage H (H ⊓ (L ⊔ (T : Subgroup G)))).map
        e.toMonoidHom = a6SynthemeStabilizer := by simpa only [inf_comm H] using he
    obtain ⟨f,hf,heq,hnc',_⟩ := MarkedQuotient.alternating_source H
      (L ⊔ (T : Subgroup G)) V V₃ e he' d.seed_le (Comparison.local_seed_index d)
      hnc hnorm σ hb
    have hcore := SourceResidual.alternating_core H (L ⊔ (T : Subgroup G)) R rfl e he'
    exact MarkedQuotient.alternating_core_not_le H R Vα e σ f hf heq hnc' hcore hquadratic
  · have he' : (Source.starImage H (H ⊓ (L ⊔ (T : Subgroup G)))).map
        e.toMonoidHom = BinaryFlags.H2 := by simpa only [inf_comm H] using he
    obtain ⟨f,hf,heq,hnc',_⟩ := MarkedQuotient.symmetric_source H
      (L ⊔ (T : Subgroup G)) V V₃ e he' d.seed_le (Comparison.local_seed_index d)
      hnc hnorm σ hb
    have hcore := SourceResidual.symmetric_core H (L ⊔ (T : Subgroup G)) R rfl e he'
    exact MarkedQuotient.symmetric_core_not_le H R Vα e σ f hf heq hnc' hcore hquadratic

/-- All three clauses of original 13.8.34, with both strict denominators
constructed from the original ordinary hypotheses rather than assumed. -/
theorem original_rank_and_lines
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalPair L (T : Subgroup G) H V) (hH : H = G₁)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (K : Subgroup G) (hK : (K.subgroupOf H).IsCComponent)
    (hN : (K.subgroupOf H).Normal) (hqs : IsQuasisimple (Source.starImage H K))
    (hgen : H = K ⊔ (sourceOne L T V₁ ⊔ (T : Subgroup G)))
    (hprod : (H : Set G) = (K : Set G) * (T : Set G))
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (models : letI := d.uh_elementary hHz
      MarkedModels H ((L ⊔ (T : Subgroup G)) ⊓ H) V₃ V₁)
    (earlier1354 : TransvectionParabolic.EarlierCore.Earlier1354 T L V)
    (earlier1376 : TransvectionParabolic.Marking.NaturalSection.Earlier1376 L
      (TransvectionParabolic.EarlierCore.localResidual L V₁)
      T (normalizer (V₁ : Set G)) M V₂ V₃ V₁)
    (chief : TransvectionQuotients.FourLocalFactors.ChiefGeneration.Earlier1376ChiefFactors
      (sourceOne L T V₁) T G₁ M V₃ V₁)
    (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥) :
    (c.Aone V₁ ≤ Source.UH H V₃ ∧ V₁ ≤ c.Ugamma V₃) ∧
    rank (Source.starImage H (c.Ugamma V₃)) = 1 ∧
    (∀ g : H, ¬ (Source.starImage H ((pResidual 2 ↥(H ⊓ (L ⊔ (T : Subgroup G)))).map
      (H ⊓ (L ⊔ (T : Subgroup G))).subtype)).pCoreIn 2 ≤
        Source.starImage H (c.Vgamma.map (MulAut.conj (g : G)).toMonoidHom)) ∧
    rank (Source.starImage H c.Vgamma) ≤ 2 := by
  let : IsElementaryAbelian 2 (Source.UH H V₃) := d.uh_elementary hHz
  obtain ⟨hstrict,hDstrict⟩ := CaseOne.original_strict_denominators d h c hH hcentral
    hHz K hK hprod eL models earlier1354 earlier1376 chief hcomm
  obtain ⟨hline,hrank,hsmall⟩ := rank_and_lines_of_source d hHz h hgen hK hN hqs
    hcentral hcomm models c hstrict hDstrict
  exact ⟨hline,hrank,original_core_not_le_endpoint d hHz h hcentral hcomm models c,hsmall⟩
end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.TerminalRanks
