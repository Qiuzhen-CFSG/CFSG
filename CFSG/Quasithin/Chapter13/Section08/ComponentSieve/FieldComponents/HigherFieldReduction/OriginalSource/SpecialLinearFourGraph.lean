module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource.SpecialLinearFour
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives.SourceAlternatives
public import Theory.GroupTheory.PrimeRankAutomorphismOrder

/-!
# The original SL₃(4) graph actor

The genuine Borel has three-rank two and lies in L₁, which excludes the
ordinary A₆ local quotient. The actual covered flag supplies L₀, L₁,+,
their two-core quotients and an inverter in T intersected with L. The
intrinsic marked-Borel calculation classifies that same actor as graph
or graph-field. In the latter case L₀* is central; the original two-core
lies in T and normalizes L₀, so two-perfectness lifts centrality to
H-normalization. The proved original normalizer bound then contradicts
H not contained in M. Thus the graph alternative holds with its full
GL₃ correction and the literal central L₁,+ image.

This discharges the automorphism step in the full SL₃(4) branch. The
natural-plus-dual selection and critical-subspace contradiction remain
with qt-d-138-fields-source. Earlier source inputs retain their producers
through qt-d-1381-source.
Source: Aschbacher–Smith, 13.8.20, printed p.955, using 13.2.2(9)
and the source Borel on pp.954–955.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.SL3FourNaturalDual
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource
open SourceCompletion TransvectionRecognition.Component.ModelExtension
open LinearThree.Geometry.CoveredProduct.ResidualPlacement
open ExceptionalFields.LinearThreeFour.AutomorphismModule
open ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives
open LocalBorel.CentralizingCalculation
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}

/-- The original local action is covered and its actual inverter acts by
an inner-diagonal correction of the graph automorphism on the full SL₃(4).
The scalar center and the residual of the Borel commutator are retained. -/
theorem source_specialLinearThree_graph
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (eK : Source.starImage H K ≃* SL) :
    letI : (Source.starImage H K).Normal :=
      c.component.normal.map _ (QuotientGroup.mk'_surjective _)
    ∃ (_ : (L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms)
      (t : ((T : Subgroup G) ⊓ L : Subgroup G)),
      InvertsTwoCoreQuotient (plus L T V₁) t.val ∧
      GraphAlternative H K L T V₁ eK
        (QuotientGroup.mk' (pCore 2 H)
          ⟨t.val,c.component.local_overgroup.1.2 (mem_sup_right t.property.1)⟩) := by
  let : (K.subgroupOf H).Normal := c.component.normal
  let : (Source.starImage H K).Normal :=
    c.component.normal.map _ (QuotientGroup.mk'_surjective _)
  let model : TorusModels.Assembly.Model.{u,0} (Source.starImage H K) 2 false true :=
    .specialLinearThree F sl3Field_card eK
      (Matrix.PSL3.OuterSolvable.standard_eq_top_of_two_power_card F (by decide) sl3Field_card)
  let i := sourceInput c (by decide : 1 < 2) model
  have hLK := source_specialLinearThree_containment c eK
  rcases local_quotient_alternatives c.localSetup with ⟨e,he⟩ | ⟨e,he⟩
  · obtain ⟨a⟩ := LocalFitting.ordinary_natural c.localSetup e he
    let d := i.ordinarySourceContext a
    have hBM : SourceMarking.sourceBorel H K T eK d.component_le d.sylow_H ≤ M := by
      rw [source_specialLinearThree_borel_eq]
      exact d.borel_in_M
    have hBL := SourceMarking.sourceBorel_le_one H K T eK d.component_le d.sylow_H
      L M V₁ hBM d.theta
    have hr := primeRank_mono 3 hBL
    rw [SourceMarking.sourceBorel_threeRank] at hr
    have hr1 : primeRank 3 (one L T V₁) ≤ 1 := by
      rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide)
        (pCore 2 (one L T V₁)) pCore_isPGroup]
      apply primeRank_le_of_card_le_prime_pow
      rw [LocalFitting.ordinary_core_card c.localSetup ⟨e⟩]
      norm_num
    omega
  · obtain ⟨a⟩ := local_covered_flag_model c.localSetup e he
    have hfactor := CoverFactorization.source_factorization a
    let d := i.coveredSourceContext a hfactor
    have hBM : SourceMarking.sourceBorel H K T eK d.component_le d.sylow_H ≤ M := by
      rw [source_specialLinearThree_borel_eq]
      exact d.borel_in_M
    have hBL := SourceMarking.sourceBorel_le_one H K T eK d.component_le d.sylow_H
      L M V₁ hBM d.theta
    obtain ⟨t,hinv,_,_,_,_⟩ :=
      Covered.SourceCalculation.exists_marked_inverter d a hfactor
    let tH : H := ⟨t.val,d.T_le_H t.property.1⟩
    let m := SourceMarking.marking H K T eK d.component_le d.sylow_H L V₁ hLK
      a.normalizes_L a.line_stable hfactor a.zero_core_card (a.plus_core_card hfactor)
      hBL tH t.property.1 t.property.2
      ((Covered.inversion_iff _ ⟨t.val,T_normalizes_plus L T V₁
        a.normalizes_L a.line_stable t.property.1⟩).mp hinv)
    have hB : modelImage H K (one L T V₁) eK = normalizer (m.factors.sylow : Set SL) := by
      change modelImage H K (one L T V₁) eK =
        normalizer (SourceMarking.sourceSylow H K T eK d.sylow_H : Set SL)
      unfold modelImage
      rw [SourceMarking.one_star_eq_borel H K T eK d.component_le d.sylow_H L V₁ hLK
        a.normalizes_L a.line_stable hfactor a.zero_core_card (a.plus_core_card hfactor) hBL,
        modelBorel,comap_map_eq_self_of_injective (sourceActor_injective H K eK)]
    rcases IntrinsicAction.alternatives m.factors
        (Matrix.PSL3.OuterSolvable.standard_eq_top_of_two_power_card F (by decide) sl3Field_card) with
      ⟨g,hg,hX,hres⟩ | ⟨_,_,_,_,hZ,_⟩
    · have hXK := (plus_le_one L T V₁ a.line_stable).trans hLK
      have hstar := starImage_eq_center_of_modelImage H K (plus L T V₁) eK
        (SourceMarking.starImage_mono H hXK) (m.plus_eq.symm.trans hX)
      exact ⟨e,t,hinv,g,hg,source_graph_relation H K eK _ g hg,hstar,hB ▸ hres⟩
    · have hZK := (LocalAction.zero_le_one_of_factorization L T V₁ hfactor).trans hLK
      have hstar := starImage_eq_center_of_modelImage H K (zero L) eK
        (SourceMarking.starImage_mono H hZK) (m.zero_eq.symm.trans hZ)
      have hQ : Source.QH H ≤ normalizer (zero L : Set G) :=
        (c.f9 H c.component.local_overgroup).QH_le_T.trans
          (c.localSetup.normalizes_L.trans (normalizer_le_zero_normalizer L))
      exact (graph_field_contradiction H K (zero L) M (hZK.trans d.component_le)
        (zero_isPPerfect L) hQ hstar
        (SolvableSource.covered_normalizer_source c.localSetup c.maximal ⟨e⟩)
        c.component.local_overgroup.2.2).elim

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource
