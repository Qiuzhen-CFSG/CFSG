module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.Solvable.Selected
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.D213Source
public import Theory.GroupTheory.SylowNormalizerOvergroup

/-!
# The full solvable-overgroup contradiction in 13.8.13

Choose a minimal solvable overgroup in the original Hz family. The actual
quotient action and critical pair are constructed internally. Both
three-primary alternatives contradict the native natural-module geometry;
the resulting five-primary subgroup contradicts the proved two-support
localization. The two universal D.2.13 inputs are instantiated by their
source theorems. No model recognition or selected geometry is a premise.

The final universal conclusion is exactly H ≤ M for every solvable H
between L1 T and G1. Its earlier inputs are F.9 applicability, 13.2.2(9),
13.5.5, 13.7.3(6), 13.7.7 and the universal 13.3.9 residual theorem.
Source: Aschbacher--Smith, 13.8.13, printed pp.950--951.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.SolvableSource
open TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree
open Geometry.CoveredProduct.ResidualPlacement
open CriticalGeometry CriticalGeometry.Reorientation
open SolvableExclusion Three.Supercritical.Offenders
open Five.Localization.EndpointGeometry
universe u
variable {G:Type u} [Group G] [Finite G]
 {T:Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H:Subgroup G}
 (d:LocalSetup T L V V₁ V₂ V₃ M G₁)
 (hH:Minimal (·∈Source.Hz (one L T V₁) T G₁ M) H)
 (hF9:(Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
 (hN:Nonempty ((L⧸pCore 2 L)≃*Atlas.Codes.HexEvenAutomorphisms)→normalizer (zero L:Set G)≤M)
 (hflag:normalizer (V₁:Set G)⊓normalizer (V₃:Set G)≤M⊓normalizer (V:Set G))
 (hdisp:V₁=⁅V₃,Source.QH H⁆)
 (hnoncentral:¬⁅Source.VH H V,H⁆≤Source.UH H V₃)
 (hsource:Residual.Source1339 L (one L T V₁) (plus L T V₁) T M V V₁)
include d hH hF9 hN hflag hdisp hnoncentral hsource

theorem minimal_not_solvable : ¬Group.IsSolvable H := by
  intro hs
  let : IsElementaryAbelian 2 (Source.UH H V₃):=d.uh_elementary hH.prop
  let : IsElementaryAbelian 2 (conjugateSpanBy V G₁):=d.span_elementary
  let : IsElementaryAbelian 2 (Source.VH H V):=
    IsElementaryAbelian.of_le (conjugateSpanBy_mono le_rfl hH.prop.2.1)
  obtain ⟨a,c,g,hcomp,hquad⟩:=exists_selected d hH.prop hF9 hN hflag hdisp hnoncentral hs
  have h135:Five.TransvectionComponentConclusion a T := by
    intro t hn ht
    exact (no_star_transvection d hH.prop hF9 hN hflag hdisp hs a t hn ht).elim
  have hmodels:=local_flag_alternatives d
  have hfactor:=fun W₁ W₃ (a:LocalAction.NaturalSetup L (T:Subgroup G) V W₁ W₃)=>CoverFactorization.source_factorization a
  have hgen:=TransvectionRecognition.Solvable.seed_generation_of_core_displacement d hH.prop hmodels hfactor hdisp
  have hseed:V₃≤⁅V₃,one L T V₁⁆⊔V₁ := hgen.le.trans le_sup_left
  obtain ⟨h,hplace,⟨reduced⟩⟩:=OddReduction.five_of_selected_source d
    d213PrimeRestriction_source hF9 g hH hs hsource a hquad h135 hseed
  have hLM:L⊔(T:Subgroup G)≤M := by
    rw [d.local_normalizer]
    exact sup_le L.le_normalizer d.normalizes_L
  have hgeo:=local_earlierGeometry d hF9
  have src:Five.Localization.EndpointGeometry.SourceInputs c V₃ V₁ (one L T V₁) G₁ M := {
    seed_le:=d.seed_le
    V_sylow:=hF9.V_le_T
    line_seed:=d.line_le_plane.trans d.plane_le_seed
    line_card:=d.line_card
    line_normalized:=d.first_normalizer ▸ le_rfl
    flag_index:=Comparison.local_seed_index d
    flag_normalized:=inf_le_left.trans d.normalizes_V
    base_edge:=Comparison.local_edge d hF9
    base_in_M:=sup_le ((one_le L T V₁).trans (inf_le_left.trans hLM)) (le_sup_right.trans hLM)
    noncentral:=hnoncentral
    centralizer_bound:=by
      rw [commutator_comm]
      exact Section07.centralizer_UH_commutator (localNaturalSetup d) hF9
    geometry:=hgeo
    endpoint_core:=by
      intro c'
      have hh:=(f9_endpoint_edge_cores _ hF9 c' (hgeo c').length).1
      change Source.VH H V≤(vertexGroup _ _ _ c'.previous⊓vertexGroup _ _ _ c'.gamma).pCoreIn 2 at hh
      rwa [inf_comm] at hh
    critical_commutator:=fun c'=>f9_commutator_not_le_Aone _ hF9 c' (hgeo c').length
    selected_rank:=hcomp }
  exact Five.reducedFive_false_of_action Five.sourceD213PrimeInput_source reduced c a
    d.counterexample.qtke.quasithin hH hs src (OddReduction.source_kernel hF9)
    (Q_of_quadraticMember _ hquad)
    (fun ht=>(no_center_transvection d hH.prop hF9 hN hflag hdisp hs a ht).elim)
    ⟨h,hplace⟩

omit hH hF9 hdisp hnoncentral in
theorem solvable_overgroup_le
    (hF9all:∀J∈Source.Hz (one L T V₁) T G₁ M,
      (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
    (hdispall:∀J∈Source.Hz (one L T V₁) T G₁ M,V₁=⁅V₃,Source.QH J⁆)
    (hnoncentralall:∀J∈Source.Hz (one L T V₁) T G₁ M,
      ¬⁅Source.VH J V,J⁆≤Source.UH J V₃)
    (hLT:one L T V₁⊔(T:Subgroup G)≤H) (hHG:H≤G₁)
    (hs:Group.IsSolvable H) : H≤M := by
  by_contra hout
  have hline:V₁≠⊥ := by
    intro he
    have hc:=d.line_card
    rw [he,Nat.card_unique] at hc
    contradiction
  let : IsElementaryAbelian 2 V:=local_elementary d
  let : IsElementaryAbelian 2 V₁:=IsElementaryAbelian.of_le (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le))
  have hp:IsPGroup 2 V₁:=IsElementaryAbelian.isPGroup 2 V₁
  have hVT:V₁≤(T:Subgroup G) := hp.le_sylow_of_normalized T d.line_stable
  obtain ⟨J,hJH,hJ,hsolv⟩:=exists_minimal_Hz_of_solvable_overgroup hline hp
    (hVT.trans le_sup_right) (d.first_normalizer ▸ le_rfl) hLT hHG hout hs
  exact minimal_not_solvable d hJ (hF9all J hJ.prop) hN hflag
    (hdispall J hJ.prop) (hnoncentralall J hJ.prop) hsource hsolv

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.SolvableSource
