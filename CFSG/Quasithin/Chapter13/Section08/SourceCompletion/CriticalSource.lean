module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.Comparison.Geometry
public import CFSG.Quasithin.Chapter13.Section07.SpanGrowth
public import CFSG.Quasithin.Chapter13.Section05.PointAction
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.CriticalInputs.Geometry

/-!
# Original-source inputs for the component critical geometry

The natural source flag and the earlier centralizer and plane noncentrality
bounds imply that H acts nontrivially on V_H/U_H. F.9 supplies both edge cores,
the first-kernel identity and the common-center codimension bound, uniformly
on every genuine critical pair. These deductions construct the literal
EarlierInputs used by the exceptional field branch.

For a normal C-component with H = K(L₁T), the same inputs construct a selected
pair, its actual H-conjugator, a quadratic actor, every-F generation, and
rank(Vγ*) > 1 whenever the original action has no transvections. Relative
normality and the star quotient are transported by the endpoint conjugator.
No selected pair, rank comparison, or geometric conclusion is assumed.
The earlier source inputs and the component assertions retain their original
owners; this is the geometry application, not the final 13.8.1 theorem.

Source: Aschbacher–Smith, F.9.13–16 and 13.8.4,8,18, printed
pp.322–324,947,949,953, combined manuscript of 1 March 2004.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CriticalSource
open CriticalGeometry CriticalGeometry.SectionActions
open TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.HigherFieldReduction
open ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules
open ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.ReversedSourceData
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

/-- All earlier geometric premises of the field consumer, on its literal
conjugation representation. Noncentrality is derived from the original flag. -/
theorem earlier_inputs
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) T G₁ M)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SeedAction.Space H V₃ V₁))
    (hρ : SeedAction.IsConjugation H V₃ V₁ ρ) :
    CriticalInputs.EarlierInputs L (T : Subgroup G) H V V₃ V₁ ρ := by
  let dn := localNaturalSetup d
  have hg := local_earlierGeometry d hF9
  have hflag : normalizer (V₁ : Set G) ⊓ normalizer (V₃ : Set G) ≤ M := by
    have hh := Section05.PointAction.normalizer_intersection_source dn hcentral
    simpa only [d.first_normalizer] using hh.trans inf_le_left
  let s := CriticalInputs.sourceSection H V₃ V₁ ρ hρ hF9.plus_le_H
    (d.line_le_plane.trans d.plane_le_seed) hF9.H_centralizes
  refine {
    geometry := hg
    terminal_core := ?_
    centralizer := ?_
    failure := fun c => f9_commutator_not_le_Aone _ hF9 c (hg c).length
    noncentral := Section07.source_noncentral_VH_quotient_of_earlier_geometry dn hF9
      inferInstance hH.2.1 hH.2.2 hflag hcomm
    flag_index := Comparison.local_seed_index d
    edge_normalizes := inf_le_left.trans d.normalizes_V
    endpoint_core := Comparison.local_core_le_edge d hF9
    proper_edge := Comparison.local_proper_edge d hF9 hH
    estimate := fun c _ hc => dn.fixedCodim_le_twice_rank d.abelian_span hF9 s c hc
    initial_core := fun c => (f9_endpoint_edge_cores _ hF9 c (hg c).length).2 }
  · intro c
    have hh := (f9_endpoint_edge_cores _ hF9 c (hg c).length).1
    change Source.VH H V ≤ (vertexGroup _ _ _ c.previous ⊓ vertexGroup _ _ _ c.gamma).pCoreIn 2 at hh
    rw [inf_comm] at hh
    exact (conjugateSpanBy_mono d.seed_le le_rfl).trans hh
  · rw [commutator_comm]
    exact Section07.centralizer_UH_commutator dn hF9

/-- The same selected critical pair carries 13.8.8(2), quadraticity of Vγ*,
and all of 13.8.18's generation and final rank conclusions. Only the preceding
normal component and its supplement remain as component-source premises. -/
theorem exists_selected_witness
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) T G₁ M)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hgen : H = K ⊔ (sourceOne L T V₁ ⊔ (T : Subgroup G)))
    (hK : (K.subgroupOf H).IsCComponent) (hN : (K.subgroupOf H).Normal)
    (hqs : IsQuasisimple (Source.starImage H K))
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SeedAction.Space H V₃ V₁))
    (hρ : SeedAction.IsConjugation H V₃ V₁ ρ)
    (hno : ∀ g, Module.finrank (ZMod 2) (LinearMap.range (ρ g - LinearMap.id)) ≠ 1) :
    Nonempty (CriticalInputs.SelectedWitness L (T : Subgroup G) H V
      (sourceOne L T V₁) V₃ V₁ ρ) := by
  let : Group.IsPerfect (K.subgroupOf H) := hK.perfect
  let : IsElementaryAbelian 2 (conjugateSpanBy V G₁) := d.span_elementary
  let : IsElementaryAbelian 2 (Source.VH H V) :=
    IsElementaryAbelian.of_le (conjugateSpanBy_mono le_rfl hH.2.1)
  let s := CriticalInputs.sourceSection H V₃ V₁ ρ hρ hF9.plus_le_H
    (d.line_le_plane.trans d.plane_le_seed) hF9.H_centralizes
  have e := earlier_inputs d hH hF9 hcentral hcomm ρ hρ
  have hKH : K ≤ H := hgen ▸ le_sup_left
  have hc (c : CriticalPair L (T : Subgroup G) H V) :=
    Comparison.component_conjugate H K hKH hN hqs (MulAut.conj (c.gb : G))
  obtain ⟨initial, _, _⟩ := (localNaturalSetup d).exists_criticalPair d.abelian_span hF9
  obtain ⟨c, hd, hdγ, hp, hcomp, hquad, ⟨a, ha, hplace, _⟩, hgenerate, hrank⟩ :=
    initial.exists_selected_component_rank (sourceOne L T V₁)
      ((sourceOne L T V₁ ⊔ (T : Subgroup G)).pCoreIn 2) K V₃ V₁ s
      (f9_section_faithful _ hF9 s) hgen (Comparison.local_edge d hF9)
      (fun c => by rw [c.vertexGroup_gamma]; exact (hc c).1)
      (fun c => by rw [c.vertexGroup_gamma]; exact (hc c).2.1)
      (fun c => by rw [c.vertexGroup_gamma]; exact (hc c).2.2)
      e.terminal_core d.seed_le hF9.V_le_H hF9.commutator_UH_QH_le_point
      e.geometry d.line_card e.centralizer e.failure e.noncentral e.flag_index
      e.edge_normalizes e.endpoint_core e.proper_edge e.estimate e.initial_core le_rfl
      (CriticalInputs.no_source_transvection H V₃ V₁ ρ hρ
        (hF9.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
        hF9.commutator_UH_QH_le_point hno)
  exact ⟨{
    pair := c
    conjugator := a
    second_to_base := ha
    actor_le := (e.geometry c).Vgamma_H
    strict_base := hd
    strict_endpoint := hdγ
    positive := hp
    comparison := hcomp
    quadratic_member := hquad
    generation := hgenerate
    rank_gt_one := hrank
    quadratic := (c.quadratic_star_on_Utilde V₃ V₁ s d.seed_le (e.geometry c).VH_endpoint).1
    conjugate_le_core := hplace }⟩

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CriticalSource
