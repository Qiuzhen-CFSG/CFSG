module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.Comparison.Geometry
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.CoveredAssembly

/-!
# Constructing the critical input of the covered comparison

Starting from the original natural local setup and genuine F.9 applicability,
select an actual critical pair and, if required, its geodesic reversal. The
checked common-center estimate gives the quadratic bound. Component generation
and the absence of transvections give rank greater than one at the same pair.
The literal endpoint and line kernels supply every field of CriticalEarlier,
including both conjugation directions and the relative-index comparison.

Only the preceding noncentrality of V_H/U_H and the actual component hypotheses
remain. F.9 applicability is the earlier 13.5.7 input; the standing abelian span
is the earlier 13.7.8 input. No geometric conclusion or rank bound is assumed.
Source: Aschbacher--Smith, 13.8.8,18,21(1), printed pp.949,953,957.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.Comparison
open CriticalGeometry CriticalGeometry.SectionActions
open TransvectionRecognition.Component.ModelExtension
open ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
open ComponentSieve.FieldComponents.LinearThree
open Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

theorem critical_earlier
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) T G₁ M)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hgen : H = K ⊔ (one L T V₁ ⊔ (T:Subgroup G)))
    (hK : (K.subgroupOf H).Normal) [Group.IsPerfect (K.subgroupOf H)]
    (hqs : IsQuasisimple (Source.starImage H K))
    (hnoncentral : ¬ ⁅Source.VH H V,H⁆ ≤ Source.UH H V₃)
    (act : SourceAction H V₃ V₁)
    (hno : ∀ a : Source.Hstar H, fixedCodim act.representation (zpowers a) ≠ 1) :
    Nonempty (CriticalEarlier H (one L T V₁) T V V₃ V₁ act) := by
  let s := sourceSection act hF9.H_centralizes
  have hfaith := f9_section_faithful _ hF9 s
  let dn := localNaturalSetup d
  let : IsElementaryAbelian 2 (conjugateSpanBy V G₁) := d.span_elementary
  let : IsElementaryAbelian 2 (Source.VH H V) :=
    IsElementaryAbelian.of_le (conjugateSpanBy_mono le_rfl hH.2.1)
  have hz : H ≤ normalizer (V₁:Set G) := hF9.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)
  have hQ : ⁅Source.UH H V₃,Source.QH H⁆ ≤ V₁ := hF9.commutator_UH_QH_le_point
  have hgeo := local_earlierGeometry d hF9
  have hKH : K ≤ H := hgen ▸ le_sup_left
  have he := local_edge d hF9
  have hcomp (c : CriticalPair L (T:Subgroup G) H V) :=
    component_conjugate H K hKH hK hqs (MulAut.conj (c.gb:G))
  have hU (c : CriticalPair L (T:Subgroup G) H V) :
      Source.UH H V₃ ≤ (edgeGroup L (T:Subgroup G) H c.gamma c.previous).pCoreIn 2 := by
    have hh := (f9_endpoint_edge_cores _ hF9 c (hgeo c).length).1
    change Source.VH H V ≤ (vertexGroup _ _ _ c.previous ⊓ vertexGroup _ _ _ c.gamma).pCoreIn 2 at hh
    rw [inf_comm] at hh
    exact (conjugateSpanBy_mono d.seed_le le_rfl).trans hh
  have hcentral : ⁅Source.VH H V,Source.HC H V₃⁆ ≤ V₁ := by
    rw [commutator_comm]
    exact Section07.centralizer_UH_commutator dn hF9
  obtain ⟨c,_,_⟩ := dn.exists_criticalPair d.abelian_span hF9
  obtain ⟨c,hd,hdg,hp,hc,hquad,⟨a,ha,hplace,_⟩,hgenerate,hlarge⟩ :=
    c.exists_selected_component_rank (one L T V₁) ((one L T V₁ ⊔ (T:Subgroup G)).pCoreIn 2)
      K V₃ V₁ s hfaith hgen he
      (fun c => by rw [c.vertexGroup_gamma]; exact (hcomp c).1)
      (fun c => by rw [c.vertexGroup_gamma]; exact (hcomp c).2.1)
      (fun c => by rw [c.vertexGroup_gamma]; exact (hcomp c).2.2)
      hU d.seed_le hF9.V_le_H hQ hgeo d.line_card hcentral
      (fun c => f9_commutator_not_le_Aone _ hF9 c (hgeo c).length)
      hnoncentral (local_seed_index d) (inf_le_left.trans d.normalizes_V)
      (local_core_le_edge d hF9) (local_proper_edge d hF9 hH)
      (fun c _ hcmp => dn.fixedCodim_le_twice_rank d.abelian_span hF9 s c hcmp)
      (fun c => (f9_endpoint_edge_cores _ hF9 c (hgeo c).length).2) le_rfl
      (no_source_transvection act _ hQ hno)
  have hγH : c.Ugamma V₃ ≤ H :=
    (map_mono (conjugateSpanBy_mono d.seed_le le_rfl)).trans (hgeo c).Vgamma_H
  have hback : Source.VH H V ≤
      ((one L T V₁ ⊔ (T:Subgroup G)).pCoreIn 2).map (MulAut.conj (c.gb:G)).toMonoidHom := by
    have hh := (f9_endpoint_edge_cores _ hF9 c (hgeo c).length).1
    change Source.VH H V ≤ (vertexGroup _ _ _ c.previous ⊓ vertexGroup _ _ _ c.gamma).pCoreIn 2 at hh
    rw [inf_comm] at hh
    change Source.VH H V ≤ (edgeGroup L (T:Subgroup G) H c.gamma c.previous).pCoreIn 2 at hh
    rw [c.edgeGroup_eq _ he,←map_pCoreIn_of_ker_isPGroup _
      (IsPGroup.ker_isPGroup_of_injective (MulAut.conj (c.gb:G)).injective)] at hh
    exact hh
  have hVA : Source.VH H V ≤ normalizer (c.Aone V₁ : Set G) :=
    (hgeo c).VH_endpoint.trans (SectionActions.CriticalPair.normalizes_Aone c V₁ hz)
  refine ⟨{
    g := c.gb
    h := a
    hV := hF9.V_le_H
    hflag := d.seed_le
    hflag_index := local_seed_index d
    hline := d.line_le_plane.trans d.plane_le_seed
    hcard := d.line_card
    hcentral := hF9.H_centralizes
    hseed := local_seed_commutator d hF9 hnoncentral c
    hnoncentral := hnoncentral
    hforward := (hgeo c).Vgamma_H
    hback := hback
    hplace := hplace
    hcentralizer := by simpa only [commutator_comm] using hcentral
    hdisjoint := disjoint_iff.mpr (hgeo c).lines_disjoint
    hseed_noncentral := f9_commutator_not_le_Aone _ hF9 c (hgeo c).length
    hcommute := (hgeo c).cross_centralizes
    hline_commutators := ?_
    hcritical := ?_
    hactor := hquad
    hlarge := fun _ => hlarge }⟩
  · constructor
    · rw [commutator_comm]
      exact commutator_commutatorPreimage_le _ _ _ hVA
    · rw [commutator_comm]
      exact commutator_commutatorPreimage_le _ _ _ ((hgeo c).Vgamma_H.trans hz)
  · change Reorientation.denominatorRank V₃ V₁ c ≤
      Nat.log 2 ((Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁).relIndex (c.Ugamma V₃))
    rw [s.Dgamma_relIndex _ hγH hfaith]
    exact hc

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.Comparison
