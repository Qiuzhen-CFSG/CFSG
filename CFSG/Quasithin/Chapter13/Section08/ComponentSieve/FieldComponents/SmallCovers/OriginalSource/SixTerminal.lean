module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.OriginalSource.SixGeometry
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.TerminalSource.HexacodeMarking.PairCoreBound
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.TerminalSource
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CriticalSource
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.Terminal.RankSourceActions
public import Theory.Representation.HexacodeAction.NoTransvections
public import Theory.Representation.BinaryOffender.CodimensionSieve
public import Theory.Representation.BinaryOffender.CommutatorRank
/-!
# The original six-cover terminal contradiction and reducible exclusion

A recognized proper quotient retains the surviving source seed and its
actual parabolic stabilizer. Solvability selects the coordinate-pair orbit,
whose intrinsic two-core has order at most four. The full hexacode action
has no transvections, and its faithful quotient action excludes them on the
original module. The original critical pair then supplies rank greater than
one and placement, forcing that two-core to have order exactly four.

The final contradiction acts on the different, literal V_H/U_H section.
Its conjugation action, noncentrality, permutation-module surjection and
quadraticity are all constructed from SourceContext. No nonquadraticity of
the six-dimensional hexacode module is asserted.

Native recognition already supplies both sections of a reducible source
module, so this excludes that case without additional premises. Combined
with the existing homogeneous selection it also completes the conditional
six-cover exclusion. qt-d-138-fields-source retains the proof of those
homogeneous alternatives in the remaining irreducible case and the other
field-sieve branches; qt-d-1381-source supplies the preceding SourceContext.

Source: Aschbacher–Smith, 13.8.21(2), printed p.956 (PDF p.973), using
13.8.4(5–6), 13.8.8(2), 13.8.18(4) and F.9.18(4),(6).
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.OriginalSource
open Reduction Reduction.ModuleRecognition SourceCompletion
open LinearThree.Geometry.CoveredProduct.ResidualPlacement
open HigherFieldReduction.ExternalModules
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)] [(K.subgroupOf H).Normal]

/-- The literal V_H/U_H obstruction after recognition of a proper quotient. -/
theorem source_six_cover_false_of_quotient_model
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (e : (K ⧸ pCore 2 K) ≃* Components.Models.A6Triple)
    (act : QuotientAction H V₃ V₁)
    (W : Subrepresentation act.representation) (ht : W ≠ ⊤)
    (q : HexacodeModel (Source.starImage H K) W.quotientRepresentation) : False := by
  classical
  have hno : ∀ a : Source.Hstar H, fixedCodim act.representation (zpowers a) ≠ 1 := by
    intro a hr
    have he := fixedCodim_map_equivariant W.quotientRepresentation Hexacode.action
      q.actor q.coordinates q.intertwines (zpowers a)
    rw [MonoidHom.map_zpowers] at he
    have hn : fixedCodim W.quotientRepresentation (zpowers a) ≠ 1 :=
      he ▸ Hexacode.no_transvections (q.actor a)
    have hle := fixedCodim_quotient_add_subrepresentation_le act.representation W (zpowers a)
    have hz : fixedCodim W.quotientRepresentation (zpowers a) = 0 := by omega
    by_cases hA : zpowers a = ⊥
    · have hh := (fixedCodim_eq_zero_iff act.representation ⊥).mpr (fixedSpace_bot _)
      rw [hA] at hr
      omega
    · have hp := fixedCodim_pos_of_faithful W.quotientRepresentation
        ((source_six_cover_sections c e act).2 W ht).1 hA
      omega
  have hH := c.component.local_overgroup
  have hF9 := c.f9 H hH
  have hKH : K ≤ H := (le_sup_left.trans le_sup_left).trans_eq c.component.generated
  have hgen : H = K ⊔ (one L T V₁ ⊔ (T : Subgroup G)) := by
    rw [←c.component.generated,sup_assoc]
  have hLH : one L T V₁ ≤ H := le_sup_left.trans hH.1.2
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans hH.1.2
  let : IsElementaryAbelian 2 (conjugateSpanBy V G₁) := c.localSetup.span_elementary
  let : IsElementaryAbelian 2 (Source.VH H V) :=
    IsElementaryAbelian.of_le (conjugateSpanBy_mono le_rfl hH.2.1)
  let : IsQuasisimple Atlas.Codes.HexEvenAutomorphisms := Hexacode.even_isQuasisimple
  have hqs : IsQuasisimple (Source.starImage H K) := IsQuasisimple.of_mulEquiv
    ((Components.componentStarEquiv H K hKH c.component.component).symm.trans e).symm
  obtain ⟨w⟩ := CriticalSource.exists_selected_witness c.localSetup hH hF9 hgen
    c.component.component c.component.normal hqs c.centralizer c.noncentral_core
    act.representation act.conjugation (by
      intro a
      rw [←fixedCodim_zpowers_eq_displacement_rank]
      exact hno a)
  obtain ⟨D,s,hd,_,hs,hpoint⟩ := source_six_cover_quotient_pair c e act W ht q
  have hj : Source.starImage H (one L T V₁ ⊔ (T : Subgroup G)) =
      Source.starImage H (one L T V₁) ⊔ Source.starImage H (T : Subgroup G) := by
    simp only [Source.starImage,subgroupOf_sup hLH hTH,Subgroup.map_sup]
  have heven : Atlas.Codes.hexSign.ker ≤ q.actor.range := by
    rw [←q.component_image]
    exact map_le_range _ _
  have hbound := TerminalSource.HexacodeMarking.pair_point_twoCore_card_le_four
    q.actor q.faithful heven D s hs
  change Nat.card ((TerminalSource.HexacodeMarking.pointStabilizer q.actor D).pCoreIn 2) ≤ 4 at hbound
  change TerminalSource.HexacodeMarking.pointStabilizer q.actor D = _ at hpoint
  rw [hj] at hpoint
  rw [hpoint] at hbound
  have hconj : (Source.starImage H w.pair.Vgamma).map
      (MulAut.conj (QuotientGroup.mk' (pCore 2 H) w.conjugator)).toMonoidHom =
      Source.starImage H w.alpha :=
    (AlternatingAndLinear.FourStructure.CriticalTransfer.MarkedGeometry.starImage_conjugate w.pair.Vgamma
      w.actor_le w.conjugator).symm
  have hrank : 1 < rank (Source.starImage H w.alpha) := by
    rw [←hconj,rank_map_conj]
    exact w.rank_gt_one
  have hplace := w.alpha_star_le_core hLH hTH
  have hfour : Nat.card ((Source.starImage H (one L T V₁) ⊔
      Source.starImage H (T : Subgroup G)).pCoreIn 2) = 4 := by
    apply Nat.le_antisymm hbound
    have hlow : 4 ≤ Nat.card (Source.starImage H w.alpha) :=
      Nat.pow_le_of_le_log (Nat.card_pos.ne') hrank
    exact hlow.trans (Nat.card_le_card_of_injective _ (inclusion_injective hplace))
  obtain ⟨a,ha⟩ := Terminal.exists_rank_section_action c.localSetup hF9 hH.2.1 c.noncentral_core
  let ρ := SolvableExclusion.Three.Supercritical.Offenders.linearAction a
  have hear := CriticalSource.earlier_inputs c.localSetup hH hF9 c.centralizer
    c.noncentral_core act.representation act.conjugation
  have hpar := (source_six_cover_parabolic c e q.actor q.faithful q.component_image).2.1
  have hnorm : H ⊓ M ≤ normalizer (V : Set G) := by
    rw [hpar]
    rw [←Comparison.local_edge c.localSetup hF9]
    exact inf_le_left.trans c.localSetup.normalizes_V
  let : Fintype (Source.Hstar H ⧸ Source.starImage H (H ⊓ M)) := Fintype.ofFinite _
  obtain ⟨f,hf⟩ := source_13_8_4_permutation_surjection H M V V₃ c.localSetup.seed_le
    hear.flag_index hear.noncentral hnorm ρ ha
  have hquad := Terminal.rank_section_quadratic c.localSetup hF9 a w.pair (1 : H)
  have hquad' : IsQuadratic ρ (Source.starImage H w.pair.Vgamma) := by
    have he : w.pair.Vgamma.map (MulAut.conj ((1 : H) : G)).toMonoidHom = w.pair.Vgamma := by
      change w.pair.Vgamma.map (MulAut.conj (1 : G)).toMonoidHom = _
      rw [show (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G from by ext x; simp]
      exact Subgroup.map_id _
    rw [he] at hquad
    exact hquad
  exact TerminalSource.contradiction_of_hexacode_point H M K (one L T V₁) T V V₃
    w.alpha w.pair.Vgamma ρ ha q.actor q.faithful q.component_image D hd hpoint
    (by rw [hpar]; exact hj) f.toLinearMap hf
    (fun h v => LinearMap.congr_fun (f.isIntertwining' h) v) hear.noncentral
    (QuotientGroup.mk' (pCore 2 H) w.conjugator) hconj hplace hfour hrank hquad'

/-- Native recognition of both proper sections lets the reducible source
six-cover case reach the literal permutation-quotient contradiction. -/
theorem source_six_cover_no_proper_section
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (e : (K ⧸ pCore 2 K) ≃* Components.Models.A6Triple)
    (act : QuotientAction H V₃ V₁)
    (W : Subrepresentation act.representation) (hb : W ≠ ⊥) (ht : W ≠ ⊤) : False := by
  obtain ⟨_,⟨q⟩,_⟩ := source_six_cover_proper_sections c e act W hb ht
  exact source_six_cover_false_of_quotient_model c e act W ht q

/-- Any original six-cover module would be irreducible. -/
theorem source_six_cover_irreducible
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (e : (K ⧸ pCore 2 K) ≃* Components.Models.A6Triple)
    (act : QuotientAction H V₃ V₁) : IsIrreducible act.representation := by
  let : Nontrivial (Additive (Source.Utilde H V₃ V₁)) := source_quotient_nontrivial c
  let : Nontrivial (Subrepresentation act.representation) := ⟨⟨⊥,⊤,fun he =>
    bot_ne_top (congrArg Subrepresentation.toSubmodule he)⟩⟩
  apply IsSimpleOrder.of_forall_eq_top
  intro W hb
  by_contra ht
  exact source_six_cover_no_proper_section c e act W hb ht

/-- The genuine homogeneous alternatives now give the complete six-cover
contradiction; their source proof remains with the field-sieve owner. -/
theorem source_six_cover_false_of_alternatives
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (e : (K ⧸ pCore 2 K) ≃* Components.Models.A6Triple)
    (act : QuotientAction H V₃ V₁)
    (P : Sylow 2 (Source.Hstar H))
    (hP : (P : Subgroup (Source.Hstar H)) = Source.starImage H (T : Subgroup G))
    (src : LocalGeometry.DynkinExclusion.Recognition.Alternatives act.representation
      (Source.starImage H K) P
      (LocalGeometry.DynkinExclusion.star_sylow_generation H K (T : Subgroup G)
        (source_six_cover_consequences c e).2.1 P hP)) : False := by
  obtain ⟨s⟩ := source_six_cover_section_of_alternatives c e act P hP src
  exact source_six_cover_false_of_quotient_model c e act s.denominator s.proper {
    actor := s.actor
    faithful := s.actor_injective
    component_image := s.component_image
    coordinates := s.equivalence
    intertwines := s.intertwines }
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.OriginalSource
