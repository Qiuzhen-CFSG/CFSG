module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Localization.Data
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Localization.NoTransvections
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Localization.EndpointGeometry.Transport
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Localization.EndpointGeometry.Generation
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Localization.EndpointGeometry.Bounds

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Localization.EndpointGeometry.Symmetry

/-!
# Geometric bounds for the five-primary rank-one branch

`geometric_bounds` constructs the actual endpoint bounds from the faithful
star action, the five-primary reduction and rank-one factors, and genuine
minimal solvable membership in Hz. `SourceInputs` lists the consumed standing
flag and earlier source facts; the full 13.8.5 model implication is explicit.
These are the authorized earlier inputs to this local deduction.

The proof derives strict denominators by excluding quotient transvections,
uses irreducibility to generate across the original terminal edge, and applies
13.8.11(2) after transporting its common-axis alternative through Uγ/A₁.
The reversed configuration has its own valid rank selection and an explicit
quotient transport. The opposite rank-one argument places A₁ in UH, and
conjugation transports the 13.7.3(7) centralizer bound. All groups, lines and
edges remain those of the supplied CriticalPair.

`geometric_bounds_and_symmetry` additionally exports the strict binary rank
bound and the constructed reversal. The separate second-actor construction
and the final 13.8.13 contradiction remain with the localization assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.13,
printed p.951 (PDF p.968), with 13.8.4–11 and Remark F.9.17.
-/

@[expose] public section

open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five.Localization.EndpointGeometry
open CriticalGeometry CriticalGeometry.Reorientation
open ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.ReversedSourceData
variable {G : Type*} [Group G] [Finite G]

/-- The consumed standing flag, 13.7.3(7), 13.8.4(5), 13.8.8(2), and
universal F.9.13/15 statements. No endpoint generation, symmetry, line
placement in UH, denominator index, or rank conclusion is a field. -/
structure SourceInputs {L H V : Subgroup G} {T : Sylow 2 G}
    (c : CriticalPair L T H V) (V₃ V₁ L₁ G₁ M : Subgroup G) : Prop where
  seed_le : V₃ ≤ V
  V_sylow : V ≤ T
  line_seed : V₁ ≤ V₃
  line_card : Nat.card V₁ = 2
  line_normalized : G₁ ≤ normalizer (V₁ : Set G)
  flag_index : V₃.relIndex V = 2
  flag_normalized : (L ⊔ T) ⊓ H ≤ normalizer (V : Set G)
  base_edge : (L ⊔ T) ⊓ H = L₁ ⊔ T
  base_in_M : L₁ ⊔ T ≤ M
  noncentral : ¬ ⁅Source.VH H V, H⁆ ≤ Source.UH H V₃
  centralizer_bound : ⁅Source.VH H V, Source.HC H V₃⁆ ≤ V₁
  geometry : ∀ d : CriticalPair L T H V, EarlierGeometry d V₃ V₁
  endpoint_core : ∀ d : CriticalPair L T H V,
    Source.VH H V ≤ (edgeGroup L T H d.gamma d.previous).pCoreIn 2
  critical_commutator : ∀ d : CriticalPair L T H V,
    ¬ ⁅d.Ugamma V₃, V⁆ ≤ d.Aone V₁
  selected_rank : denominatorRank V₃ V₁ c ≤ rank (Source.starImage H (c.Ugamma V₃))

/-- The five-primary geometric output and genuine symmetric critical pair.
Minimality and irreducibility enter through ReducedFive; the generation
prerequisite proves movement of the pulled-back actor and normal generation,
retaining exactly the original seed and terminal edge. The full earlier
13.8.5 conclusion excludes transvections and discharges 13.8.11(2). -/
theorem geometric_bounds_and_symmetry
    {L H V V₃ V₁ L₁ G₁ M Vα : Subgroup G} {T : Sylow 2 G}
    (c : CriticalPair L T H V)
    [IsElementaryAbelian 2 (Source.UH H V₃)] [IsElementaryAbelian 2 (Source.VH H V)]
    (a : StarAction H (Source.UH H V₃) V₁) (_faithful : Function.Injective a.action)
    (reduced : ReducedFive H L₁ T M Vα)
    (f : RankOneFactors a reduced.P (c.Ugamma V₃))
    (hminimal : Minimal (· ∈ Source.Hz L₁ T G₁ M) H)
    (hs : Group.IsSolvable H) (s : SourceInputs c V₃ V₁ L₁ G₁ M)
    (h135 : (∃ h : H, (centerAction a).action h ≠ 1 ∧
      binaryLinear ((centerAction a).action h) ∈
        LinearEquiv.transvections (ZMod 2) (Additive (Source.Utilde H V₃ V₁))) →
      FullModelConclusions L L₁ T (le_sup_left.trans hminimal.prop.1.2) (centerAction a)) :
    GeometricBounds c V₃ V₁ ∧
      1 < rank (Source.starImage H c.Vgamma) ∧
      ∃ r : Reversal c,
        (Source.DH (Source.UH H V₃) (r.pair.Ugamma V₃) (r.pair.Aone V₁)).relIndex
          (Source.UH H V₃) = 2 ∧
        (Source.Dgamma (r.pair.Ugamma V₃) (Source.UH H V₃) V₁).relIndex (r.pair.Ugamma V₃) = 2 ∧
        rank (Source.starImage H (r.pair.Ugamma V₃)) = 1 ∧
        denominatorRank V₃ V₁ r.pair ≤ rank (Source.starImage H (r.pair.Ugamma V₃)) := by
  let _ : IsElementaryAbelian 2 (c.Ugamma V₃) := IsElementaryAbelian.map _
  let _ : IsElementaryAbelian 2 c.Vgamma := IsElementaryAbelian.map _
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans hminimal.prop.1.2
  have hVH : V ≤ H := s.V_sylow.trans hTH
  have hz : H ≤ normalizer (V₁ : Set G) := hminimal.prop.2.1.trans s.line_normalized
  have hline : V₁ ≤ Source.UH H V₃ := s.line_seed.trans (le_conjugateSpanBy V₃ H)
  have hUγVγ : c.Ugamma V₃ ≤ c.Vgamma := map_mono (conjugateSpanBy_mono s.seed_le le_rfl)
  have hγH : c.Ugamma V₃ ≤ H := hUγVγ.trans (s.geometry c).Vgamma_H
  have hUJ := (conjugateSpanBy_mono s.seed_le le_rfl).trans (s.geometry c).VH_endpoint
  have hQ : ⁅Source.UH H V₃, Source.QH H⁆ ≤ V₁ := by
    rw [commutator_comm]
    exact core_commutator_le a
  have hc := component_conclusion_of_full a (le_sup_left.trans hminimal.prop.1.2) h135
  have hno := no_uStar_transvection a hz hQ hs hc
  obtain ⟨hDH, hDγ⟩ := c.strict_denominators_of_no_uStar_transvection V₃ V₁ s.seed_le hz
    hQ (s.geometry c) s.line_card s.centralizer_bound (s.critical_commutator c) hno
  have hcomp := c.index_comparison_of_selected_rank V₃ V₁ hγH
    (s.geometry c).Dgamma_kernel s.selected_rank
  have hi := denominator_indices c V₃ V₁ a f hγH (s.geometry c).Dgamma_kernel hDH hcomp
  have hcore : Source.QH H ≤ L₁ ⊔ T := by
    have hh := pCoreIn_le_sylow H (T.subtype hTH)
    rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH] at hh
    exact hh.trans le_sup_right
  have hbase : edgeGroup L T H (base L T H false) (base L T H true) = L₁ ⊔ T := by
    simpa [edgeGroup, vertexGroup_base] using s.base_edge
  have hgen := endpoint_generation c a reduced f hbase
    ((conjugateSpanBy_mono s.seed_le le_rfl).trans (s.endpoint_core c)) hcore hDH
  have hQE : c.Qgamma ≤ edgeGroup L T H c.gamma c.previous := by
    rw [terminal_edge_eq_map c hbase]
    exact map_mono hcore
  have hEJ : edgeGroup L T H c.gamma c.previous < vertexGroup L T H c.gamma := by
    rw [terminal_edge_eq_map c hbase, c.vertexGroup_gamma]
    apply (map_lt_map_iff_of_injective (f := (MulAut.conj (c.gb : G)).toMonoidHom)
      (MulAut.conj (c.gb : G)).injective).mpr
    refine lt_of_le_of_ne hminimal.prop.1.2 ?_
    intro he
    exact hminimal.prop.2.2 (he ▸ s.base_in_M)
  have hstar : Source.starImage H (c.Ugamma V₃) ≠ ⊥ := by
    intro he
    have hh := f.actor_card
    rw [he, Nat.card_unique] at hh
    contradiction
  have haxis := no_endpoint_axis c a hz hs hc hUJ hDH
  have hrank := (c.generated_rank_conclusions V₃ V₁ s.seed_le hVH hline hz hQ
    (s.geometry c) s.line_card s.noncentral s.flag_index s.flag_normalized hstar hgen hQE hEJ
    s.selected_rank).2 haxis
  have helem : IsElementaryTwo (Source.starImage H c.Vgamma) :=
    ⟨ne_bot_of_le_ne_bot hstar (map_mono (subgroupOf_mono H hUγVγ)),
      starImage_isElementaryAbelian H c.Vgamma (s.geometry c).Vgamma_H⟩
  have hcard : 2 < Nat.card (Source.starImage H c.Vgamma) := by
    rw [helem.card_eq_two_pow_rank]
    simpa only [pow_one] using Nat.pow_lt_pow_right (by decide : 1 < 2) hrank
  refine ⟨⟨hγH, (s.geometry c).Vgamma_H, hline,
    Aone_le_of_indices c a hz hs hc hγH hUJ s.line_card hDγ hi,
    endpoint_line_card c V₁ s.line_card, hi.1, ?_, ?_, hgen, hcard⟩,
    hrank, exists_symmetric_reversal c a f s.seed_le hz s.geometry s.selected_rank hDH s.line_card⟩
  · exact disjoint_iff.mpr (s.geometry c).lines_disjoint
  · apply centralizer_commutator_bound c V₃ V₁ hUJ
    rw [commutator_comm]
    exact s.centralizer_bound

/-- The construction target consumed by the independent second-actor task. -/
theorem geometric_bounds
    {L H V V₃ V₁ L₁ G₁ M Vα : Subgroup G} {T : Sylow 2 G}
    (c : CriticalPair L T H V)
    [IsElementaryAbelian 2 (Source.UH H V₃)] [IsElementaryAbelian 2 (Source.VH H V)]
    (a : StarAction H (Source.UH H V₃) V₁) (faithful : Function.Injective a.action)
    (reduced : ReducedFive H L₁ T M Vα)
    (f : RankOneFactors a reduced.P (c.Ugamma V₃))
    (hminimal : Minimal (· ∈ Source.Hz L₁ T G₁ M) H)
    (hs : Group.IsSolvable H) (s : SourceInputs c V₃ V₁ L₁ G₁ M)
    (h135 : (∃ h : H, (centerAction a).action h ≠ 1 ∧
      binaryLinear ((centerAction a).action h) ∈
        LinearEquiv.transvections (ZMod 2) (Additive (Source.Utilde H V₃ V₁))) →
      FullModelConclusions L L₁ T (le_sup_left.trans hminimal.prop.1.2) (centerAction a)) :
    GeometricBounds c V₃ V₁ :=
  (geometric_bounds_and_symmetry c a faithful reduced f hminimal hs s h135).1

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five.Localization.EndpointGeometry

end
