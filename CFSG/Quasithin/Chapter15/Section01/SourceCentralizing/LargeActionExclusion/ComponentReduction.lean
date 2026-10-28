module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.SourceInterface
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.Ordinary.ModelExclusions
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.Ordinary.HigmanSims
public import CFSG.Quasithin.Chapter15.Section01.CaseI.SourceTrialityExclusion

/-!
# Fixed-plane obstructions in the large-action component reduction

For either surviving exchanged row, the fixed plane lies in the source Sylow
and centralizes the literal cubic actor. Thus the source 15.1.22 equality of
the cubic-actor and component centralizers contradicts fixed-plane movement.
The triality case uses its fixed-nine argument instead of an outer-two bound.
The same component consequently excludes the recognized ordinary Mathieu/J2,
small binary Lie, and HS models, for both plane sizes four and sixteen.

These are the centralizer obstructions needed for 15.1.26. The exhaustive
ordinary catalogue, constrained block exclusions, and selection for the
non-Nine rows remain separate source obligations; this module does not
assert a complete component classification.

Source: Aschbacher--Smith 15.1.22, 15.1.24(4), 15.1.25(1),(3), and
15.1.26, printed pp.1098--1102.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterD ChapterD.UniqueFactor Section03 Section03.InitialSource ChapterA.Section05To06
open Theory.SpecificGroups.BinaryComponentResidual
variable {G : Type*} [Group G] [Finite G]
namespace CaseIComponentData
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The fixed plane centralizes the literal cubic actor inside the source Sylow. -/
theorem fixedPlane_le_sylow_cubicCentralizer (d : CaseIComponentData T M Mc V)
    (hTM : (T : Subgroup G) ≤ M) (h : PreparedChosenModule T M V) :
    d.nineFixedPlane ≤ d.S ⊓ centralizer (d.nineCubic : Set G) := by
  let := h.elementary
  have hYR : d.nineCubic ≤ d.nineResidual := map_mono (le_pResidual_of_isPPerfect _
    (isPPerfect_primeToResidual 3 2 (by decide)))
  have hVT : V ≤ (T : Subgroup G) := by
    let : (V.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer h.normalized
    let := IsElementaryAbelian.subgroupOf h.le_selected (p := 2)
    have hh := (IsElementaryAbelian.isPGroup 2 (V.subgroupOf M)).le_sylow_of_normal
      (T.subtype hTM)
    simpa only [map_subgroupOf_eq_of_le h.le_selected, Sylow.coe_subtype,
      map_subgroupOf_eq_of_le hTM] using map_mono (f := M.subtype) hh
  exact le_inf (le_inf (inf_le_left.trans hVT)
    (inf_le_left.trans (V.le_centralizer.trans
      (centralizer_le (d.Z1_le_fixed.trans inf_le_left)))))
    (inf_le_right.trans (centralizer_le hYR))

/-- Original 15.1.26's equal-centralizer contradiction for either exchanged row. -/
theorem ExchangedSource.no_equal_centralizers {d : CaseIComponentData T M Mc V}
    (s : d.ExchangedSource) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hTM : (T : Subgroup G) ≤ M) (h : PreparedChosenModule T M V)
    (hf : Facts (d.L ⧸ pCore 2 d.L)) :
    d.S ⊓ centralizer (((primeToResidual 3 (M ⊓ d.L : Subgroup G)).map
      (M ⊓ d.L).subtype) : Set G) ≠ d.S ⊓ centralizer (d.L : Set G) := by
  let := s.quasisimple
  intro heq
  have hY := (d.source_cubic_component hG h hf).2
  have hc : d.S ⊓ centralizer (d.nineCubic : Set G) =
      d.S ⊓ centralizer (d.L : Set G) := by
    dsimp only [nineCubic]
    rw [hY]
    exact heq
  exact s.fixed_noncentral hf
    (((d.fixedPlane_le_sylow_cubicCentralizer hTM h).trans hc.le).trans inf_le_right)

/-- Triality uses its fixed-nine argument, without an outer-two assumption. -/
theorem ExchangedSource.triality_no_equal_centralizers {d : CaseIComponentData T M Mc V}
    (s : d.ExchangedSource) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hTM : (T : Subgroup G) ≤ M) (h : PreparedChosenModule T M V)
    (j : (d.L ⧸ pCore 2 d.L) ≃* Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one) :
    d.S ⊓ centralizer (((primeToResidual 3 (M ⊓ d.L : Subgroup G)).map
      (M ⊓ d.L).subtype) : Set G) ≠ d.S ⊓ centralizer (d.L : Set G) := by
  let := s.quasisimple
  let := h.elementary
  intro heq
  have hV2 : d.nineMovingPlane ≠ ⊥ := by
    intro he
    rcases s.sizes with hs | hs <;> have hc := hs.2.2.2 <;>
      rw [he, card_bot] at hc <;> omega
  obtain ⟨t,ht,htS⟩ := s.exchange_exists
  have hnon := d.fixed_plane_not_centralizes_of_triality hG j
    d.nineFixedPlane d.nineMovingPlane d.nineCubic s.marked_le_fixed
    ((IsElementaryAbelian.isPGroup 2 V).to_le inf_le_left) hV2
    s.cubic_idempotent s.cubic_moving t (s.exchanges t ht htS).2
  have hY := (d.source_triality_cubic_component hG h j).2
  have hc : d.S ⊓ centralizer (d.nineCubic : Set G) =
      d.S ⊓ centralizer (d.L : Set G) := by
    dsimp only [nineCubic]
    rw [hY]
    exact heq
  exact hnon (((d.fixedPlane_le_sylow_cubicCentralizer hTM h).trans hc.le).trans inf_le_right)

/-- The intrinsic small-model fixer bounds apply to either exchanged row. -/
theorem ExchangedSource.not_ordinary_small_models {d : CaseIComponentData T M Mc V}
    (s : d.ExchangedSource) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1)) :
    ¬ SmallOrdinaryModel (d.L ⧸ pCore 2 d.L) ∧
      ¬ SmallBinaryOrdinaryModel (d.L ⧸ pCore 2 d.L) := by
  let := s.quasisimple
  constructor
  · intro he
    have hf := facts_of_small_model he
    exact s.no_equal_centralizers hG hM.1.2 h hf
      (d.ordinary_small_model_centralizer hG hM.1.2 hu h hL s.odd_core
        s.component_sylow hf he s.cubic_escape)
  · intro he
    have hf := facts_of_small_binary_model he
    exact s.no_equal_centralizers hG hM.1.2 h hf
      (d.ordinary_small_binary_model_centralizer hG hM.1.2 hu h hL s.odd_core
        s.component_sylow he s.cubic_escape)

/-- The intrinsic HS fixer bound also excludes HS for sixteen-element planes. -/
theorem ExchangedSource.not_ordinary_hs {d : CaseIComponentData T M Mc V}
    (s : d.ExchangedSource) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1)) :
    ¬ Nonempty ((d.L ⧸ pCore 2 d.L) ≃* Sporadic.LeechRelated.HS.Carrier) := by
  rintro ⟨e⟩
  let := s.quasisimple
  have hhs : Facts Sporadic.LeechRelated.HS.Carrier :=
    ⟨Sporadic.LeechRelated.HS.BlockNormalizer.center_carrier_eq_bot,
      Sporadic.LeechRelated.HS.ThreeRank.two_le_primeRank,
      Sporadic.LeechRelated.HS.outer_isPGroup_two_of_pointStabilizer_map
        Sporadic.LeechRelated.HS.pointStabilizer_map
        Sporadic.LeechRelated.HS.normalizer_relIndex_dvd_two_pow⟩
  have hf := Facts.of_equiv e hhs
  exact s.no_equal_centralizers hG hM.1.2 h hf
    (d.ordinary_source_centralizer_of_model hG hM.1.2 hu h hL s.odd_core
      s.component_sylow hf e
      (fun P A _ hfix => Sporadic.LeechRelated.HS.ElementarySylowFixers.sylow_fixer_card_le_two
        P A hfix) s.cubic_escape)

end CaseIComponentData
end CFSG.Quasithin.Chapter15.Section01
